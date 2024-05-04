#include <cstdio>
#include <cstring>
#include <cmath>
#include <vector>
#include <queue>
#include <map>
#include <iostream>
#include <algorithm>
#include <unordered_map>
#include <string>

using namespace std;
// ----------------------------- 常量 -----------------------------
const int     TOTAL_FRAME                 =   15000;                              // 总帧数
const int     STOP_FRAME                  =   980;                                // 停留时间，20帧用于掉帧冗余
const int     MAP_ARRAY_SIZE              =   210;                                // 地图数组大小，预留一点空间
const int     MAP_REAL_SIZE               =   200;                                // 地图的真实大小
const int     ROBOT_NUM                   =   10;                                 // 机器人的数量
const int     BOAT_NUM                    =   5;                                  // 轮船的数量
const int     BERTH_NUM                   =   10;                                 // 泊位的数量
const int     MAX_PATH_STEP               =   4 * MAP_REAL_SIZE + MAP_REAL_SIZE;  // 最大的路程距离(绕地图一圈) + 倒退预留大小
const int     LIMIT_LOAD_FRAME            =   14995;                              // 终止装货的帧数
// 超参数
const int     STEP                        =   15;                                 // 抢夺货物预留步数
const float   PUNISH                      =   2.5;                                // 惩罚港口
const int     VANISH                      =   80;                                 // 消失帧数
const float   VANISH_PUNISH               =   2;                                  // 惩罚消失权重



// 方向
const int DIRECTION[4] = {
        0,  // 右移一格
        1,  // 左移一格
        2,  // 上移一格
        3   // 下移一格
};

// 方向数组，用于表示上下左右四个方向
const int DIRECTION_TO_GO[4][2] = {
        {0, 1},     // 右移一格
        {0, -1},    // 左移一格
        {-1, 0},    // 上移一格
        {1, 0}      // 下移一格
};

// ----------------------------- 预定义结构体 -----------------------------
class Point;
class Path;
class Berth;
class Boat;
class Good;
class GoodList;
class Robot;

// ----------------------------- 预定义函数 -----------------------------
bool        IsValid(int x, int y);                                  // 检查坐标(x, y)是否在地图内以及是否可以走
bool        CanHit(Point np);
void        FixPos(Point &p);
long long   HashTwoPoints(const Point &a, const Point &b);          // 对两个坐标点进行hash
bool        getPath(Point p);
void        CalcPath(Point start, int (&endPoints)[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE]);
Path        *FindPath(Point start, Point end);                      // 从hash_paths中获取对应两点的最短路径
void        HandleFrame(int frame);
void        InitPre();
void        Init();


// ----------------------------- 变量 -----------------------------
int     g_init_berth[5] = {9, 8, 7, 6, 5};
int     g_lost_frame  =   15000;
int     g_count_value =   0;
int     g_frameId;
int     g_money;
int     g_boat_capacity;
int     g_berths_pull_point[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE];
char    g_map[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE];
char    g_ok[100];

vector<Robot>   g_robots(ROBOT_NUM);
typedef pair<int, int> g_lock_index;
multimap<int, g_lock_index>  g_berth_value_rank; // 动态统计, 当前泊位价值总量<unalloc_value, total_value, index>
int g_berth_ship_count[BERTH_NUM];                        // 每个港口船只数量
int g_target_position[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE];   //目标点机器人id
int g_nearest_berth[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE];     //距离最近的港口
// ----------------------------- 结构体 -----------------------------

class Point {
public:
    explicit Point (int x = -1, int y = -1) : x(x), y(y) {}
    bool operator==(const Point &other) const {
        return x == other.x && y == other.y;
    }

    bool operator!=(const Point &other) const {
        return !(*this == other);
    }
public:
    int x;
    int y;
} ;

Point g_init_pre[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE];
const Point INVALID_POINT = Point(-1,-1);       // 无效点

template<>
struct std::hash<Point> {
    size_t operator()(const Point &p) const {
        // 使用了异或^和左移<<操作符来组合 “x和y坐标” 的哈希值
        return hash<int>()(p.x) ^ hash<int>()(p.y) << 1;
    }
};

class Path {
public:
    Path() : pathHead(MAP_REAL_SIZE), pathRear(MAP_REAL_SIZE), dis(1) {}
    //检查当前位置是否有问题
    bool checkCurrPoint(const Point &p);
    //获取路径下一个点
    Point getNextPoint();
    //倒退是获取前一个点
    Point getBeforePoint();
    // 添加路径点
    void addPoint(const Point &p);
    // 倒转路径点
    void reversePath();
    // 重设
    void resetHead();
    int getDis() const{
        return dis;
    }
    int getRestStep() const{
        return pathRear - pathHead;
    }
    Point finallyPoint() const{
        return path[pathRear - 1];
    }
public:
    Point path[MAX_PATH_STEP];  // 路径经过的点
    int pathHead;               // path头
    int pathRear;               // path尾
    int dis;                    // 路径的总距离
};

bool Path::checkCurrPoint(const Point &p) {
    if (pathHead == MAP_REAL_SIZE || p == path[pathHead])
        return true;
    else
        return false;
}

Point Path::getNextPoint() {
    if (pathHead < pathRear) {
        pathHead++;
        return path[pathHead];
    } else {
        // 处理数组越界的情况
        std::cerr << "Path is too long, (" << pathHead << ")exceeding MAX_PATH_STEP." << std::endl;
        return INVALID_POINT;
    }
}

Point Path::getBeforePoint() {
    pathHead = pathHead - 2;
    if (path[pathHead].x == -1) {
        bool flag = false;
        for (int i = 0; i < 4; i++) {
            Point tmp(path[pathHead + 1].x + DIRECTION_TO_GO[i][0], path[pathHead + 1].y + DIRECTION_TO_GO[i][1]);
            if (IsValid(tmp.x, tmp.y) && !CanHit(tmp)) {
                flag = true;
                path[pathHead].x = tmp.x;
                path[pathHead].y = tmp.y;
                break;
            }
        }
        if (!flag) pathHead++;
    }
    return path[pathHead];
}

void Path::addPoint(const Point &p) {
    if (pathRear < MAX_PATH_STEP) {
        path[pathRear++] = p;
        ++dis;
    } else {
        // 处理数组越界的情况
        std::cerr << "Path is too long, (" << pathRear << ")exceeding MAX_PATH_STEP." << std::endl;
    }
}

void Path::reversePath() {
    for (int i = pathHead; i < (pathRear - pathHead) / 2 + pathHead; ++i) {
        // 交换元素，使用临时变量保存一个元素的值
        Point temp = path[i];
        path[i] = path[pathRear - 1 - i + pathHead];
        path[pathRear - 1 - i + pathHead] = temp;
    }
}

void Path::resetHead() {
    this->pathHead = 200;
    int tmp = pathHead - 1;
    while (path[tmp].x != -1) {
        path[tmp].x = -1;
        tmp--;
    }
}

unordered_map<long long, Path>      g_hash_paths;         // 两点最短路径的Cache
unordered_map<Point, Path>          g_back_paths;         // 两点最短路径的Cache

class Berth {
public:
    Berth();
    void Init();
    Point CalcPullPoint();
public:
    int id;
    Point p;
    Point pullP;
    int transportTime{};  // 表示该泊位轮船运输到虚拟点的时间
    int loadingSpeed{};   // 表示该泊位的装载速度，即每帧可以装载的物品数，单位(个)
    int totalValueBerth; // 当前泊位货物总值
    int leftValueBerth; // 剩余可分配给船的货物总值
    vector<int> storedGoods; // 堆积货物价值排序, 便于ship取价值高的货物, 同时可内调函数获取当前泊位货物数量
    queue<int> boatQueue; // 记录当前泊位已有的和等待的boat
};

Berth::Berth()
    :totalValueBerth(0),
     leftValueBerth(0){
}

inline void Berth::Init() {
    FixPos(this->p);  // 得到的位置是从0开始的，+1与地图保持一致
    CalcPullPoint();
}

inline Point Berth::CalcPullPoint() {
    this->pullP.x = this->p.x;
    this->pullP.y = this->p.y;
    return this->pullP;
}

Berth g_berths[BERTH_NUM];

class Boat {
public:
    // 船的状态
    Boat();
    //为船分配港口
    void FindSuitableBerth(int frame);

public:
    int id;
    int capacity;
    int totalValueBoat;
    int berthId;        // 表示目标泊位
    int status;     // 状态(0表示运输中；1表示正常运行状态，即装货中或运输完成；2表示泊位外等待)
};

Boat g_boats[BOAT_NUM];

Boat::Boat() {
    totalValueBoat = 0;
    berthId = -1;
}

void Boat::FindSuitableBerth(int frame) {
    int sourceBerthId = this->berthId;
    double maxValue = -1000;
    int maxBerthId = -1;

    for (auto it = g_berth_value_rank.rbegin(); it != g_berth_value_rank.rend(); ++it) {
        if(g_berth_ship_count[it->second.second] >= 1)continue;
        if (frame + 500 + g_berths[it->second.second].transportTime > LIMIT_LOAD_FRAME) continue;
        if (g_berths[it->second.second].leftValueBerth >= 0) {
            double choiceValue = g_berths[it->second.second].leftValueBerth;
            if (choiceValue > maxValue) {
                maxValue = choiceValue;
                maxBerthId = it->second.second;
            }
        }
    }

    if (maxBerthId >= 0) {
        if(this->berthId >= 0)g_berth_ship_count[this->berthId]--;
        this->berthId = maxBerthId;
        g_berth_ship_count[this->berthId]++;
        g_berths[this->berthId].boatQueue.push(this->berthId);
    }
}

class Good {
public:
    Good() {}
    void Init(int startFrame);
    void findBerth();
public:
    Point p;                    // 货物坐标
    int value;                  // 货物金额(<= 1000)
    int restFrame;              // 剩余停留时间。 开始为1000帧。
    int startFrame;             // 出现时间
    bool hasDelete;             // 是否被运送
    bool canShip;               // 是否可以运送
    Berth *targetBerth;         // 目标泊位
    int disToTargetBerth;       // 到目标泊位的距离
    Path *pathToTargetBerth;    // 到目标泊位的路径
};

void Good::Init(int startFrame) {
    targetBerth = nullptr;
    disToTargetBerth = 40000;
    pathToTargetBerth = nullptr;

    FixPos(this->p);  // 得到的位置是从0开始的，+1与地图保持一致
    restFrame = 1000;
    hasDelete = false;
    canShip = true;
    this->startFrame = startFrame;
}

void Good::findBerth() {
    // 如果不能找到到达货物的路径, 则该货物无法ship
    if (!getPath(this->p)) {
        this->canShip = false;
        return;
    }

    // TODO: BUG 货物被墙包围起来的判断?

    // TODO: 检查Berth
    auto it = g_back_paths.find(this->p);
    auto path = &(it->second);
    int dis = path->getDis();

    for (auto &g_berth: g_berths) {
        if (path->finallyPoint() == g_berth.p) {
            this->targetBerth = &g_berth;
        }
    }

    this->disToTargetBerth = dis;
    this->pathToTargetBerth = path;

}

typedef struct GoodNode {
    Good good;
    struct GoodNode *next;
    struct GoodNode *prev;  // 前一个节点，便于删除
} GoodNode;

class GoodList {   // 货物清单
public:
    GoodList();
    // 判断货物清单是否为空
    bool isEmpty() const{
        return this->head->next == this->head;
    }
    // 增加一个货物
    void addGood(Good item);
    // 删除一个货物
    void deleteGood(GoodNode *item);
    // 删除消失的货物
    void deleteTimeOut(int frame);
public:
    int length;
    GoodNode *head;
};

GoodList  g_goodList;

GoodList::GoodList() {
    this->head = (GoodNode *) malloc(sizeof(GoodNode));    // 头节点
    this->head->next = this->head;
    this->head->prev = this->head;
    this->length = 0;
}

void GoodList::addGood(Good item) {
    GoodNode *newNode = (GoodNode *) malloc(sizeof(GoodNode));
    newNode->good = item;
    newNode->next = this->head;         // 新节点的下一个是头节点(插在队尾)
    newNode->prev = this->head->prev; // 新节点的前一个是当前的队尾

    this->head->prev->next = newNode; // 当前队尾的下一个是新节点
    this->head->prev = newNode;         // 头节点的前一个现在是新节点
    this->length++;
}

void GoodList::deleteGood(GoodNode *item) {
    if (item == nullptr || item == this->head) {
        return;
    }
    item->prev->next = item->next;
    item->next->prev = item->prev;

    this->length--;
    free(item);
}

void GoodList::deleteTimeOut(int frame) {
    int deletenum = 0;
    GoodNode *cur = head->next;
    while (cur->good.startFrame + STOP_FRAME < frame) {
        GoodNode *tmp = cur;
        cur = cur->next;
        deleteGood(tmp);
        deletenum ++;
    }
}



class Robot {
public:
    Robot();
    void resetStatus();
    void CheckStatus();
    bool InBerth(Point target, Point next);
    void CalcNextStep();
    void FindSuitableGood(int frame);
    int CalcMoveDirection(const Point &np) const ;
    Good *getTargetGood() const{
        return this->targetGood;
    }
    Berth *getTargetBerth() const{
        return this->targetBerth;
    }
public:
    int id;
    int nearWorkStation;    // -1 表示没有靠近工作站
    Point p;                // 当前坐标
    int value = 0;          // 携带的货物价值
    Path *path;                  // 路径
    // 恢复状态：status == 0
    // 正常状态但没有分配任务：status == 1, goods == 0, targetGood == nullptr, targetBerth == nullptr
    // 正常状态且正在前往取货：status == 1, goods == 0, targetGood != nullptr
    // 正常状态且正在送货：status == 1, goods == 1, targetBerth != nullptr
    int goods;          // 是否携带物品（0表示未携带物品，1表示携带物品）
    int status;         // 状态（0表示恢复状态，1表示正常运行状态）
    Good *targetGood;           // 目标货物
    Berth *targetBerth;         // 目标泊位

    bool pull;                  // 是否放置货物
    bool get;                   // 是否取货
    int move;                   // 移动方向
};

Robot::Robot() {
    path = nullptr;
    targetGood = nullptr;
    targetBerth = nullptr;
    goods = 0;
    status = 1;
    value = 0;
}

void Robot::resetStatus() {
    this->targetBerth = nullptr;
    this->targetGood = nullptr;
    this->path = nullptr;
    this->value = 0;    // 清除携带货物价值
}

void Robot::CheckStatus() {
    FixPos(this->p);  // 得到的位置是从0开始的，+1与地图保持一致
    this->move = -1;              // -1表示不对机器人下达指令
    this->get = false;
    this->pull = false;
    if (status == 0) return;

    if (this->targetBerth != nullptr && this->goods == 0) {

        if(this->targetGood != nullptr){
            g_target_position[this->targetGood->p.x][this->targetGood->p.y] = -1;
        }
        this->resetStatus();
    }

    // “正常状态且正在前往取货”, 当前点处在货物位置，并取到货物：重置机器人状态为“正常状态且正在送货”
    if (this->targetGood != nullptr && this->goods == 1 && this->p == this->targetGood->p) {
        if (g_target_position[this->p.x][this->p.y] != -1) {
            g_target_position[this->p.x][this->p.y] = -1;
        }

        this->targetBerth = this->targetGood->targetBerth;
        this->path->resetHead();
        this->path = this->targetGood->pathToTargetBerth;


        this->path->resetHead();

        this->targetGood->hasDelete = true;
        this->targetGood = nullptr;

    }
}

bool Robot::InBerth(Point target, Point next) {
    if (next.x >= target.x && next.x <= target.x + 3 && next.y >= target.y && next.y <= target.y + 3) return true;
    return false;
}

void Robot::CalcNextStep() {
    this->get = false;
    this->pull = false;
    if (this->path == nullptr) {
        move = -1;
        return;
    }
    if (this->path->checkCurrPoint(p) == false) {
        this->targetBerth = nullptr;
        this->targetGood = nullptr;
        this->path = nullptr;
    } else {
        auto nextPoint = path->getNextPoint();
        if (CanHit(nextPoint)) {
            nextPoint = path->getBeforePoint();
            if(nextPoint == p){
                move = -1;
                return;
            }
            if (CanHit(nextPoint)) {
                move = -1;
                path->pathHead = path->pathHead + 1;
                return;
            } else {
                move = CalcMoveDirection(nextPoint);
                this->p.x = nextPoint.x;
                this->p.y = nextPoint.y;
                // logInfo << " ============ " << this->p.x << " " << this->p.y << endl;
                return;
            }
        }
        move = CalcMoveDirection(nextPoint);
        // 检查是否走到最后一步的前一步，更新get或pull指令
        if (this->targetGood != nullptr && this->targetGood->p == nextPoint) {
            this->get = true;
            this->targetBerth = this->targetGood->targetBerth;
        }
        if (this->targetBerth != nullptr && InBerth(this->targetBerth->p ,nextPoint) && this->goods == 1) {
            this->pull = true;
            // 更新berth存储的货物价值链表, 并降序排序
            this->targetBerth->totalValueBerth += this->value;
            this->targetBerth->leftValueBerth += this->value;
            this->targetBerth->storedGoods.push_back(this->value);
            sort(this->targetBerth->storedGoods.rbegin(), this->targetBerth->storedGoods.rend());
            // 更新berth总体价值全局变量berth_value_rank
            for (auto it = g_berth_value_rank.begin(); it != g_berth_value_rank.end(); ++ it) {
                if (it->second.second == this->targetBerth->id) {
                    g_lock_index berthStatus(this->targetBerth->totalValueBerth, this->targetBerth->id);
                    g_berth_value_rank.erase(it);  // Wang
                    g_berth_value_rank.insert(make_pair(this->targetBerth->leftValueBerth, berthStatus));
                    break;
                }
            }

        }
        this->p.x = nextPoint.x;
        this->p.y = nextPoint.y;
        return;
    }
}

void Robot::FindSuitableGood(int frame) {
    if (targetGood != nullptr) return;
    int i = 0;
    int goodsPoint[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE];
    memset(goodsPoint, -2, sizeof(goodsPoint));

    for (GoodNode *curr = g_goodList.head->next; curr != g_goodList.head; curr = curr->next) {
        if (curr->good.canShip && curr->good.startFrame + STOP_FRAME > frame) {
            goodsPoint[curr->good.p.x][curr->good.p.y] = -1;
        }
    }
    // 计算 货物价值 / (机器人到货物的距离 + 货物到泊位的距离)，按顺序检查是否可以在货物消失前搬运
    CalcPath(this->p, goodsPoint);
    double vpdToTargetBerth = 0.0;   // Value per dis
    Good *tmp = nullptr;
    for (GoodNode *curr = g_goodList.head->next; curr != g_goodList.head; curr = curr->next) {
        if(curr->good.hasDelete)continue;
        auto pathToGood = FindPath(this->p, curr->good.p);
        if (pathToGood == nullptr) continue;    // 货物不可达
        int dis = pathToGood->getDis();
        float k = 1;
        if(this->id == g_nearest_berth[curr->good.p.x][curr->good.p.y]){
            k = PUNISH;
        }
        if( curr->good.startFrame +STOP_FRAME < frame + dis + VANISH){
            k = k * VANISH_PUNISH;
        }
        double valuePerDis = curr->good.value * k  * 1.0 / (curr->good.pathToTargetBerth->getDis() + dis);
        if (valuePerDis > vpdToTargetBerth && frame + dis < (curr->good.startFrame + STOP_FRAME)) {
            if (g_target_position[curr->good.p.x][curr->good.p.y] != -1) {
                if (dis > g_robots[g_target_position[curr->good.p.x][curr->good.p.y]].path->getRestStep() - STEP) {
                    continue;
                }
            }
            vpdToTargetBerth = valuePerDis;
            this->targetGood = &curr->good;
            this->value = curr->good.value;
            tmp = this->targetGood;
            this->path = pathToGood;
        }

    }
    // 跟新货物
    if (tmp != nullptr) {
        //抢夺货物时
        if (g_target_position[tmp->p.x][tmp->p.y] != -1) {
            g_robots[g_target_position[tmp->p.x][tmp->p.y]].path->resetHead();
            g_robots[g_target_position[tmp->p.x][tmp->p.y]].resetStatus();
        }
        g_target_position[tmp->p.x][tmp->p.y] = this->id;
    }
}

int Robot::CalcMoveDirection(const Point &np) const{
    // 遍历四个方向
    for (int i = 0; i < 4; ++i) {
        if (p.x + DIRECTION_TO_GO[i][0] == np.x && p.y + DIRECTION_TO_GO[i][1] == np.y)
            return DIRECTION[i];
    }
    return -1;
}

// ---------------------------- 函数 ----------------------------

// 检查坐标(x, y)是否在地图内以及是否可以走
bool IsValid(int x, int y) {
    return x >= 0 && x < MAP_ARRAY_SIZE && y >= 0 && y < MAP_ARRAY_SIZE &&
           (g_map[x][y] == '.' || g_map[x][y] == 'A' || g_map[x][y] == 'B');
}

// 修复点
void FixPos(Point &p) {
    p.x += 1;
    p.y += 1;
}

inline double CalcDis(const Point &p1, const Point &p2) {
    return sqrt((p2.x - p1.x) * (p2.x - p1.x) + (p2.y - p1.y) * (p2.y - p1.y));
}

// 查找货物到最近泊位的路径
bool getPath(Point p) {
    if (g_init_pre[p.x][p.y] == INVALID_POINT) {
        return false;
    }
    if (g_back_paths.find(p) == g_back_paths.end()) { // 如果路径未被记录
        Path path;
        Point cur = p;
        while (cur != g_init_pre[cur.x][cur.y]) {
            path.addPoint(cur);
            cur = g_init_pre[cur.x][cur.y];
        }
        path.addPoint(cur);
        g_back_paths[p] = path;
        return true;
    }
    return true;
}

// bfs算法查找单源最短路径，结果存在hash_paths中(使用findPath来查找)
void CalcPath(Point start, int (&endPoints)[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE]) {
    queue<Point> q;
    q.push(start);
    Point prev[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE];   // 记录前驱节点，用于重建从起点到该终点的最短路径
    // 初始化prev数组
    for (int i = 0; i < MAP_REAL_SIZE; i++) {
        for (int j = 0; j < MAP_REAL_SIZE; j++) {
            prev[i][j] = INVALID_POINT;
        }
    }
    prev[start.x][start.y] = start; // 起点的前驱是自己
    bool visited[MAP_REAL_SIZE][MAP_REAL_SIZE] = {};
    memset(visited, false, sizeof(visited));
    visited[start.x][start.y] = true;

    while (!q.empty()) {
        Point cur = q.front();
        q.pop();
        if (endPoints[cur.x][cur.y] == -1) {


            Point endPoint(cur.x, cur.y);

            long long hashKey = HashTwoPoints(start, endPoint);
            if (g_hash_paths.find(hashKey) == g_hash_paths.end()) { // 如果路径未被记录
                Path path;
                for (Point p = cur; p != start; p = prev[p.x][p.y]) {
                    path.addPoint(p);
                }
                path.addPoint(start);
                path.reversePath();
                g_hash_paths[hashKey] = path;
            }
        }

        // 遍历四个方向
        for (int i = 3; i >= 0; i--) {
            Point next(cur.x + DIRECTION_TO_GO[i][0], cur.y + DIRECTION_TO_GO[i][1]);
            if (IsValid(next.x, next.y) && !visited[next.x][next.y]) {
                visited[next.x][next.y] = true;
                prev[next.x][next.y] = cur; // 记录到达next的前驱节点是cur
                q.push(next);
            }
        }
    }
}

// 从hash_paths中获取对应两点的最短路径
Path *FindPath(Point start, Point end) {
    long long hashKey = HashTwoPoints(start, end);
    auto it = g_hash_paths.find(hashKey);
    if (it != g_hash_paths.end()) {
        return &it->second; // 返回找到的路径的引用
    } else {


        return nullptr;
    }
}

bool CanHit(Point np) {
    for (int i = 0; i < ROBOT_NUM; i++) {
        if (np.x == g_robots[i].p.x && np.y == g_robots[i].p.y) {
            return true;
        }
    }
    return false;
}

// 对两个坐标点进行hash
long long HashTwoPoints(const Point &a, const Point &b) {
    const int shift = 16;    // 每8位存储一个值（使用16位以确保没有溢出）
    // 地图的大小是200，因此可以使用8位二进制存储（256）。
    // 通过位操作将[a.x, a.y, b.x, b.y]组合成一个long long类型的值，每个占8位
    return ((long long) a.x << (shift * 3)) | ((long long) a.y << (shift * 2)) |
           ((long long) b.x << (shift * 1)) | ((long long) b.y << (shift * 0));
}

// Game control logic
void HandleFrame(int frame) {
    g_goodList.deleteTimeOut(frame - 500);  //删除超时节点
    // 为新增的每个货物找到最近的泊位（避免重复计算）
    for (GoodNode *curr = g_goodList.head->next; curr != g_goodList.head; curr = curr->next) {
        if (curr->good.canShip && curr->good.targetBerth == nullptr) {
            curr->good.findBerth();
        }
    }

    for (int i = 0; i < ROBOT_NUM; i++) {


        // 对机器人的四个状态进行处理
        if (g_robots[i].status == 0) continue;  // 恢复状态
        if (g_robots[i].goods == 0 && g_robots[i].getTargetGood() == nullptr &&
            g_robots[i].getTargetBerth() == nullptr) {     // 正常状态但没有分配任务
            g_robots[i].FindSuitableGood(frame);
            g_robots[i].CalcNextStep();
        } else if (g_robots[i].goods == 0 && g_robots[i].getTargetGood() != nullptr) { // 正常状态且正在前往取货
            g_robots[i].CalcNextStep();
        } else if (g_robots[i].goods == 1 && g_robots[i].getTargetBerth() != nullptr) {  // 正常状态且正在送货
            g_robots[i].CalcNextStep();
        } else {    // 未确认的状态
            continue;
        }


        // 输出机器人控制指令
        if (g_robots[i].move != -1)
            printf("move %d %d\n", i, g_robots[i].move);

        if (g_robots[i].get) {
            printf("get %d\n", i);
            // logInfo << "frame:" << frame << " robot:" << i << " get" << endl;
        } else if (g_robots[i].pull) {
            printf("pull %d\n", i);
            // logInfo << "frame:" << frame << " robot:" << i << " pull" << endl;
            g_count_value += g_robots[i].value;
        }
    }



    // 此处策略：针对每一艘船
    for (int i = 0; i < BOAT_NUM; i++) {    // 船(Boat)


        // 船只状态: 移动中, 什么也不能做
        // TODO 移动过程中真的不能更改target berth嘛, 如果可以的话, 倒是可以计算到达帧数, 做个权衡
        if (g_boats[i].status == 0) {
            continue;
        }

        // 船只状态: 泊位外等待状态
        if (g_boats[i].status == 2) {
            if (frame + g_berths[g_boats[i].berthId].transportTime > LIMIT_LOAD_FRAME) {    // 没时间
                g_berths[g_boats[i].berthId].boatQueue.pop();
                g_berth_ship_count[g_boats[i].berthId]--;
                printf("go %d\n", i);
            }
            else{
                continue;
            }

        }

        // 船只状态: 正常状态(装货状态or运输完成状态)
        if (g_boats[i].status == 1) {

            // 船只位于虚拟点
            if (g_boats[i].berthId == -1) {

                if(frame < 100){
                    g_boats[i].berthId = g_init_berth[i];
                    g_berth_ship_count[g_boats[i].berthId]++;
                    g_berths[g_boats[i].berthId].boatQueue.push(g_boats[i].berthId);
                    printf("ship %d %d\n", i, g_boats[i].berthId);
                    continue;
                }

                g_boats[i].capacity = g_boat_capacity;
                g_boats[i].totalValueBoat = 0;

                // 为船只寻找合适泊位
                g_boats[i].FindSuitableBerth(frame);
                // 若有合适的泊位
                if (g_boats[i].berthId != -1) {
                    // 将船只移动到泊位
                    printf("ship %d %d\n", i, g_boats[i].berthId);
                }
            } else { // 船只位于泊位
                // 若当前帧数加上泊位运输帧数超过限定帧数, 则直接运送至虚拟点
                if (frame + g_berths[g_boats[i].berthId].transportTime > LIMIT_LOAD_FRAME) {    // 没时间
                    g_berths[g_boats[i].berthId].boatQueue.pop();
                    g_berth_ship_count[g_boats[i].berthId]--;
                    printf("go %d\n", i);
                }
                // 船只还有capacity
                if (g_boats[i].capacity > 0) {
                    // 泊位还有货

                    if (g_berths[g_boats[i].berthId].storedGoods.size() > 0) {
                    // 针对当前船只的装载速度, 装货
                        for (int k = 0; k < g_berths[g_boats[i].berthId].loadingSpeed; k ++) {
                            // 获取泊位价值最大的货物
                            auto tmpGood =  g_berths[g_boats[i].berthId].storedGoods.at(0);
                            // 船只货物价值更新
                            g_boats[i].totalValueBoat += tmpGood;
                            // 泊位货物价值更新
                            g_berths[g_boats[i].berthId].leftValueBerth -= tmpGood;
                            // 去除泊位持有的该货物
                            g_berths[g_boats[i].berthId].storedGoods.erase(g_berths[g_boats[i].berthId].storedGoods.begin());
                            // 泊位价值总量排序动态更新
                            for (auto it = g_berth_value_rank.begin(); it != g_berth_value_rank.end(); ++ it) {
                                if (it->second.second == g_boats[i].berthId) {
                                    g_lock_index berthStatus(g_berths[g_boats[i].berthId].totalValueBerth, g_boats[i].berthId);
                                    g_berth_value_rank.insert(make_pair(g_berths[g_boats[i].berthId].leftValueBerth, berthStatus));
                                    g_berth_value_rank.erase(it);
                                    break;
                                }
                            }
                            // 船只容量减一
                            g_boats[i].capacity --;
                            // 如果船只容量为0, 直接去虚拟点
                            if (g_boats[i].capacity == 0) {
                                break;
                            }
                            if (g_berths[g_boats[i].berthId].storedGoods.size() == 0) {
                                break;
                            }
                        }
                    } else { // 泊位没货了
                        g_boats[i].FindSuitableBerth(frame);
                        // 如果找到合适的泊位
                        if (g_boats[i].berthId != -1) {
                            // 如果到达目标泊位的时间+泊位到虚拟点时间小于TOTAL_FRAME,则移动船
                            if (frame + 500 + g_berths[g_boats[i].berthId].transportTime < LIMIT_LOAD_FRAME) {
                                printf("ship %d %d\n", i, g_boats[i].berthId);
                            } else {
                                continue;
                            }
                        }
                    }
                } else {
                    // 船只没容量了直接开往虚拟点
                    g_berths[g_boats[i].berthId].boatQueue.pop();
                    g_berth_ship_count[g_boats[i].berthId]--;
                    printf("go %d\n", i);
                }
            }
        }


    }


    g_lost_frame --;
    return;
}

// Pre的作用从后面看来是与PATH SCHEDULE有关的
void InitPre() {
    queue<Point> q;
    for (int i = 0; i < MAP_REAL_SIZE; i++) {
        for (int j = 0; j < MAP_REAL_SIZE; j++) {
            g_init_pre[i][j] = INVALID_POINT;
        }
    }
    bool visited[MAP_ARRAY_SIZE][MAP_ARRAY_SIZE];
    memset(visited, false, sizeof(visited));
    for (int i = 0; i < BERTH_NUM; i++) {
        Point start(g_berths[i].p.x, g_berths[i].p.y);
        q.push((start));
        visited[start.x][start.y] = true;
        g_init_pre[start.x][start.y] = start;
        // logFile << " init pre" << start.x << " " << start.y << endl;
        g_nearest_berth[start.x][start.y] = i;
    }

    while (!q.empty()) {
        Point cur = q.front();
        q.pop();
        for (int i = 0; i < 4; ++i) {
            Point next(cur.x + DIRECTION_TO_GO[i][0], cur.y + DIRECTION_TO_GO[i][1]);
            if (IsValid(next.x, next.y) && !(visited[next.x][next.y])) {
                visited[next.x][next.y] = true;
                g_init_pre[next.x][next.y] = cur; // 记录到达next的前驱节点是cur
                g_nearest_berth[next.x][next.y] = g_nearest_berth[cur.x][cur.y];
                q.push(next);
            }
        }
    }

}


void Init() {

    // 地图数据
    for (int i = 1; i <= MAP_REAL_SIZE; i++)
        scanf("%s", g_map[i] + 1);

    memset(g_berths_pull_point, -2, sizeof(g_berths_pull_point));
    memset(g_berth_ship_count, 0, sizeof(g_berth_ship_count));
    memset(g_target_position, -1, sizeof(g_target_position));
    memset(g_nearest_berth, -1, sizeof(g_nearest_berth));
    for (int i = 0; i < BERTH_NUM; i++) {
        int id;
        scanf("%d", &id);
        scanf("%d%d%d%d", &g_berths[id].p.x, &g_berths[id].p.y, &g_berths[id].transportTime,
              &g_berths[id].loadingSpeed);
        g_berths[id].id = id;   // 存储id
        g_berths[id].Init();    // 初始化
        g_berths_pull_point[g_berths[id].pullP.x][g_berths[id].pullP.y] = -1;
    }
    for (int i = 0; i < BERTH_NUM; i ++) {
        g_lock_index value(0, i);
        g_berth_value_rank.insert(make_pair(0, value));
    }
    // 船的容积
    scanf("%d", &g_boat_capacity);
    for (int i = 0; i < BOAT_NUM; i ++) {
        g_boats[i].capacity = g_boat_capacity;
        g_boats[i].id = i;
    }
    InitPre();
    // 一行 OK
    char okk[100];
    scanf("%s", okk);
    printf("OK\n");
    fflush(stdout);

}

int main() {

    ios::sync_with_stdio(false);
    cout.tie(nullptr);
    setbuf(stdout, nullptr);
    Init();
    for (int frame = 1; frame <= TOTAL_FRAME; frame++) {
        // 帧序号, 当前金钱数
        scanf("%d%d", &g_frameId, &g_money);

        int num;
        scanf("%d", &num);

        for (int i = 1; i <= num; i++)  // 场上新增num个货物
        {
            Good g;
            scanf("%d%d%d", &g.p.x, &g.p.y, &g.value);
            g.Init(frame);    // 初始化
            g_goodList.addGood(g);
        }
        for (int i = 0; i < ROBOT_NUM; i++) {   // 机器人(Robot)
            g_robots[i].id = i;
            scanf("%d%d%d%d", &g_robots[i].goods, &g_robots[i].p.x, 
                &g_robots[i].p.y, &g_robots[i].status);
            g_robots[i].CheckStatus();
        }
        for (int i = 0; i < BOAT_NUM; i++) {    // 船(Boat)
            g_boats[i].id = i;
            scanf("%d%d\n", &g_boats[i].status, &g_boats[i].berthId);

        }
        scanf("%s", g_ok);
        HandleFrame(frame);
        puts("OK");
        fflush(stdout);
    }

    return 0;
}