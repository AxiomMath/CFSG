module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.RankThree.PartOne.CTP.StrongPLinear

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.SectionRank.LocalWitness CFSG.RankThree.PartOne.StrongP
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem pow_mul_eq_of_mul_eq {a b c : G} (h : b * a = a * b * c) (hcb : Commute c b) (n : ℕ) :
    b ^ n * a = a * b ^ n * c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcbn : Commute c (b ^ n) := hcb.pow_right n
    calc b ^ (n + 1) * a = b * (b ^ n * a) := by rw [pow_succ', mul_assoc]
      _ = b * (a * b ^ n * c ^ n) := by rw [ih]
      _ = (b * a) * b ^ n * c ^ n := by simp only [mul_assoc]
      _ = a * b * c * b ^ n * c ^ n := by rw [h]
      _ = a * b * (c * b ^ n) * c ^ n := by simp only [mul_assoc]
      _ = a * b * (b ^ n * c) * c ^ n := by rw [hcbn.eq]
      _ = a * (b * b ^ n) * (c * c ^ n) := by simp only [mul_assoc]
      _ = a * b ^ (n + 1) * c ^ (n + 1) := by rw [← pow_succ', ← pow_succ']

theorem mul_pow_eq_of_mul_eq {a b c : G} (h : b * a = a * b * c) (hca : Commute c a)
    (hcb : Commute c b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n * c ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcC : Commute (c ^ n.choose 2) (a * b) := (hca.pow_left _).mul_right (hcb.pow_left _)
    have hcb' : Commute c b := hcb
    calc (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := pow_succ _ _
      _ = a ^ n * b ^ n * c ^ n.choose 2 * (a * b) := by rw [ih]
      _ = a ^ n * b ^ n * (c ^ n.choose 2 * (a * b)) := by simp only [mul_assoc]
      _ = a ^ n * b ^ n * ((a * b) * c ^ n.choose 2) := by rw [hcC.eq]
      _ = a ^ n * (b ^ n * a) * b * c ^ n.choose 2 := by simp only [mul_assoc]
      _ = a ^ n * (a * b ^ n * c ^ n) * b * c ^ n.choose 2 := by
        rw [pow_mul_eq_of_mul_eq h hcb n]
      _ = a ^ n * a * b ^ n * (c ^ n * b) * c ^ n.choose 2 := by simp only [mul_assoc]
      _ = a ^ n * a * b ^ n * (b * c ^ n) * c ^ n.choose 2 := by
        rw [(hcb.pow_left n).eq]
      _ = a ^ (n + 1) * b ^ (n + 1) * c ^ (n + n.choose 2) := by
        rw [pow_succ a n, pow_succ b n, pow_add]
        simp only [mul_assoc]

      _ = a ^ (n + 1) * b ^ (n + 1) * c ^ (n + 1).choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]

theorem isPGroup_closure_of_central_commutator {p : ℕ} (hp : p.Prime) {x y : G} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    IsPGroup p (Subgroup.closure ({x, y} : Set G)) := by
  set z := ⁅x, y⁆ with hzdef
  have hz : z ^ p = 1 := by
    rw [hzdef, commutator_pow_eq hzx, hx, commutatorElement_one_left]
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  obtain ⟨i, j, k, -, -, -, hg⟩ := mem_closure_normalForm hp.pos hx hy hzx hzy g.2
  have h1 : y * x ^ i = x ^ i * y * z ^ ((p - 1) * i) := y_mul_x_pow hp.pos hzx hzy hz i
  have h2 : y ^ j * x ^ i = x ^ i * y ^ j * (z ^ ((p - 1) * i)) ^ j :=
    pow_mul_eq_of_mul_eq h1 (hzy.pow_left _) j
  set c : G := (z ^ ((p - 1) * i)) ^ j with hc
  have hcx : Commute c (x ^ i) := ((hzx.pow_left _).pow_left _).pow_right _
  have hcy : Commute c (y ^ j) := ((hzy.pow_left _).pow_left _).pow_right _
  have hu : (x ^ i * y ^ j) ^ p = c ^ p.choose 2 := by
    rw [mul_pow_eq_of_mul_eq h2 hcx hcy p, ← pow_mul, mul_comm i p, pow_mul, hx, one_pow,
      ← pow_mul, mul_comm j p, pow_mul, hy, one_pow, one_mul, one_mul]
  have hcp : c ^ p = 1 := by
    have : c ^ p = (z ^ p) ^ ((p - 1) * i * j) := by
      rw [hc, ← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
    rw [this, hz, one_pow]
  have hzk : Commute (x ^ i * y ^ j) (z ^ k) :=
    ((hzx.symm.pow_left i).pow_right k).mul_left ((hzy.symm.pow_left j).pow_right k)
  rw [← hzdef] at hg
  have hgp : (g : G) ^ p = c ^ p.choose 2 := by
    have hzkp : (z ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
    rw [hg, hzk.mul_pow, hu, hzkp, mul_one]
  show (g : G) ^ p ^ 2 = 1
  rw [sq, pow_mul, hgp, ← pow_mul, mul_comm, pow_mul, hcp, one_pow]

theorem hasNoncommPair_of_central_commutator {p : ℕ} (hp : p.Prime) {x y : G} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hz : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    HasNoncommPair p G :=
  ⟨x, y, hx, hy, fun h => hz (commutatorElement_eq_one_iff_mul_comm.2 h),
    isPGroup_closure_of_central_commutator hp hx hy hzx hzy⟩

end CFSG.AGLEmbedding.Norton.MON11_13
