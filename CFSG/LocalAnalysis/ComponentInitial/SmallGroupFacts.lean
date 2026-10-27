module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.CyclicCriterion

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem solvable_simple_abelian {G : Type*} [Group G] [IsSimpleGroup G]
    (h : Group.IsSolvable G) : ∀ a b : G, a * b = b * a :=
  IsSimpleGroup.comm_iff_isSolvable.2 h

theorem pow_mul_eq_mul_pow_mul_pow {H : Type*} [Group H] {a c z : H} (hz : z ∈ center H)
    (hca : c * a = a * c * z) (n : ℕ) : c ^ n * a = a * c ^ n * z ^ n := by
  have hzc : ∀ g : H, g * z = z * g := fun g => mem_center_iff.1 hz g
  induction n with
  | zero => simp
  | succ n ih =>
    calc c ^ (n + 1) * a = c * (c ^ n * a) := by rw [pow_succ', mul_assoc]
      _ = c * (a * c ^ n * z ^ n) := by rw [ih]
      _ = (c * a) * c ^ n * z ^ n := by simp only [mul_assoc]
      _ = a * c * z * c ^ n * z ^ n := by rw [hca]
      _ = a * c * (z * c ^ n) * z ^ n := by simp only [mul_assoc]
      _ = a * c * (c ^ n * z) * z ^ n := by rw [hzc]
      _ = a * c ^ (n + 1) * z ^ (n + 1) := by rw [pow_succ', pow_succ']; group

theorem central_commutation_power {H : Type*} [Group H] {a c z : H} (hz : z ∈ center H)
    (hca : c * a = a * c * z) (n : ℕ) : (a * c) ^ n = a ^ n * c ^ n * z ^ n.choose 2 := by
  have hzc : ∀ g : H, g * z = z * g := fun g => mem_center_iff.1 hz g
  have hzpow : ∀ (g : H) (k : ℕ), g * z ^ k = z ^ k * g := fun g k =>
    ((Commute.pow_right (hzc g) k))
  induction n with
  | zero => simp
  | succ n ih =>
    have hch : (n + 1).choose 2 = n + n.choose 2 := by
      simpa [Nat.choose_one_right] using Nat.choose_succ_succ' n 1
    have e2 : a ^ n * c ^ n * z ^ n.choose 2 * (a * c) =
        a ^ n * (c ^ n * a) * c * z ^ n.choose 2 := by
      have hz' : z ^ n.choose 2 * (a * c) = (a * c) * z ^ n.choose 2 :=
        (hzpow (a * c) _).symm
      calc a ^ n * c ^ n * z ^ n.choose 2 * (a * c)
          = a ^ n * c ^ n * (z ^ n.choose 2 * (a * c)) := by rw [mul_assoc]
        _ = a ^ n * c ^ n * ((a * c) * z ^ n.choose 2) := by rw [hz']
        _ = a ^ n * (c ^ n * a) * c * z ^ n.choose 2 := by simp only [mul_assoc]
    have hz2 : z ^ n * c = c * z ^ n := (hzpow c n).symm
    rw [pow_succ, ih, e2, pow_mul_eq_mul_pow_mul_pow hz hca, hch, pow_add z n (n.choose 2)]
    calc a ^ n * (a * c ^ n * z ^ n) * c * z ^ n.choose 2
        = a ^ n * a * c ^ n * (z ^ n * c) * z ^ n.choose 2 := by simp only [mul_assoc]
      _ = a ^ n * a * c ^ n * (c * z ^ n) * z ^ n.choose 2 := by rw [hz2]
      _ = a ^ (n + 1) * c ^ (n + 1) * (z ^ n * z ^ n.choose 2) := by
          rw [pow_succ, pow_succ]
          simp only [mul_assoc]

theorem pgroup_rank_one_abelian_subgroups {p : ℕ} (hp : p.Prime) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) :
    CFSG.pRank p P ≤ 1 ↔ ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B := by
  have : Fact p.Prime := ⟨hp⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  constructor
  · intro hrank B hB
    let : CommGroup B := { (inferInstance : Group B) with mul_comm := hB.is_comm.comm }
    refine (CFSG.RankTwoShapes.isCyclic_iff_elementary_card_le (hP.to_subgroup B)).2 fun E hE => ?_
    have hEel : CFSG.Open.IsElemAbelian p (E.map B.subtype) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨x', -, hx'⟩ := Subgroup.mem_map.1 x.2
        obtain ⟨y', -, hy'⟩ := Subgroup.mem_map.1 y.2
        apply Subtype.ext
        change (x : P) * y = y * x
        rw [← hx', ← hy']
        exact congrArg Subtype.val (mul_comm x' y')
      · obtain ⟨x', hx'E, rfl⟩ := Subgroup.mem_map.1 hx
        change ((x' : P)) ^ p = 1
        rw [← Subgroup.coe_pow, hE x' hx'E, Subgroup.coe_one]
    have hEp : IsPGroup p (E.map B.subtype) := hP.to_subgroup _
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hEp
    have hle := CFSG.SectionRank.le_pRank hp.one_lt (le_top) hEel hk
    have hk1 : k ≤ 1 := hle.trans hrank
    rw [Subgroup.card_map_of_injective B.subtype_injective] at hk
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  · intro hcyc
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
    have : IsCyclic E := hcyc E hE.1
    have hexp : Monoid.exponent E ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun e => Subtype.ext (by simpa using hE.2 e e.2)
    rw [← IsCyclic.exponent_eq_card, pow_one]
    exact Nat.le_of_dvd hp.pos hexp

end CFSG.LocalAnalysis.ComponentInitial
