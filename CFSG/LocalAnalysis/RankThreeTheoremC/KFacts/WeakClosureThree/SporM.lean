module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Witness
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporMData
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Pinned
open scoped commutatorElement

section ClassTwo

variable {G : Type*} [Group G]

private theorem class_two_pow_aux (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y)
    (n : ℕ) : y ^ n * x = ⁅y, x⁆ ^ n * (x * y ^ n) := by
  have hc : y * x = ⁅y, x⁆ * (x * y) := by
    rw [commutatorElement_def]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : y * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * y := (hy.symm.pow_right n).eq
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (⁅y, x⁆ ^ n * (x * y ^ n)) := by rw [ih]
      _ = ⁅y, x⁆ ^ n * (y * x) * y ^ n := by rw [← mul_assoc, h1]; group
      _ = ⁅y, x⁆ ^ n * (⁅y, x⁆ * (x * y)) * y ^ n := by rw [hc]
      _ = ⁅y, x⁆ ^ (n + 1) * (x * y ^ (n + 1)) := by rw [pow_succ, pow_succ']; group

private theorem class_two_pow (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    (x * y) ^ n = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x ^ n * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * x ^ n := ((hx.pow_pow n n).symm).eq
    have h2 : (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
    have h3 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := h2
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * (y ^ n * x) * y) := by rw [ih]; group
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * (⁅y, x⁆ ^ n * (x * y ^ n)) * y) := by
        rw [class_two_pow_aux x y hx hy n]
      _ = ⁅y, x⁆ ^ n.choose 2 * (⁅y, x⁆ ^ n * (x ^ n * (x * y ^ n)) * y) := by
        rw [← mul_assoc (x ^ n), h1]; group
      _ = ⁅y, x⁆ ^ (n + 1).choose 2 * (x ^ (n + 1) * y ^ (n + 1)) := by
        rw [h3]; group

theorem mul_pow_three_of_commute (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y)
    (hc : ⁅y, x⁆ ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  rw [class_two_pow x y hx hy 3, show Nat.choose 3 2 = 3 from rfl, hc, one_mul]

theorem pow_three_eq_one_of_commData {n : ℕ} {q : Fin n → G} {z : G}
    {M : Matrix (Fin n) (Fin n) (ZMod 3)} (hD : CommData 3 q z M) {g : G}
    (hg : g ∈ Subgroup.closure (Set.range q)) : g ^ 3 = 1 := by
  have hz3 : ∀ c ∈ Subgroup.zpowers z, c ^ 3 = 1 := by
    rintro _ ⟨k, rfl⟩
    show (z ^ k) ^ 3 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hD.orderOf_z,
      pow_orderOf_eq_one, one_zpow]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hD.pow_q i
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hc : ⁅y, x⁆ ∈ Subgroup.zpowers z := by
      rw [commutatorElement_eq_bcomm]
      exact hD.bcomm_mem (inv_mem hy) (inv_mem hx)
    rw [mul_pow_three_of_commute x y (hD.commute_of_mem hx hc).symm
      (hD.commute_of_mem hy hc).symm (hz3 _ hc), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

end ClassTwo

theorem dichThreeAt_of_M
    {K : Type} [Group K] [Finite K] [IsSimpleGroup K] (e : K ≃* NativeSporadic.Carrier .M) :
    DichThreeAt K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e'⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  haveI : Finite CFSG.Monster.Generated.Gmat := Finite.of_equiv K e'.toEquiv
  have hD := CFSG.AGLEmbedding.Norton.MON5_7.tbCommData
  set U : Subgroup CFSG.Monster.Generated.Gmat :=
    Subgroup.closure (Set.range CFSG.AGLEmbedding.Norton.MON5_7.tbq) with hUdef
  have hUcard : Nat.card U = 3 ^ (12 + 1) := hD.card_eq
  have hUexp : ∀ u ∈ U, u ^ 3 = 1 := fun u hu => pow_three_eq_one_of_commData hD hu
  have hexp : ∀ u ∈ U.map e'.symm.toMonoidHom, u ^ 3 = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hUexp u hu, map_one]
  refine dichThreeAt_of_pair_exponent
    (KFactProofs.Stroth.WeakClosure.hasNoncommPair_three_Gmat.map e'.symm.toMonoidHom
      e'.symm.injective) (U := U.map e'.symm.toMonoidHom)
    (fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp x x.2)⟩) hexp ?_
  rw [Subgroup.card_map_of_injective e'.symm.injective, hUcard]
  norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
