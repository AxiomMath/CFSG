module

public import CFSG.CGT.PushingUpLit.CGT6K1.InnerBase
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenInner

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem center_SL_two_eq_bot_of_charTwo {K : Type*} [Field K] [CharP K 2] :
    center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcA, hc1]
  simp [Matrix.one_apply]

theorem lieModel_PSL_two_of_mulEquiv_SL_two {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : LieModel X .PSL 2 2 n := by
  have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK'
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let eP : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_SL_two_eq_bot_of_charTwo.symm)
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance,
    inferInstance, hK', ⟨(e.trans eP).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem even_lie_type_no_inner_datum
    {D : Type} [Group D] [Finite D] (hDs : IsSimpleGroup D) (heven : EvenLieType D) {n : ℕ}
    (hn : 2 ≤ n) (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n) (α : MulAut D)
    (hα : orderOf α = 2) (hin : α ∈ (MulAut.conj : D →* MulAut D).range) (S : Subgroup D)
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) : False := by
  obtain ⟨hD's, hD'nab, ⟨eD'⟩⟩ := fixedRoot_simple hn hK hSα hSK
  set D' : Subgroup (fixedSubgroup α) := S.subgroupOf (fixedSubgroup α) with hD'def
  have hD' : IsComponent D' :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hD'nab).1, hSn.isSubnormal⟩
  have hZD' : center D' = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hD'nab).2
  have hLie : LieModel (D' ⧸ center D') .PSL 2 2 n :=
    lieModel_PSL_two_of_mulEquiv_SL_two hn hK
      (((QuotientGroup.quotientMulEquivOfEq hZD').trans QuotientGroup.quotientBot).trans eD')
  have hnab : ∃ x y : D, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hD'nab
    exact ⟨a.1.1, b.1.1, fun h => hab (Subtype.ext (Subtype.ext h))⟩
  exact CFSG.SeitzReduction.LinearPilot.catSLmEvenInner D hDs hnab heven α hα hin 2 n D' hD' hLie

end CFSG.CGT.PushingUpLit.CGT6K1
