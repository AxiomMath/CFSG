module

public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.GH74.Uniqueness.Bender.Linear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiFamilyNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOrders
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiCommutant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiIrreducibleAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section SzG

open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator CFSG.BenderSuzuki.MatrixGroups

theorem suzuki_derangement_relIndex_eq_four
    {m : ℕ} (hm : 0 < m) {x : SuzukiMatrixGroup m}
    (hx : suzukiDerangement m x) :
    (centralizer ({x} : Set (SuzukiMatrixGroup m))).relIndex
      (normalizer ((centralizer ({x} : Set (SuzukiMatrixGroup m)) : Subgroup _) : Set _)) = 4 := by
  classical
  let := suzukiDerangementCentralizerAction m
  let A : suzukiDerangementCentralizers m := ⟨centralizer ({x} : Set (SuzukiMatrixGroup m)), x, hx, rfl⟩
  let c : suzukiDerangementCentralizerClasses m := Quotient.mk'' A
  let R := suzukiDerangementCentralizerRepresentative m c
  have h1 : (Quotient.mk'' A : suzukiDerangementCentralizerClasses m) = Quotient.mk'' R := by
    change c = Quotient.mk'' (Quotient.out c)
    exact (Quotient.out_eq c).symm
  have h2 := Quotient.exact h1
  have h3 : A ∈ MulAction.orbit (SuzukiMatrixGroup m) R := (MulAction.orbitRel_apply).mp h2
  obtain ⟨s, hs⟩ := h3
  have hAR : A.val = R.val.map (MulAut.conj s).toMonoidHom := congrArg Subtype.val hs.symm
  have h4 := suzuki_derangement_family_normalizer_index_eq_four m hm c
  have hA : A.val = centralizer ({x} : Set (SuzukiMatrixGroup m)) := rfl
  rw [← hA, hAR]
  rw [← Subgroup.map_normalizer_eq_of_bijective R.val (MulAut.conj s).bijective]
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj s).injective]
  exact h4

end SzG

section Transport

open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator CFSG.BenderSuzuki.MatrixGroups

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem BenderType.suzuki_derangement_type
    {n e : ℕ} (h : BenderType K n 2 e) {x : K}
    (hx1 : x ≠ 1) (hdiv : orderOf x ∣ (2 ^ n) ^ 2 + 1) :
    IsCyclic (centralizer ({x} : Set K)) ∧ Odd (Nat.card (centralizer ({x} : Set K))) ∧
      (∃ a, n = 2 * a + 1 ∧
        (Nat.card (centralizer ({x} : Set K)) = 2 ^ n - 2 ^ (a + 1) + 1 ∨
          Nat.card (centralizer ({x} : Set K)) = 2 ^ n + 2 ^ (a + 1) + 1)) ∧
      Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) =
        4 * Nat.card (centralizer ({x} : Set K)) := by
  cases h with
  | suzuki a ha e₁ =>
    let ε : K ≃* SuzukiMatrixGroup a :=
      e₁.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a))
    have hy1 : ε x ≠ 1 := fun h1 => hx1 (ε.injective (by rw [h1, map_one]))
    have hydiv : orderOf (ε x) ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
      have h0 : orderOf (ε x) = orderOf x := orderOf_injective ε.toMonoidHom ε.injective x
      rw [h0]
      exact hdiv
    have hC : (centralizer ({x} : Set K)).map ε.toMonoidHom = centralizer ({ε x} : Set _) :=
      map_centralizer_singleton ε x
    obtain ⟨hcyc, hodd⟩ := suzuki_degree_divisor_centralizer_cyclic_odd a ha (ε x) hy1 hydiv
    have hcard := suzuki_degree_divisor_entire_centralizer_exact_order a ha (ε x) hy1 hydiv
    have hder : suzukiDerangement a (ε x) := suzuki_degree_divisor_derangement a (ε x) hy1 hydiv
    have hidx := suzuki_derangement_relIndex_eq_four ha hder
    have hcardC : Nat.card (centralizer ({x} : Set K)) = Nat.card (centralizer ({ε x} : Set _)) := by
      rw [← hC, Subgroup.card_map_of_injective ε.injective]
    refine ⟨?_, ?_, ⟨a, rfl, ?_⟩, ?_⟩
    · have e2 : (centralizer ({x} : Set K)) ≃* (centralizer ({ε x} : Set _)) :=
        (Subgroup.equivMapOfInjective _ ε.toMonoidHom ε.injective).trans
          (MulEquiv.subgroupCongr hC)
      exact e2.isCyclic.mpr hcyc
    · rw [hcardC]
      exact hodd
    · rw [hcardC]
      exact hcard
    ·
      set C := centralizer ({ε x} : Set _) with hCdef
      have hN : (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)).map ε.toMonoidHom =
          normalizer (C : Set (SuzukiMatrixGroup a)) := by
        rw [← hC]
        exact Subgroup.map_normalizer_eq_of_bijective _ ε.bijective
      have h5 : Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) =
          Nat.card (normalizer (C : Set (SuzukiMatrixGroup a))) := by
        rw [← hN, Subgroup.card_map_of_injective ε.injective]
      rw [h5]
      have h6 := Subgroup.card_mul_index (C.subgroupOf (normalizer (C : Set (SuzukiMatrixGroup a))))
      have h7 : Nat.card (C.subgroupOf (normalizer (C : Set (SuzukiMatrixGroup a)))) = Nat.card C :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
      rw [h7] at h6
      change Nat.card C * C.relIndex (normalizer (C : Set (SuzukiMatrixGroup a))) = _ at h6
      rw [hidx] at h6
      rw [← h6, mul_comm, hcardC]

end Transport

end CFSG.GH74.Uniqueness.Bender
