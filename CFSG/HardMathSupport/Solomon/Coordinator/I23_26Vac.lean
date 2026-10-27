module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ABridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Lin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Uni
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofU3
public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.QuasithinUnique

namespace VacAut

open CFSG.Quasithin.SBd19F

theorem card_le_nine_of_model {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    {S : Type} [Group S] [Finite S] (e : (K ⧸ Subgroup.center K) ≃* S)
    (hcyc : ∀ T : Subgroup S, IsPGroup 3 ↥T → IsCyclic ↥T) (hS : OutThreeBound S)
    (E : Subgroup (MulAut K)) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have hperf : Group.IsPerfect K := (Group.isPerfect_def).2 hK.1
  have hZK : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e.symm hZK
  set Φ : MulAut K →* MulAut S := (MulAut.congr e).toMonoidHom.comp (centerDescend K) with hΦ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    apply eq_one_of_centerDescend_eq_one hK
    have : MulAut.congr e (centerDescend K α) = 1 := hα
    exact (MulAut.congr e).injective (by rw [this, map_one])
  have h9 := card_le_nine_of_outThreeBound hcyc hZ hS (E.map Φ) (by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE.2 y hy, map_one])
  rwa [Subgroup.card_map_of_injective hinj] at h9

theorem scalars_subgroupOf_le_center {n : ℕ} {F : Type} [Field F] (H : Subgroup (GL (Fin n) F)) :
    (CFSG.Open.StatedScalars (Fin n) F).subgroupOf H ≤ Subgroup.center H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  have h1 : (x : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro g
  exact Subtype.ext (h1 g)

theorem card_le_nine_linear {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F % 3 = 2)
    (e : (K ⧸ Subgroup.center K) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F))
    (E : Subgroup (MulAut K)) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3' : ¬ 3 ∣ Nat.card F - 1 := by
    have : 2 ≤ Nat.card F := by omega
    omega
  have h30 : ¬ 3 ∣ Nat.card F := by omega
  have hcyc : ∀ Q : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)), IsPGroup 3 ↥Q →
      IsCyclic ↥Q := fun Q hQ =>
    CFSG.Quasithin.F134.isCyclic_of_isPGroup_of_surjective (QuotientGroup.mk'_surjective _)
      (fun S => CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_of_le_GL_three h30 h3'
        S.isPGroup') Q hQ
  have hS : OutThreeBound (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)) :=
    (outThreeBound_psl3 F (by rw [Nat.card_units]; exact h3')).of_mulEquiv
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
  have := Finite.of_equiv _ e.toEquiv
  exact card_le_nine_of_model hK e hcyc hS E hE

theorem card_le_nine_unitary {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 3 = 1)
    (e : (K ⧸ Subgroup.center K) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 q F))
    (E : Subgroup (MulAut K)) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p, f, rfl, hU⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.exists_unitaryFieldData hF hq
  have hq2 : 2 < p ^ f := by
    have h1 : 1 < p ^ f := Nat.one_lt_pow (by have := hU.one_le; omega) hU.prime.one_lt
    omega
  have hS : OutThreeBound (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) :=
    (outThreeBound_psu3 hU hq2 (by omega)).of_mulEquiv
      (unitaryPSUEquiv hU (by norm_num)).symm
  have hZ : Subgroup.center ↥(CFSG.Open.StatedSU 3 (p ^ f) F) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.center_statedSU_eq_bot hU hq
  have hN : (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf (CFSG.Open.StatedSU 3 (p ^ f) F) =
      Subgroup.center ↥(CFSG.Open.StatedSU 3 (p ^ f) F) := by
    apply le_antisymm (scalars_subgroupOf_le_center _)
    rw [hZ]; exact bot_le
  let e2 : CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F) ≃*
      (↥(CFSG.Open.StatedSU 3 (p ^ f) F) ⧸ Subgroup.center ↥(CFSG.Open.StatedSU 3 (p ^ f) F)) :=
    QuotientGroup.quotientMulEquivOfEq hN
  have hrank : CFSG.pRank 3 (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) ≤ 1 :=
    (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num) e2.toMonoidHom e2.injective).trans
      (CFSG.RankThree.PartTwo.Sec21.census228U3Rank_holds (p ^ f) F hF hq)
  have hcyc : ∀ T : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)),
      IsPGroup 3 ↥T → IsCyclic ↥T := by
    intro T hT
    have hF' := Finite.of_equiv _ e.toEquiv
    refine CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
      (le_top : T ≤ ⊤) hT ?_
    exact (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num)
      (Subgroup.topEquiv (G := CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F))).toMonoidHom
      (Subgroup.topEquiv).injective).trans hrank
  have := Finite.of_equiv _ e.toEquiv
  exact card_le_nine_of_model hK e hcyc hS E hE

end VacAut

theorem autL3NoE27OffType_holds : AutL3NoE27OffType := by
  intro K _ _ hK hbar hnot E hE h27
  rcases hbar with ⟨F, _, _, h3, ⟨e⟩⟩ | ⟨F, _, _, q, hF, hq0, hq8, ⟨e⟩⟩
  · have hF2 : Nat.card F % 3 = 2 := by
      by_contra h
      exact hnot (Or.inl ⟨F, inferInstance, inferInstance, by omega, ⟨e⟩⟩)
    have := VacAut.card_le_nine_linear hK hF2 e E hE
    omega
  · have hq1 : q % 3 = 1 := by
      by_contra h
      exact hnot (Or.inr ⟨F, inferInstance, inferInstance, q, hF, by omega, hq8, ⟨e⟩⟩)
    have := VacAut.card_le_nine_unitary hK hF hq1 e E hE
    omega

end CFSG.HardMathSupport.Solomon.Coordinator
