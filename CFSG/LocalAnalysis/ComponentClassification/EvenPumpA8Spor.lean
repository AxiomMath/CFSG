module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause1
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Proof
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.McLLyInnerCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLoc
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.Monster.SteinbergMSporadicOddCoreFree

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem card_of_alt8 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 8)) :
    Nat.card X = 20160 := by
  rw [SolMax.card_of_mulEquiv_alt (by norm_num) e]
  decide

private theorem false_of_held_alt8
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (eS : S ≃* NativeSporadic.He) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 8)) :
    False := by
  rcases GrSLit.simpleFixedComponents_held GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
      GrSLit.HeldFix.not_isPComponent_centralizer_heT1P S
      inferInstance hna ⟨eS⟩ σ h.1 P h.2.1 h.2.2.1 h.2.2.2 with hL | ⟨⟨eA⟩⟩
  · exact ((PSL3Four.excludes_alternating_models_stated _
      (statedClassicalModel_of_lieModel_psl hL)).2.2 (Fin 8) (by simp)).false eP
  · have h1 := card_of_alt8 (eA.symm.trans eP)
    have h2 := SolMax.card_of_mulEquiv_alt (by norm_num)
      (MulEquiv.refl (alternatingGroup (Fin 7)))
    rw [h1] at h2
    revert h2
    decide

private theorem a8PumpOutcome_of_oddCore (I : CatFC.ArmInputs)
    (hT : CatFC.EvenOuterTypedInput) (hHSO : CatFC.HeSuzONNoAltEight)
    (hMcL : ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      (S ≃* NativeSporadic.Carrier .McL) → ∀ {σ : MulAut S}, orderOf σ = 2 →
      σ ∈ (MulAut.conj : S →* MulAut S).range → ∀ {D : Subgroup ↥(fixedSubgroup σ)},
      IsComponent D → Nat.card (center ↥D) = 2)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hcore : CFSG.oddCore (fixedSubgroup σ) = ⊥)
    (hPex : Open.fusionZStar ↥P = pPrimeCore 2 ↥P)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 8)) : A8PumpOutcome S := by
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  rcases CatFC.clause1_of_inputs I hT hHSO hMcL hna hcat hσ2 hcomp ⟨eZ.symm.trans eP⟩ with
    ⟨m, hm, hθ⟩ | hHS | hL | ⟨-, hZ⟩
  · exact .inl ⟨2 * m, even_two_mul m, by omega, hθ⟩
  · exact .inr (.inr hHS)
  · exact .inr (.inl hL)
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (P.subgroupOf (fixedSubgroup σ)))
    rw [hZ, ← Nat.card_congr eZ.toEquiv, card_of_alt8 eP,
      Nat.card_congr (subgroupOfEquivOfLe h.2.1).toEquiv] at hL
    have hP := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar P)
    rw [card_of_alt8 eP, hL, hPex] at hP
    have h2 : Nat.card (pPrimeCore 2 P) = 2 := by omega
    have hodd := pPrimeCore_coprime_card (p := 2) (G := P)
    rw [h2] at hodd
    exact absurd hodd (by decide)

private theorem a8SporadicClause_of_inputs
    (I : CatFC.ArmInputs) (hT : CatFC.EvenOuterTypedInput) (hHSO : CatFC.HeSuzONNoAltEight)
    (hMcL : ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      (S ≃* NativeSporadic.Carrier .McL) → ∀ {σ : MulAut S}, orderOf σ = 2 →
      σ ∈ (MulAut.conj : S →* MulAut S).range → ∀ {D : Subgroup ↥(fixedSubgroup σ)},
      IsComponent D → Nat.card (center ↥D) = 2)
    (hfree : ∀ s : TauCeti.SporadicName, s ≠ .He → CatalogueU.SporadicOddCoreFree s) :
    A8PumpSporadicClause := by
  intro S _ _ _ hna ⟨s, ⟨e⟩⟩ σ P h hPex ⟨eP⟩
  by_cases hs : s = .He
  · subst hs
    exact (false_of_held_alt8 hna e h eP).elim
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  have hcore : CFSG.oddCore (fixedSubgroup σ) = ⊥ :=
    oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree (hfree s hs) hna e) hσ2
  have hcat : Catalog S :=
    Milestones.ct_catalog_nonabelian_type_partition_converse S (.inr (.inr (.inr ⟨s, ⟨e⟩⟩)))
  exact a8PumpOutcome_of_oddCore I hT hHSO hMcL hna hcat h hcore hPex eP

theorem a8SporadicClause_holds
    : A8PumpSporadicClause :=
  a8SporadicClause_of_inputs CatFC.armInputs_holds CatFC.evenOuterTypedInput_holds
    CatFC.heSuzONNoAltEight_proved CatFC.mcl_inner_component_center fun s hs => by
      cases s with
      | M11 => exact CatalogueU.sporadicOddCoreFree_M11
      | M12 => exact CatalogueU.sporadicOddCoreFree_M12
      | M22 => exact CatalogueU.sporadicOddCoreFree_M22
      | M23 => exact CatalogueU.sporadicOddCoreFree_M23
      | M24 => exact CatalogueU.sporadicOddCoreFree_M24
      | J1 => exact Foote5.sporadicOddCoreFree_J1
      | J2 => exact CatalogueU.sporadicOddCoreFree_J2
      | J3 => exact CatalogueU.sporadicOddCoreFree_J3
      | J4 => exact CatalogueU.sporadicOddCoreFree_J4
      | Co1 => exact CatalogueU.sporadicOddCoreFree_Co1
      | Co2 => exact Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
      | Co3 => exact Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
      | Fi22 => exact CatalogueU.sporadicOddCoreFree_Fi22
      | Fi23 => exact CatalogueU.sporadicOddCoreFree_Fi23
      | Fi24Prime => exact CatalogueU.sporadicOddCoreFree_Fi24Prime
      | HS => exact CatalogueU.sporadicOddCoreFree_HS
      | McL => exact CatalogueU.sporadicOddCoreFree_McL
      | He => exact absurd rfl hs
      | Ru => exact CatalogueU.sporadicOddCoreFree_Ru
      | Suz => exact CatalogueU.sporadicOddCoreFree_Suz
      | ONan => exact Sporadic.ONOddCore.sporadicOddCoreFree_ONan
      | HN => exact Sporadic.HNOddCore.sporadicOddCoreFree_HN
      | Ly => exact Sporadic.LySchreier.sporadicOddCoreFree_Ly
      | Th => exact Sporadic.ThSchreier.sporadicOddCoreFree_Th
      | B => exact BMCase.sporadicOddCoreFree_B
      | M => exact CatalogueU.sporadicOddCoreFree_M

end CFSG.ComponentClassification.EvenPump
