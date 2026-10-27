module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.GS82PumpInputs.SporTable

open CFSG Subgroup Blueprint Assembly.LowTwoRank CatLeaf HarrisLit.T1.SporRow SporNum SporLie
open SporChev2
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def TableExcl (s : TauCeti.SporadicName) : Prop :=
  ∀ c : ℕ, OddLieOrder c → c ∣ AGLEmbedding.sporOrd s →
    ¬ CatFC.SporadicInnerRow s c ∧ ¬ CatFC.SporadicOuterRow s c

theorem tableExcl_Co1 : TableExcl .Co1 := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  subst h
  exact not_oddLieOrder_G24 hO

theorem tableExcl_Co2 : TableExcl .Co2 := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h

theorem tableExcl_Co3 : TableExcl .Co3 := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  rcases h with rfl | rfl
  · exact not_oddLieOrder_Sp62 hO
  · exact not_oddLieOrder_M12 hO

theorem tableExcl_B : TableExcl .B := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  rcases h with rfl | rfl
  · exact not_oddLieOrder_E62 hO
  · exact not_oddLieOrder_F42 hO

theorem tableExcl_M : TableExcl .M := by
  refine fun c hO hd => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  exact not_oddLieOrder_monster hd h.1 h.2 hO

theorem tableExcl_J4 : TableExcl .J4 := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h

theorem tableExcl_Th : TableExcl .Th := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h

theorem tableExcl_HN : TableExcl .HN := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h <;> subst h
  · exact not_oddLieOrder_HS hO
  · exact not_oddLieOrder_A10 hO

theorem tableExcl_McL : TableExcl .McL := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h <;> subst h
  · exact not_oddLieOrder_L34 hO
  · exact not_oddLieOrder_M11 hO

theorem tableExcl_Fi22 : TableExcl .Fi22 := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  · subst h
    exact not_oddLieOrder_U62 hO
  · rcases h with rfl | rfl
    · exact not_oddLieOrder_O8p2 hO
    · exact not_oddLieOrder_Sp62 hO

theorem tableExcl_Fi23 : TableExcl .Fi23 := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  rcases h with rfl | rfl
  · exact not_oddLieOrder_Fi22 hO
  · exact not_oddLieOrder_U62 hO

theorem tableExcl_Fi24Prime : TableExcl .Fi24Prime := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  · subst h
    exact not_oddLieOrder_Fi22 hO
  · rcases h with rfl | rfl
    · exact not_oddLieOrder_Fi23 hO
    · exact not_oddLieOrder_U62 hO

theorem tableExcl_Ly : TableExcl .Ly := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  subst h
  exact not_oddLieOrder_A11 hO

theorem tableExcl_Suz : TableExcl .Suz := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  · subst h
    exact not_oddLieOrder_L34 hO
  · rcases h with rfl | rfl
    · exact not_oddLieOrder_M12 hO
    · exact not_oddLieOrder_J2 hO

theorem tableExcl_ONan : TableExcl .ONan := by
  refine fun c hO _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h <;> subst h
  · exact not_oddLieOrder_L34 hO
  · exact not_oddLieOrder_J1 hO

theorem tableExcl_Ru : TableExcl .Ru := by
  refine fun c hO hd => ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at h
  exact not_oddLieOrder_ru hd h hO

section Table


theorem comp_data (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    {s : TauCeti.SporadicName} (hfree : CatalogueU.SporadicOddCoreFree s) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) :
    Nat.card (P ⧸ Open.fusionZStar P) ∣ AGLEmbedding.sporOrd s ∧
      (σ ∈ (MulAut.conj : S →* MulAut S).range →
        CatFC.SporadicInnerRow s (Nat.card (P ⧸ Open.fusionZStar P))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        CatFC.SporadicOuterRow s (Nat.card (P ⧸ Open.fusionZStar P))) := by
  have hσ2 := SporSmall.orderOf_eq_two h
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  rw [Nat.card_congr eZ.toEquiv]
  exact CatFC.sporadic_comp_order hMcard inferInstance hna e hσ2 hcomp

theorem false_of_tableExcl (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    {s : TauCeti.SporadicName} (hfree : CatalogueU.SporadicOddCoreFree s) (hT : TableExcl s)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hO : OddLieOrder (Nat.card (P ⧸ Open.fusionZStar P))) :
    False := by
  obtain ⟨hd, hin, hout⟩ := comp_data hMcard hfree hna e h
  obtain ⟨h1, h2⟩ := hT _ hO hd
  by_cases hσ : σ ∈ (MulAut.conj : S →* MulAut S).range
  · exact h1 (hin hσ)
  · exact h2 (hout hσ)

theorem false_of_hs (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    (hfree : CatalogueU.SporadicOddCoreFree .HS) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .HS) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) {τ : StatedLieTag} {n r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  obtain ⟨-, hin, hout⟩ := comp_data hMcard hfree hna e h
  by_cases hσ : σ ∈ (MulAut.conj : S →* MulAut S).range
  · have h360 : Nat.card (P ⧸ Open.fusionZStar P) = 360 := hin hσ
    rcases tuple_of_dvd_360 hr2 hL (h360 ▸ dvd_rfl) with ht | ht
    · exact hnot (inChev2_of_tuple_nine hL ht)
    · exact hnot (inChev2_of_tuple_five hL ht)
  · rcases (hout hσ : _ ∨ _) with h1 | h1
    · exact not_oddLieOrder_L34 (h1 ▸ oddLieOrder_of_lieModel hr hr2 hL)
    · exact hnot (SporSmall.inChev2_of_dvd_1920 hr2 hL h1)

end Table

section He


theorem false_of_he {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.He) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) {τ : StatedLieTag} {n r f : ℕ}
    (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  rcases GrSLit.simpleFixedComponents_held GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
      GrSLit.HeldFix.not_isPComponent_centralizer_heT1P S
      inferInstance hna ⟨e⟩ σ h.1 P h.2.1 h.2.2.1 h.2.2.2 with hL34 | hA7
  · exact hnot (Or.inl ⟨.PSL, 3, 2,
      SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL34, hL34⟩)
  · exact CatFC.not_lieModel_of_alt7 CatLeafProof.lieOrderFormulasInput
      (SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL) hL hA7

end He

end CFSG.ComponentClassification.GS82PumpInputs.SporTable
