module

public import CFSG.LocalAnalysis.ComponentClassification.GS82L34P9Defs
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStableCentre
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedGS (gsFixedLayer)

theorem he_fusionZStar_sq_eq_one
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.He) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (htype : IsL34Type (↥P ⧸ Open.fusionZStar ↥P)) :
    ∀ z ∈ Open.fusionZStar ↥P, z * z = 1 := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  have hd : 20160 ∣ Nat.card P := L34PF.dvd_card_of_isL34Type htype
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · obtain ⟨ht2, hPC, -, -⟩ := h.inner hna ht
    have hPp : ⁅P, P⁆ = P := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ h.2.2.1
      exact (Subgroup.isPerfect_iff (H := P)).mp (Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe h.2.1).toMonoidHom) (subgroupOfEquivOfLe h.2.1).surjective)
    have hL : Nonempty (↥(⊤ : Subgroup S) ≃* NativeSporadic.He) := ⟨Subgroup.topEquiv.trans e⟩
    have hPtC : P ≤ (⊤ : Subgroup S) ⊓ centralizer ({t} : Set S) := le_inf le_top hPC
    by_cases hK : gsFixedLayer (⊤ : Subgroup S) t = ⊥
    ·
      exfalso
      have h1 := (heldTwoBFact S ⊤ hL t (mem_top t) ht2 hK).1
      have h2 : 20160 ∣ 21504 := h1 ▸ hd.trans (Subgroup.card_dvd_of_le hPtC)
      norm_num at h2
    ·
      have hu : HeldTwoA (⊤ : Subgroup S) t := ⟨mem_top t, ht2, hK⟩
      obtain ⟨hZK, hperfK, hcent⟩ := heldTwoAKFact S ⊤ hL t hu
      obtain ⟨hKp, hKt⟩ := heldTwoALayerFact S ⊤ hL t hu
      have hPeq : P = gsFixedLayer ⊤ t := HeZ.eq_of_card_ge hKt hKp hZK (hperfK P hPtC hPp)
        hPp (Nat.le_of_dvd Nat.card_pos hd)
      subst hPeq
      set P := gsFixedLayer (⊤ : Subgroup S) t
      have hcardP : Nat.card P = 20160 * 4 := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥P), card_of_isL34Type hKt,
          hZK]
      have hZs : Nat.card (Open.fusionZStar ↥P) = 4 := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar ↥P)
        rw [card_of_isL34Type htype, hcardP] at h1
        omega
      have hZeq : center ↥P = Open.fusionZStar ↥P :=
        Subgroup.eq_of_le_of_card_ge (center_le_fusionZStar P) (by rw [hZs, hZK])
      intro z hz
      rw [← hZeq] at hz
      have hzc : ∀ k ∈ P, (z : S) * k = k * z := fun k hk =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)).symm
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      rcases hcent (z : S) (mem_top _) hzc with h1 | ⟨⟨-, h2, -⟩, -⟩
      · rw [h1, mul_one]
      · rw [← sq, ← h2, pow_orderOf_eq_one]
  ·
    exfalso
    have h1 := SeitzReduction.SporadicRefine.he_outer_card_fixedSubgroup e hσ2 hout
    have h2 : 20160 ∣ 15120 := h1 ▸ hd.trans (Subgroup.card_dvd_of_le h.2.1)
    norm_num at h2

private theorem fusionZStar_eq_center_of_oddCoreFree
    {s : TauCeti.SporadicName} (hs : CatalogueU.SporadicOddCoreFree s) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (htype : IsL34Type (↥P ⧸ Open.fusionZStar ↥P)) :
    Open.fusionZStar ↥P = center ↥P := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hs hna e) hσ2
  exact L34PF.fusionZStar_eq_center_of_comp h (h.isComponent_of_oddCore hcore).1 htype

private theorem pumpRow_of_evenLie
    (hGA : TBLit.GriessMultipliersAllModels) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hL34 : IsL34Type (↥P ⧸ Open.fusionZStar ↥P)) :
    (NativeSporadic.IsSporadic S .He ∧ ∀ z ∈ Open.fusionZStar ↥P, z * z = 1) ∨
      (NativeSporadic.IsSporadic S .ONan ∧ Nat.card ↥(Open.fusionZStar ↥P) = 4) ∨
      (Open.fusionZStar ↥P = ⊥ ∧ CentreTwoPartLe S 2) := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · exfalso
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    · rcases hU with ho | ⟨n, -, h7, hA⟩ | hL | hH
      · exact absurd hL34 (not_held_not_L34_of_properFixedComponent_oddLie
          gls3OddLieAutComponentsInput_holds CatLeafProof.lieOrderFormulasInput hna ho h).2
      · obtain ⟨θ⟩ := hA
        exact absurd hL34 (not_isL34Type_of_properFixedComponent_alternating (by omega) θ h)
      · exact (L34PF.false_of_isL34Type_self h hL34 hL).elim
      · obtain ⟨eHe⟩ := hH
        exact Or.inl ⟨⟨eHe⟩, he_fusionZStar_sq_eq_one hna eHe h hL34⟩
  · obtain ⟨τ, n, f, hadm, hm⟩ := heven
    by_cases hτ : τ ∈ classicalTags
    · by_cases hexc : (τ = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨ (τ = .PSU ∧ n = 6 ∧ f = 1) ∨
          (τ = .PSL ∧ n = 3 ∧ f = 2)
      ·
        exfalso
        obtain ⟨eP⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
        have hL' : IsL34Type (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
            Open.fusionZStar ↥(P.subgroupOf (fixedSubgroup σ))) :=
          LieType.CurtisTits.lieModel_of_mulEquiv eP hL34
        rcases hexc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact evenLieExcOuterL34Input_holds S .POmegaPlus 4 1 (by simp) hm σ hσ2 hout _
            h.2.2.1 hL'
        · exact evenLieExcOuterL34Input_holds S .PSU 6 1 (by simp) hm σ hσ2 hout _ h.2.2.1 hL'
        · exact L34PF.false_of_isL34Type_self h hL34 hm
      ·
        have eP := subgroupOfEquivOfLe h.2.1
        have hdP := L34PF.dvd_card_of_isL34Type hL34
        have hd : 20160 ∣ Nat.card ↥(P.subgroupOf (fixedSubgroup σ)) := by
          rw [Nat.card_congr eP.toEquiv]
          exact hdP
        have hs := L34PF.isSimpleGroup_of_classical_outer hτ hadm hm hσ2 hout h.2.2.1 hd
        have : IsSimpleGroup P := eP.symm.isSimpleGroup
        have hnaP : ∃ a b : P, a * b ≠ b * a :=
          HeldBalSpor.exists_mul_ne_mul_of_four_dvd ((show 4 ∣ 20160 by norm_num).trans hdP)
        exact Or.inr (Or.inr ⟨L34PF.fusionZStar_eq_bot_of_simple hnaP
          ((show 2 ∣ 20160 by norm_num).trans hdP),
          centreTwoPartLe_two_of_classical hGA hτ hm hexc⟩)
    · exfalso
      have hτ' : τ ≠ .PSL ∧ τ ≠ .PSU ∧ τ ≠ .PSp ∧ τ ≠ .POmegaOdd ∧ τ ≠ .POmegaPlus ∧
          τ ≠ .POmegaMinus := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hτ (by decide)
      obtain ⟨eP⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
      exact L34R.not_isL34Type_outer_nonclassical CatLeafProof.lieOrderFormulasInput hτ' hadm
        hm hσ2 hout h.2.2.1 (LieType.CurtisTits.lieModel_of_mulEquiv eP hL34)

section Rows


theorem l34ExpFourPumpLeaf_holds : L34ExpFourPumpLeaf := by
  intro S _ _ hs hna hcat σ P h hL34
  have : IsSimpleGroup S := hs
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, hA⟩ | ho | he | hsp
  · obtain ⟨θ⟩ := hA
    exact absurd hL34 (not_isL34Type_of_properFixedComponent_alternating hn θ h)
  · exact absurd hL34 (not_held_not_L34_of_properFixedComponent_oddLie
      gls3OddLieAutComponentsInput_holds CatLeafProof.lieOrderFormulasInput hna ho h).2
  · exact pumpRow_of_evenLie HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      hna he h hL34
  · rcases HeldBalSpor.sporadicL34ComponentsInput_holds S hs hsp σ P h hL34 with
      ⟨⟨e⟩, hZP⟩ | ⟨⟨e⟩, hZP4⟩ | hHe
    ·
      refine Or.inr (Or.inr ⟨?_, fun L _ _ hq he T =>
        centreTwoPartLe_suz_cert L hq (he.map fun e' => e'.trans e) T⟩)
      rw [fusionZStar_eq_center_of_oddCoreFree CatalogueU.sporadicOddCoreFree_Suz hna e h hL34]
      exact Subgroup.eq_bot_of_card_eq _ hZP
    ·
      refine Or.inr (Or.inl ⟨⟨e⟩, ?_⟩)
      rw [fusionZStar_eq_center_of_oddCoreFree Sporadic.ONOddCore.sporadicOddCoreFree_ONan hna e
        h hL34]
      exact hZP4
    · obtain ⟨e⟩ := hHe
      exact Or.inl ⟨⟨e⟩, he_fusionZStar_sq_eq_one hna e h hL34⟩

end Rows

end CFSG.ComponentClassification.GS82PumpInputs
