module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.EightTenI.SymThreeLift
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.EightTenI.AltNaturalType
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortClauses
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightBlockOfThetaX

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure CFSG CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19 CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem outcomeFive_of_caseA (h84 : Asc81bEightFour)
    (hAut : SymAutInner) (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {m r s : ℕ} (hm : 8 < m) (hmeven : Even m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    (hN : NaturalSectionLSL S L m) (hr1 : 1 ≤ r) (hrs : 2 * r + s = m)
    (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) (hs6 : 6 ≤ s)
    (hEBX : EightBlockDataX S L r s) (hY : HasSym3LiftS S L (L ⊔ S)) :
    ∃ N r' : ℕ, Even N ∧ 2 * r' ≤ N ∧ 1 ≤ r' ∧ 6 ≤ N - 2 * r' ∧
      EightBlockData X S L r' (N - 2 * r') ∧ IsShort2 L ∧ IsTypeScriptL L := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hcenM : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_center_barM_sup_eq_one hA' hLs hSL hm e)
  have hcore : L ⊓ pCoreOf 2 X = L ⊓ pCoreOf 2 (L ⊔ S) :=
    Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL
  have hcenX : Subgroup.center ↥(barM X L) = ⊥ := by
    let E := CFSG.HardMathSupport.Cooperstein.Proving.barMEquiv hL.le (le_sup_left : L ≤ L ⊔ S) hcore
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hEz : E z ∈ Subgroup.center ↥(barM (L ⊔ S) L) := by
      rw [Subgroup.mem_center_iff]
      intro c
      have := Subgroup.mem_center_iff.1 hz (E.symm c)
      have h2 := congrArg E this
      simpa [map_mul] using h2
    rw [hcenM] at hEz
    exact E.injective (by simpa using Subgroup.mem_bot.1 hEz)
  obtain ⟨Y, hSY, hYM, hSyl, hS3, -, y, hyL, hyY, hy, hyQ⟩ := hY
  have hQV := commutator_pCore_le_blockV_of_sym3_lift h84 hX hA hL hcenX hYM hSY hSyl hS3
    hyL hyY hy hyQ
  have hirr := hasIrr_of_naturalSectionL (by omega) hN.naturalSectionL
  have hshort := isShort2_of_hQV_of_center_eq_bot hX hA hL hirr hQV hcenX
  have hAltT := isAltNaturalType_of_natural_section hX hA hL (by omega) e hN hQV hshort
  have hsub : m - 2 * r = s := by omega
  refine ⟨m, r, hmeven, by omega, hr1, by omega, ?_, hshort, Or.inr (Or.inl ⟨m, hAltT⟩)⟩
  rw [hsub]
  exact hEBX X hA hL hSL hAut


theorem isAltType_of_isAltNaturalType {n : ℕ} (hn : Odd n) (h : IsAltNaturalType L n) :
    IsAltType L n := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hR⟩ := h
  set q := QuotientAddGroup.mk' (evenWeightOnes n) with hq
  have hqinj : Function.Injective q := by
    rw [← AddMonoidHom.ker_eq_bot_iff, QuotientAddGroup.ker_mk',
      CFSG.RankThree.PartTwo.Sec19.Item194Proof.evenWeightOnes_eq_bot hn]
  let e : evenWeight n ≃+ altHeart n :=
    AddEquiv.ofBijective q ⟨hqinj, QuotientAddGroup.mk'_surjective _⟩
  have he : ∀ x, e x = q x := fun x => rfl
  refine ⟨α, hαs, hαk, (AddMonoidHom.toMultiplicative e.symm.toAddMonoidHom).comp β,
    e.symm.surjective.comp hβs, ?_, fun ℓ u v huv i => ?_⟩
  · rw [← hβk]
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hu
      have h1 : e.symm (Multiplicative.toAdd (β u)) = 0 := congrArg Multiplicative.toAdd hu
      have h2 : Multiplicative.toAdd (β u) = 0 := by
        have := congrArg e h1
        simpa using this
      exact congrArg Multiplicative.ofAdd h2
    · intro hu
      rw [hu, map_one]
  · set x := e.symm (Multiplicative.toAdd (β u)) with hx
    have hux : Multiplicative.toAdd (β u) = (x : altHeart n) := by
      rw [hx]; exact (e.apply_symm_apply _).symm
    have h1 := hR ℓ u v huv x hux
    have h2 : e.symm (Multiplicative.toAdd (β v)) = evenWeightPerm (α ℓ : Equiv.Perm (Fin n)) x := by
      rw [h1]
      exact e.symm_apply_apply _
    change ((e.symm (Multiplicative.toAdd (β v)) : evenWeight n) : Fin n → ZMod 2) i = _
    rw [h2]
    rfl

theorem outcomeOne_of_caseA_odd (h84 : Asc81bEightFour)
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m) (hmodd : Odd m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    (hN : NaturalSectionLSL S L m) (hY : HasSym3LiftS S L (L ⊔ S)) :
    InClassXBlock L := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hcenM : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_center_barM_sup_eq_one hA' hLs hSL hm e)
  have hcore : L ⊓ pCoreOf 2 X = L ⊓ pCoreOf 2 (L ⊔ S) :=
    Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL
  have hcenX : Subgroup.center ↥(barM X L) = ⊥ := by
    let E := CFSG.HardMathSupport.Cooperstein.Proving.barMEquiv hL.le (le_sup_left : L ≤ L ⊔ S) hcore
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hEz : E z ∈ Subgroup.center ↥(barM (L ⊔ S) L) := by
      rw [Subgroup.mem_center_iff]
      intro c
      have := Subgroup.mem_center_iff.1 hz (E.symm c)
      have h2 := congrArg E this
      simpa [map_mul] using h2
    rw [hcenM] at hEz
    exact E.injective (by simpa using Subgroup.mem_bot.1 hEz)
  obtain ⟨Y, hSY, hYM, hSyl, hS3, -, y, hyL, hyY, hy, hyQ⟩ := hY
  have hQV := commutator_pCore_le_blockV_of_sym3_lift h84 hX hA hL hcenX hYM hSY hSyl hS3
    hyL hyY hy hyQ
  have hirr := hasIrr_of_naturalSectionL (by omega) hN.naturalSectionL
  have hshort := isShort2_of_hQV_of_center_eq_bot hX hA hL hirr hQV hcenX
  have hAltT := isAltNaturalType_of_natural_section hX hA hL (by omega) e hN hQV hshort
  obtain ⟨k, hk⟩ := hmodd
  exact ⟨hshort, Or.inr ⟨k, by omega, hk ▸ isAltType_of_isAltNaturalType ⟨k, hk⟩ hAltT⟩⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
