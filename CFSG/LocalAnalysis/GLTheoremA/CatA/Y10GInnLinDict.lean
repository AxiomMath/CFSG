module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem largeEvenRawDatumLegacy_of_canonical_carrier {lab : LargeEvenLabel}
    {T : (R : Type) → [Group R] → Prop}
    (h : CFSG.Assembly.LargeEvenRawDatum lab (fun R _ _ _ => T R)) :
    LargeEvenRawDatumLegacy lab (fun R _ _ _ => T R) := by
  obtain ⟨tag, rank, exponent⟩ := lab
  cases tag
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRawDatumLegacy] at h ⊢
  all_goals first
    | exact h
    | (dsimp only [LargeEvenRecipeG2Derived, LargeEvenRecipeChevalley] at h ⊢
       obtain ⟨K, hf, hfin, hK, hQ⟩ := h
       exact ⟨K, hf, hfin, hK, hQ⟩)
    | (dsimp only [LargeEvenRecipeTwF4Inherited, LargeEvenRecipeTwF4] at h ⊢
       obtain ⟨K, hf, hfin, hK, hQ⟩ := h
       exact ⟨K, hf, hfin, hK, hQ⟩)

theorem ggHasLabel_of_hasLabel {J : Type} [Group J] {lab : GLALabel}
    (h : HasLabel J (· = lab)) :
    LargeEvenInLambda2 lab ∧ IsSimpleGroup (J ⧸ Subgroup.center J) ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  obtain ⟨-, lab', hlam, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, -, θ, hθeq⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst lab'
  haveI := hs
  refine ⟨hlam, θ.isSimpleGroup, ?_⟩
  have hraw' : CFSG.Assembly.LargeEvenRawDatum lab
      (fun R' _ _ _ => Nonempty (J ⧸ Subgroup.center J ≃* R')) := by
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R' _ _ _ ⟨-, -, θ', -⟩
    exact ⟨θ'⟩
  exact largeEvenRawDatumLegacy_of_canonical_carrier hraw'

theorem canonLabel_eq_of_ggLabelIso {lab lab' : GLALabel} (h : GGLabelIso lab lab') :
    canonLabel lab = canonLabel lab' := by
  rcases h with h | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · exact congrArg canonLabel h
  · obtain ⟨hB, hB', hr, hn⟩ := hBC
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨t', r', n'⟩ := lab'
    dsimp only at hr hn hB hB'
    subst hr; subst hn
    rcases hB with rfl | rfl <;> rcases hB' with rfl | rfl <;> simp [canonLabel]
  · obtain ⟨h1, h2⟩ := hDA
    rw [h1, h2]
    simp [canonLabel]
  · obtain ⟨h1, h2⟩ := hAD
    rw [h1, h2]
    simp [canonLabel]
  · obtain ⟨h1, h2⟩ := hD3A3
    rw [h1, h2]
    simp [canonLabel]
  · obtain ⟨h1, h2⟩ := hA3D3
    rw [h1, h2]
    simp [canonLabel]
  · obtain ⟨h1, h2⟩ := hD2A1
    rw [h1, h2]
    simp [canonLabel]
  · obtain ⟨h1, h2⟩ := hA1D2
    rw [h1, h2]
    simp [canonLabel]

theorem not_isSimpleGroup_of_card_eq_six {Q : Type*} [Group Q] (hQ : Nat.card Q = 6) :
    ¬ IsSimpleGroup Q := by
  intro hsimple
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have h3dvd : 3 ∣ Nat.card Q := by rw [hQ]; norm_num
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 h3dvd
  set H : Subgroup Q := Subgroup.zpowers g with hHdef
  have hHcard : Nat.card H = 3 := by
    rw [hHdef, Nat.card_zpowers, hg]
  have hHindex : H.index = 2 := by
    have hci := Subgroup.card_mul_index (H := H)
    rw [hHcard, hQ] at hci
    omega
  haveI : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  haveI : IsSimpleGroup Q := hsimple
  rcases Subgroup.Normal.eq_bot_or_eq_top H with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hHcard
    omega
  · rw [htop, Subgroup.card_top, hQ] at hHcard
    omega

theorem card_statedProj_statedSL_two_of_card_eq_two {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 2) : Nat.card (StatedProj (StatedSL 2 E)) = 6 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := E) (n := 2) (by norm_num),
      hE]
  norm_num [Finset.Icc_self]

theorem statedClassicalModel_psl_of_isSimpleGroup {Q : Type} [Group Q] [IsSimpleGroup Q] {a m : ℕ}
    {E : Type} [Field E] [Finite E] (ha : 2 ≤ a) (hE : Nat.card E = 2 ^ m)
    (e : Q ≃* StatedProj (StatedSL a E)) : StatedClassicalModel Q .PSL a 2 m := by
  have hm : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, hm0, pow_zero] at h2
    omega
  have h2m_ne3 : 2 ^ m ≠ 3 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]
    omega
  have hne22 : (a, 2 ^ m) ≠ (2, 2) := by
    intro hpair
    have ha2 : a = 2 := (Prod.mk.inj hpair).1
    have h2m2 : 2 ^ m = 2 := (Prod.mk.inj hpair).2
    have hE2 : Nat.card E = 2 := by rw [hE, h2m2]
    have hcard : Nat.card Q = 6 := by
      rw [Nat.card_congr e.toEquiv, ha2]
      exact card_statedProj_statedSL_two_of_card_eq_two hE2
    exact (not_isSimpleGroup_of_card_eq_six hcard) inferInstance
  have hne23 : (a, 2 ^ m) ≠ (2, 3) := fun hpair => h2m_ne3 (Prod.mk.inj hpair).2
  dsimp only [StatedClassicalModel, StatedLieAdmissible]
  exact ⟨⟨Nat.prime_two, hm, ha, hne22, hne23⟩, E, inferInstance, inferInstance, hE, ⟨e⟩⟩

theorem linLabelDict_of_ggLabelRigidInput (hRig : GGLabelRigidInput) : LinLabelDict := by
  intro J _ _ labJ a m E _ _ ha hE hJ he
  obtain ⟨e⟩ := he
  obtain ⟨hlab, hs, hhas⟩ := ggHasLabel_of_hasLabel hJ
  haveI := hs
  have hM : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL a 2 m :=
    statedClassicalModel_psl_of_isSimpleGroup ha hE e
  have hM' : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL (a - 1 + 1) 2 m := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
    exact hM
  have hiso : GGLabelIso labJ ⟨.A, a - 1, m⟩ :=
    hRig labJ ⟨.A, a - 1, m⟩ (J ⧸ Subgroup.center J) hlab
      (largeEvenInLambda2_typeA hM') hhas (ggHasLabel_typeA hM')
  have hc := canonLabel_eq_of_ggLabelIso hiso
  rwa [show canonLabel (⟨.A, a - 1, m⟩ : GLALabel) = ⟨.A, a - 1, m⟩ from rfl] at hc

theorem linLabelDict_holds :
    LinLabelDict :=
  linLabelDict_of_ggLabelRigidInput ggLabelRigidInput_holds

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
