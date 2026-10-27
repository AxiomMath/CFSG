module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.MarkingSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem ggHasLabel_typeB {X : Type} [Group X] {m k : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 2 ^ k) (e : X ≃* StatedProj (StatedSp m E)) :
    GGHasLabel ⟨.B, m, k⟩ X := by
  refine ⟨E, inferInstance, inferInstance, hE, ?_⟩
  exact ⟨e⟩

theorem ggHasLabel_b2der {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    GGHasLabel ⟨.B2der, 0, 1⟩ X := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  refine ⟨ZMod 2, inferInstance, inferInstance, hK, ?_⟩
  obtain ⟨e₂⟩ := nonempty_b2der_equiv_alternatingGroup (K := ZMod 2) hK
  exact ⟨e.trans e₂.symm⟩

theorem largeEvenInLambda2_typeB {m k : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (h2 : m = 2 → 2 ≤ k) :
    LargeEvenInLambda2 ⟨.B, m, k⟩ :=
  ⟨hk, hm, h2⟩

theorem canonLabel_eq_of_quot_statedSp (hRig : GGLabelRigidInput) {J : Type} [Group J]
    {labJ : GLALabel} {m k : ℕ} {E : Type} [Field E] [Finite E] (hm : 2 ≤ m)
    (hE : Nat.card E = 2 ^ k) (hne : ¬(m = 2 ∧ Nat.card E = 2)) (hJ : HasLabel J (· = labJ))
    (e : J ⧸ Subgroup.center J ≃* StatedProj (StatedSp m E)) :
    canonLabel labJ = ⟨.B, m, k⟩ := by
  obtain ⟨hlab, _, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hJ
  have hk : 1 ≤ k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, hk_eq, pow_zero] at h2
    omega
  have h2 : m = 2 → 2 ≤ k := by
    intro hm2
    by_contra hk2
    have hk1 : k = 1 := by omega
    exact hne ⟨hm2, by rw [hE, hk1, pow_one]⟩
  have hiso : GGLabelIso labJ ⟨.B, m, k⟩ :=
    hRig labJ ⟨.B, m, k⟩ (J ⧸ Subgroup.center J) hlab
      (largeEvenInLambda2_typeB hk hm h2) hhas (ggHasLabel_typeB hE e)
  rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso]
  rfl

theorem canonLabel_eq_of_quot_alternating (hRig : GGLabelRigidInput) {J : Type} [Group J]
    {labJ : GLALabel} (hJ : HasLabel J (· = labJ))
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 6)) :
    canonLabel labJ = ⟨.B, 2, 1⟩ := by
  obtain ⟨hlab, _, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hJ
  have hlam : LargeEvenInLambda2 (⟨.B2der, 0, 1⟩ : LargeEvenLabel) := ⟨le_rfl, rfl, rfl⟩
  have hiso : GGLabelIso labJ ⟨.B2der, 0, 1⟩ :=
    hRig labJ ⟨.B2der, 0, 1⟩ (J ⧸ Subgroup.center J) hlab hlam hhas (ggHasLabel_b2der e)
  rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel

end
