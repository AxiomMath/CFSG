module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrthKind
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCanon
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.StandardType

theorem innDiagKind_or_fieldKind_of_guard {S : Type} [Group S] {p : ℕ} {α : MulAut S}
    {labK : GLALabel} (hlab : HasLabel S (fun l : GLALabel => l = labK)) (hα : α ^ p = 1)
    (hP : CFSG.StandardType.Canonical.LargeEvenLabelAll labK
      (LargeEvenSimpleGuard (Y10GClsOrth.RawOddInnField p))) :
    InnDiagKind S labK α ∨ FieldKind S labK α := by
  have h1 : CFSG.Assembly.LargeEvenMarking S fun lab R _ I F _ =>
      lab = labK ∧ Y10GClsOrth.RawOddInnField p R I F := by
    obtain ⟨hS, lab, hlabΛ, hraw⟩ := hlab
    obtain ⟨R, _, I, F, -, -, θ, hEq⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    have hEq' : lab = labK := hEq
    subst hEq'
    refine ⟨hS, lab, hlabΛ,
      CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ (hP _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hodd⟩
    exact ⟨hs, hna, θ, rfl, hodd hs hna⟩
  refine Y10GClsOrth.CLB.largeEvenMarking_or
    (CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ h1)
  rintro lab R _ I F θ ⟨rfl, hodd⟩
  exact (Y10GClsOrth.CLB.induces_inn_or_field θ hα hodd).imp
    (fun h => ⟨rfl, h⟩) fun h => ⟨rfl, h⟩

section Certificates


theorem clsExc_of_fieldClosed
    (hcl : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → FamExc lab →
      CFSG.StandardType.Canonical.LargeEvenLabelAll lab
        (fun R _ _ F => ∀ f ∈ Subgroup.closure F, f ∈ F)) :
    ClsExc := by
  intro S _ _ p α labK hfam hp hp2 _ hlab hα
  have hΛ : LargeEvenInLambda2 labK := by
    obtain ⟨-, lab, hl, _, _, _, _, _, -, -, hEq⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_exists hlab
    exact (show lab = labK from hEq) ▸ hl
  have hDtag : labK.tag ≠ .D := by
    intro h
    unfold FamExc at hfam
    rcases hfam with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
      rw [h] at h' <;> cases h'
  have hD : ¬ (labK.tag = .D ∧ labK.rank = 4 ∧ p = 3) := fun h => hDtag h.1
  refine innDiagKind_or_fieldKind_of_guard hlab hα ?_
  refine MI.CAll.mono ?_
    (MI.CAll.and (hcl labK hΛ hfam) (FP.canonOddAut hp hp2 hΛ hD))
  rintro R _ I F ⟨hF, hodd⟩ hs hna φ hφ
  obtain ⟨u, hu, f, hf, rfl⟩ := hodd hs hna φ hφ
  exact Or.inr ⟨u, hu, f, hF f hf, rfl⟩

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc
