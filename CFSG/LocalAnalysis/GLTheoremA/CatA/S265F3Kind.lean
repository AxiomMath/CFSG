module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMarking
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel center_centerQuot_eq_bot)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind)

set_option linter.unusedSectionVars false

private theorem induces_quotCenter_iff {S R : Type} [Group S] [Group R] (hcen : Subgroup.center S = ⊥)
    (θ : S ≃* R) (α : MulAut S) (φ : MulAut R) :
    CFSG.Assembly.LargeEvenInduces ((CanonInn.quotCenterEquivOfBot hcen).trans θ)
      (fun s s' => s' = α s) φ ↔ φ = MulAut.congr θ α := by
  constructor
  · intro h
    ext r
    obtain ⟨s, rfl⟩ := θ.surjective r
    have hs := h s (α s) rfl
    simp only [MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk] at hs
    rw [hs, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  · rintro rfl s s' rfl
    simp only [MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk, MulAut.congr_apply,
      MulEquiv.symm_apply_apply]

section Kind


variable {G : Type} [Group G] [Finite G]

theorem fieldKind_of_fieldOn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {g : G}
    (hq : CFSG.Open.IsQuasisimple (PQuot p L)) (hF : FieldOn p g L) :
    ∃ labK : GLALabel, HasLabel (PSimple p L) (· = labK) ∧ ¬ (labK.tag = .triD4 ∧ p = 3) ∧
      FieldKind (PSimple p L) labK (indAut p L g hF.1) := by
  have hcen : Subgroup.center (PSimple p L) = ⊥ := center_centerQuot_eq_bot hq
  haveI : Group.IsPerfect (PQuot p L) := ⟨hq.1⟩
  have hS : commutator (PSimple p L) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p L)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨-, lab, hlam, hraw⟩ := FP.canon_marking_and_labelAll_simple' (P' := FP.DataFacts p)
    (fun lab hlab => FP.canonDataFacts hp hp2 hlab) hF.2
  obtain ⟨_, _, _, _, -, -, -, ⟨hlt, -⟩, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  refine ⟨lab, ⟨hS, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).trans θ, rfl⟩)
    hraw⟩, fun h => hlt.elim (· h.1) (· h.2), hS, lab, hlam,
    CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨-, f, hf, u, hu, hord, hind⟩, ⟨hmul, hinv, -, hfI⟩, hcent, -⟩
  have e1 : u * f * u⁻¹ = MulAut.congr θ (indAut p L g hF.1) := (induces_indRel_iff hF.1 θ).1 hind
  have hc : f * u⁻¹ * f⁻¹ * u ∈ I := by
    have := hcent f u⁻¹ (hinv u hu) 1 (Subgroup.one_mem _)
    simpa using this
  have hn : u * f * u⁻¹ * f⁻¹ ∈ I := by
    have := hmul u hu _ (hmul _ hc _ (hinv u hu))
    have e : u * (f * u⁻¹ * f⁻¹ * u * u⁻¹) = u * f * u⁻¹ * f⁻¹ := by group
    rwa [e] at this
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).trans θ, rfl,
    ⟨_, hn, f, hf, (induces_quotCenter_iff hcen θ _ _).2 ?_⟩, ?_⟩
  · rw [← e1]
    group
  · rintro ⟨i, hi, hind'⟩
    have e2 := (induces_quotCenter_iff hcen θ _ _).1 hind'
    apply hfI f hf hord
    have e3 : f = u⁻¹ * i * u := by rw [e2, ← e1]; group
    rw [e3]
    exact hmul _ (hmul _ (hinv u hu) _ hi) _ hu

end Kind

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
