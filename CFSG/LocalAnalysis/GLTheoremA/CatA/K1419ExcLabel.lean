module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144IOutBase
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.Quasithin.Vol2.Ch11SecOE5B

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.HardMathSupport.Dickson.Sec6 (FamG2 FamF4 FamE6 FamE7 FamE8 FamTwE6 FamTriD4 FamReeF4)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.Blueprint (LieModel)

abbrev ExcIdx (d : LieTypeIndex) : Prop :=
  FamG2 d ∨ FamF4 d ∨ FamE6 d ∨ FamE7 d ∨ FamE8 d ∨ FamTwE6 d ∨ FamTriD4 d ∨ FamReeF4 d

abbrev ExcStated (t : StatedLieTag) : Prop :=
  t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4 ∨
    t = .twistedF4

abbrev ExcGLATag (lab : GLALabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
    lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4

section Model


theorem exists_excLieModel {X : Type} [Group X] {d : ValidLieTypeIndex} (hd : ExcIdx d.1)
    (hc : d.1.characteristic = 2) (e : X ≃* (CFSGIndex.lie d).Group) :
    ∃ (t : StatedLieTag) (f : ℕ), ExcStated t ∧ LieModel X t 0 2 f := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | G2 q =>
    have hp : q.p = 2 := (LieTypeIndex.characteristic_G2 q).symm.trans hc
    exact ⟨.G2, q.exponent, Or.inl rfl,
      hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_G2 q hv e⟩
  | F4 q =>
    have hp : q.p = 2 := (LieTypeIndex.characteristic_F4 q).symm.trans hc
    exact ⟨.F4, q.exponent, Or.inr (Or.inl rfl),
      hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_F4 q hv e⟩
  | E6 q =>
    have hp : q.p = 2 := (LieTypeIndex.characteristic_E6 q).symm.trans hc
    exact ⟨.E6, q.exponent, Or.inr (Or.inr (Or.inl rfl)),
      hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E6 q hv e⟩
  | E7 q =>
    have hp : q.p = 2 := (LieTypeIndex.characteristic_E7 q).symm.trans hc
    exact ⟨.E7, q.exponent, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
      hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E7 q hv e⟩
  | E8 q =>
    have hp : q.p = 2 := (LieTypeIndex.characteristic_E8 q).symm.trans hc
    exact ⟨.E8, q.exponent, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E8 q hv e⟩
  | twistedE6 q =>
    have hp : q.p = 2 := (LieTypeIndex.characteristic_twistedE6 q).symm.trans hc
    exact ⟨.twistedE6, q.exponent, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_twistedE6 q hv e⟩
  | trialityD4 q =>
    have hp : q.p = 2 := (LieTypeIndex.characteristic_trialityD4 q).symm.trans hc
    exact ⟨.trialityD4, q.exponent,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
      hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_trialityD4 q hv e⟩
  | reeF4 m =>
    exact ⟨.twistedF4, 2 * m + 1,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))),
      CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_reeF4 m hv e⟩
  | _ => simp [ExcIdx, FamG2, FamF4, FamE6, FamE7, FamE8, FamTwE6, FamTriD4, FamReeF4] at hd

end Model

theorem excGLATag_of_markTag {lab : GLALabel} {t : StatedLieTag} (ht : ExcStated t)
    (h : CFSG.StandardType.markTag lab = t) : ExcGLATag lab := by
  obtain ⟨tg, r, n⟩ := lab
  unfold CFSG.StandardType.markTag at h
  unfold ExcGLATag
  cases tg <;> simp only at h ⊢ <;> (try split_ifs at h) <;> subst h <;> simp [ExcStated] at ht ⊢

theorem eq_of_ggLabelIso_exc {lab lab' : GLALabel} (h : CFSG.StandardType.GGLabelIso lab lab')
    (hE : ExcGLATag lab) : lab' = lab := by
  unfold ExcGLATag at hE
  rcases h with h | ⟨hB, -, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact h.symm
  all_goals exfalso
  · rcases hB with h | h <;> rw [h] at hE <;> simp at hE
  all_goals
    have ht := congrArg (fun l : GLALabel => l.tag) h
    simp only at ht
    rw [ht] at hE
    simp at hE

section Rigid


theorem tag_of_hasLabel_exc (hR : CFSG.StandardType.GGLabelRigidInput) {X : Type} [Group X]
    (hs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) {d : ValidLieTypeIndex}
    (hd : ExcIdx d.1) (hc : d.1.characteristic = 2) (e : X ≃* (CFSGIndex.lie d).Group)
    {labK : GLALabel} (hK : HasLabel X (· = labK)) : ExcGLATag labK := by
  have hcen : Subgroup.center X = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm hs hnab
  have hperf : commutator X = ⊤ := by
    have hq := K144I.openQuasisimple_of_simple hs hnab
    exact hq.1
  obtain ⟨t, f, ht, hm⟩ := exists_excLieModel hd hc
    ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).trans e)
  have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hm
  obtain ⟨lab, ⟨hlt, -, -, -⟩, hlab⟩ := K144I.exists_label_of_hasLabel hmark
  have hE : ExcGLATag lab := excGLATag_of_markTag ht hlt
  obtain ⟨hlam, -, hGlab⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlab
  obtain ⟨hlamK, -, hGlabK⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hK
  have heq := eq_of_ggLabelIso_exc (hR lab labK (X ⧸ Subgroup.center X) hlam hlamK hGlab hGlabK) hE
  rw [heq]
  exact hE

end Rigid

section InnDer


theorem mem_innAutDerived_of_innDiagKind_nd {S : Type} [Group S] [Finite S] {lab : GLALabel}
    {α : MulAut S} (hcen : Subgroup.center S = ⊥)
    (hnd : ¬ CFSG.LocalAnalysis.GLTheoremA.MI.DerivedLab lab)
    (hne : ¬ CFSG.StandardType.GGInndiagCommExclLabel lab)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S lab α) :
    α ∈ innAutDerived S := by
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, -, -, -, hlab, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst lab'
  have hall : CFSG.StandardType.LargeEvenLabelAll lab
      (CFSG.StandardType.LargeEvenSimpleGuard CFSG.StandardType.GGInndiagCommEq) := by
    by_cases hp : CFSG.StandardType.GGInndiagCommProvedLabel lab
    · exact CFSG.StandardType.largeEvenLabelAll_inndiagComm_proved hlam hp
    · exact CFSG.StandardType.ggInndiagCommRestInput_holds lab hlam hne hp
  have h2 := (CFSG.LocalAnalysis.GLTheoremA.MI.canonAll_iff_legacyAll hlam hnd _).2 hall _ hraw
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, u, hu, hind⟩, hEq⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists h2
  have hu' : u ∈ CFSG.StandardType.ggInndiagComm R := by
    rw [← hEq hs hna]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure hu)
  let e : S ≃* R := (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans θ
  have he : ∀ s, e s = θ (QuotientGroup.mk s) := fun s => by
    show θ ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm s) = _
    congr 1
    rw [MulEquiv.symm_apply_eq, CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk]
  have hconj : MulAut.congr e α = u := by
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    show e (α (e.symm (e s))) = u (e s)
    rw [MulEquiv.symm_apply_apply, he, he]
    exact (hind s (α s) rfl).symm
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e, hconj]
  exact hu'

end InnDer

theorem not_derived_not_excl_of_excGLATag {lab : GLALabel} (h : ExcGLATag lab) :
    ¬ CFSG.LocalAnalysis.GLTheoremA.MI.DerivedLab lab ∧
      ¬ CFSG.StandardType.GGInndiagCommExclLabel lab := by
  rcases h with h | h | h | h | h | h | h | h <;>
    simp [CFSG.LocalAnalysis.GLTheoremA.MI.DerivedLab, CFSG.StandardType.GGInndiagCommExclLabel, h]

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
