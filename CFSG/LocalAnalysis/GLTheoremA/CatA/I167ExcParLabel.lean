module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParBasic
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Types
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Timmesfeld

variable {Ω : Type} [Group Ω] [Finite Ω]


private theorem exc_label_of_catalog_aux1 {S : Type} [Group S] {t : StatedLieTag} {f : ℕ}
    (hmark : CFSG.Assembly.LargeEvenMarking S fun lab _ _ _ _ _ =>
      CFSG.StandardType.markTag lab = t ∧ CFSG.StandardType.markRank lab = 0 ∧
        CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = f)
    (ht : CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcStated t)
    {lab : GLALabel} (hlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = lab)) :
    ∃ labm : GLALabel, CFSG.StandardType.markTag labm = t ∧
      CFSG.StandardType.markDeg labm = f ∧ lab = labm := by
  obtain ⟨labm, ⟨hlt, -, -, hlf⟩, hlabm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K144I.exists_label_of_hasLabel hmark
  have hE : CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcGLATag labm :=
    CFSG.LocalAnalysis.GLTheoremA.K1419E.excGLATag_of_markTag ht hlt
  obtain ⟨hlamm, -, hGlamm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlabm
  obtain ⟨hlam, -, hGlab⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlab
  exact ⟨labm, hlt, hlf, CFSG.LocalAnalysis.GLTheoremA.K1419E.eq_of_ggLabelIso_exc
    (CFSG.StandardType.ggLabelRigidInput_holds labm lab (S ⧸ Subgroup.center S)
      hlamm hlam hGlamm hGlab) hE⟩

private theorem exc_label_of_catalog_aux2 {lab : GLALabel} {t : StatedLieTag} {f : ℕ}
    (hlt : CFSG.StandardType.markTag lab = t) (hdeg : CFSG.StandardType.markDeg lab = f)
    (ht : t = .F4 ∨ t = .twistedE6 ∨ t = .E7 ∨ t = .E8) :
    (lab.tag = .F4 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ lab.n = f := by
  obtain ⟨tg, r, n⟩ := lab
  unfold CFSG.StandardType.markTag at hlt
  unfold CFSG.StandardType.markDeg at hdeg
  rcases ht with rfl | rfl | rfl | rfl
  all_goals
    cases tg <;> simp only at hlt hdeg ⊢ <;> (try split_ifs at hlt hdeg) <;> simp_all

theorem exc_label_of_catalog {p : ℕ} (hp : p.Prime) {X : Subgroup Ω} (hX : CFSG.Open.IsQuasisimple ↥X)
    {kf : DefChar.LieFamily} (hkf : kf = .F4 ∨ kf = .twistedE6 ∨ kf = .E7 ∨ kf = .E8)
    {qc : TauCeti.PrimePower} (hqc : qc.p = 2) {hv : (LocalTwo.excIndex kf qc).Valid}
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex kf qc, hv⟩))
    {lab : GLALabel} (hlab : LabelOf X lab) :
    (lab.tag = .F4 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ lab.n = qc.exponent := by
  rw [Y10F.labelOf_iff_hasLabel] at hlab
  obtain ⟨e⟩ := hcat
  have hnt : Nontrivial (PSimple p X) := exc_pSimple_nontrivial hkf hqc ⟨e⟩
  have hdvd : p ∣ Nat.card X :=
    CFSG.LocalAnalysis.GLTheoremA.T123C.dvd_card_of_nontrivial_pSimple hp hnt
  have hcq : (↥X ⧸ Subgroup.center ↥X) ≃* PSimple p X :=
    CFSG.LocalAnalysis.GLTheoremA.H81Orth.centerQuotEquivPSimple_of_dvd_card hp hX hdvd
  have e2 := hcq.trans e
  rcases hkf with rfl | rfl | rfl | rfl
  · have hm : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .F4 0 2 qc.exponent :=
      hqc ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_F4 qc hv e2
    have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hX.1 hm
    obtain ⟨labm, hlt, hdeg, hlab_eq⟩ :=
      exc_label_of_catalog_aux1 hmark (Or.inr (Or.inl rfl)) hlab
    rw [hlab_eq]
    exact exc_label_of_catalog_aux2 hlt hdeg (Or.inl rfl)
  · have hm : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .twistedE6 0 2 qc.exponent :=
      hqc ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_twistedE6 qc hv e2
    have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hX.1 hm
    obtain ⟨labm, hlt, hdeg, hlab_eq⟩ :=
      exc_label_of_catalog_aux1 hmark
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hlab
    rw [hlab_eq]
    exact exc_label_of_catalog_aux2 hlt hdeg (Or.inr (Or.inl rfl))
  · have hm : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .E7 0 2 qc.exponent :=
      hqc ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E7 qc hv e2
    have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hX.1 hm
    obtain ⟨labm, hlt, hdeg, hlab_eq⟩ :=
      exc_label_of_catalog_aux1 hmark (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hlab
    rw [hlab_eq]
    exact exc_label_of_catalog_aux2 hlt hdeg (Or.inr (Or.inr (Or.inl rfl)))
  · have hm : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .E8 0 2 qc.exponent :=
      hqc ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E8 qc hv e2
    have hmark := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hX.1 hm
    obtain ⟨labm, hlt, hdeg, hlab_eq⟩ :=
      exc_label_of_catalog_aux1 hmark (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hlab
    rw [hlab_eq]
    exact exc_label_of_catalog_aux2 hlt hdeg (Or.inr (Or.inr (Or.inr rfl)))

end CFSG.LocalAnalysis.GLTheoremA.I167

end

