module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3Unpack
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExc
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSymp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Timmesfeld

section Certs


theorem exc_label_of_lieModel {p : ℕ} {G : Type} [Group G] [Finite G]
    {Y J' : Subgroup G} (hp : p.Prime) (hJcomp : GLAPComponent p Y J')
    (hq : CFSG.Open.IsQuasisimple ↥J')
    {t : StatedLieTag} {n k : ℕ} (hm : CFSG.Blueprint.LieModel (PSimple p J') t n 2 k) :
    ∃ labJ : GLALabel, Y10F.HasLabel ↥J' (· = labJ) ∧ (canonLabel labJ).n = k := by
  obtain ⟨ePZ⟩ := I141F.centerQuot_equiv_pSimple hp hJcomp hq
  have hb : CFSG.Blueprint.LieModel (↥J' ⧸ Subgroup.center ↥J') t n 2 k := hm.of_mulEquiv ePZ.symm
  have hperf : commutator ↥J' = ⊤ := by
    apply Subgroup.map_injective J'.subtype_injective
    rw [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact glaPComponent_perfect hJcomp
  obtain ⟨hperf', lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hb
  obtain ⟨R, _, I, F, -, -, -, _, _, hch, hdf⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  refine ⟨lab, ⟨hperf, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩, ?_⟩
  rw [CanonSubcomp.canonLabel_n_eq_markDeg hlab hch, hdf]

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exc_transfer_isQuasisimple {p : ℕ} {X J : Subgroup Ω} {x : Ω}
    (hp : p.Prime) (hp2 : p ≠ 2) (hsimple : IsSimpleGroup (PSimple p X))
    (hna : ∃ a b : PSimple p X, a * b ≠ b * a) {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1.characteristic = 2) (e : PSimple p X ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hN : x ∈ Subgroup.normalizer (X : Set Ω)) (hxp : x ^ p = 1)
    (hne : chevAut p X ⟨x, hN⟩ ≠ 1) (hJ : GLAPComponent p (X ⊓ cx x) J) :
    CFSG.Open.IsQuasisimple ↥(chevTransfer p X J) := by
  have hxp' : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hxp
  have hJ' := glaPComponent_chevTransfer hp hN hxp' hJ
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
    (PSimple p X) hsimple hna d ⟨e⟩ p hp hp2
    (fun h : p = d.1.characteristic => hp2 (h.trans hd))
    (chevAut p X ⟨x, hN⟩) (chevAut_pow_eq_one p X hN hxp) hne
  have hJle := hpil (chevTransfer p X J) hJ'.1 (glaPComponent_perfect hJ')
  exact (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ' hJle).1.2.2

theorem exc_fieldRel_of_lieModel {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x)
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1.characteristic = 2)
    (eE : PSimple p X ≃* (TauCeti.CFSGIndex.lie d).Group)
    {t : StatedLieTag} {n k : ℕ} (hm : CFSG.Blueprint.LieModel (PSimple p J) t n 2 k) :
    ∃ e : ℕ, 2 ^ e = KD264Lie.fieldSize d.1 ∧ e ∣ k := by
  have hq : CFSG.Open.IsQuasisimple (PQuot p X) := exc3_isQuasisimple_pQuot H
  have hcen : Subgroup.center (PSimple p X) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  have hyN := H.hxN
  have hap : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one H.hxp
  have hJx := exc3_glaPComponent_cx H
  have hJ' := glaPComponent_chevTransfer H.hp hyN hap hJx
  obtain ⟨labK, -, hinK⟩ := I141F.innDiagKind_chevAut hyN hq H.hinn
  have hKlabel : Y10F.HasLabel (PSimple p X) (· = labK) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hinK
  have hne : chevAut p X ⟨x, hyN⟩ ≠ 1 := fun h1 =>
    exc3_not_centMod H ((I141F.chevAut_eq_one_iff_of_quasisimple hq hyN).1 h1)
  have hJ'q := exc_transfer_isQuasisimple H.hp H.hp2 hq.2
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq) hd eE hyN
    H.hxp hne hJx
  obtain ⟨eP⟩ := nonempty_pSimple_equiv_chevTransfer H.hp hyN hap hJx
  obtain ⟨labJ, hlabJ, hJn⟩ := exc_label_of_lieModel H.hp hJ' hJ'q (hm.of_mulEquiv eP)
  have hdvd := Y10GField.inn_of_families
    (Y10GInnLin.innDiagLin_of_labelDict Y10GInnLin.linLabelDict_holds)
    Y10GInnUni.innDiagUni_holds Y10GField.innDiagSymp_holds Y10GField.innDiagOrth_holds
    Y10GField.innDiagExc_holds (PSimple p X) p (chevAut p X ⟨x, hyN⟩) (chevTransfer p X J) labK
    labJ H.hp H.hp2 hcen hinK (chevAut_pow_eq_one p X hyN H.hxp) hlabJ hJ'
  have hφ : (PSimple p X) ⧸ Subgroup.center (PSimple p X) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    (CanonInn.quotCenterEquivOfBot hcen).trans eE
  have h2n := CanonSubcomp.two_pow_canonLabel_n_of_lie
    CFSG.StandardType.ggLabelRigidInput_holds hKlabel d hd hφ
  rw [hJn] at hdvd
  exact ⟨_, h2n, hdvd⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I167

end
