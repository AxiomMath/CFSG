module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Ind
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeIndAutInv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172InnerConj
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms


private theorem fixSubgroup_conj_eq_centralizer {G : Type} [Group G] (x : G) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem fixedCommutingProduct_fixedSubgroup_eq_fixSubgroup {G : Type} [Group G]
    (α : MulAut G) :
    CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := rfl

private theorem congr_centerQuotientHom_eq_indAut_inv {G : Type} [Group G] {p : ℕ}
    {J : Subgroup G} {y : G} (hN : y ∈ Subgroup.normalizer (J : Set G))
    (hw : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut J)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* PSimple p J)
    (he : ∀ l : ↥J, e (QuotientGroup.mk l) = QuotientGroup.mk (QuotientGroup.mk l)) :
    MulAut.congr e (centerQuotientHom ↥J
        (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj y, hw⟩)) =
      (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN)⁻¹ := by
  ext z
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : e.symm (QuotientGroup.mk (QuotientGroup.mk l)) = QuotientGroup.mk l := by
    rw [← he l, MulEquiv.symm_apply_apply]
  set l' : ↥J := ⟨(MulAut.conj y) l,
    CFSG.GroupActions.apply_mem_of_mem_subgroupStabAut hw l.2⟩ with hl'
  have hφ : CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj y, hw⟩ l = l' := rfl
  have hrel : indRel p J y⁻¹ (QuotientGroup.mk l) (QuotientGroup.mk l') := by
    refine ⟨l, l', rfl, rfl, ?_⟩
    show (l' : G) = (y⁻¹)⁻¹ * (l : G) * y⁻¹
    rw [hl']
    simp only [MulAut.conj_apply]
    group
  have hstep := CFSG.LocalAnalysis.GLTheoremA.MI.indAut_apply_mk
    (Subgroup.inv_mem _ hN) hrel
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply]
  rw [h1]
  rw [show centerQuotientHom ↥J
        (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj y, hw⟩)
        (QuotientGroup.mk l) =
      QuotientGroup.mk (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, hw⟩ l) from
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ l]
  rw [he (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj y, hw⟩ l), hφ,
    ← CFSG.LocalAnalysis.GLTheoremA.T171Sh.indAut_inv hN]
  exact hstep.symm

private theorem shapeModelDiagAt_tri {f : ℕ} {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CatLayer) (hdata : TriFieldData f K σ)
    (hcat : catalogIs (TriGrp K σ) (onLie fun d => d.characteristic = 2)) :
    ShapeModelDiagAt (TriGrp K σ) p := by
  intro x y hx1 hxp hyp hxy J hJ hN
  haveI : Finite (TriGrp K σ) := Subtype.finite
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set (TriGrp K σ)) := fixSubgroup_conj_eq_centralizer x
  have hJfix : GLAPComponent p
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) J := by
    rw [hfix]
    exact hJ
  have hperf : ⁅J, J⁆ = J :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJfix
  have hlayer := hL (TriGrp K σ) p hp hp2 hcat x hx1 hxp
  have hle : J ≤ GLALayer
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) :=
    hlayer J hJfix.1 hperf
  have hcompOpen : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
      hJfix hle).1
  have hcomp : CFSG.Assembly.IsComponentOf J
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x)) := by
    rw [fixedCommutingProduct_fixedSubgroup_eq_fixSubgroup]
    exact (CFSG.Assembly.isComponentOf_iff_open).2 hcompOpen
  obtain ⟨t, ν, g, ht, hν, hmodel⟩ :=
    triCompClassical_holds f K σ hdata p hp hp2 x hxp hx1 J hcomp
  have hqOpen : CFSG.Open.IsQuasisimple ↥J := hcompOpen.2.2
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      hp hJfix
  obtain ⟨e, he⟩ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_pSimpleEquivCenterQuot_mk
    hp hqOpen hpJ
  have hmodelP : StatedClassicalModel (PSimple p J) t ν 2 g :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hmodel
  have hLM : CFSG.Blueprint.LieModel (PSimple p J) t ν 2 g :=
    Or.inl ⟨by rcases ht with rfl | rfl <;> decide, hmodelP⟩
  have hw : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
  have hact := triCompAction_holds f K σ hdata p hp hp2 x y hxp hx1 hxy J hcomp hw
  have hmem : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived (PSimple p J) := by
    have hmem' : MulAut.congr e (centerQuotientHom ↥J
        (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj y, hw⟩)) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived (PSimple p J) :=
      (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e).2 hact
    rw [congr_centerQuotientHom_eq_indAut_inv hN hw e he] at hmem'
    exact Subgroup.inv_mem _ hmem'
  have hq : CFSG.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open
      (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJfix)
  exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innDiagOn_of_lieModel hN hq hLM
    (by rintro ⟨h1, -⟩; rcases ht with rfl | rfl <;> exact absurd h1 (by decide))
    (by rcases ht with rfl | rfl <;> decide) hmem

theorem triDiag_of_block (hL : CatLayer) (hC : CatChevComps) (hB : DiagOfBlock)
    (hT : MarkTransport) (hI : ShapeModelDiagIso) :
    SimpleDiagModel (CharTwoOf KD264Lie.isTrialityIdx) := by
  intro S _ _ p hp hp2 hcat hnotshape
  obtain ⟨i, hi, ⟨eCat⟩⟩ := hcat
  have hcat2S : catalogIs S (onLie fun d => d.characteristic = 2) := by
    refine ⟨i, ?_, ⟨eCat⟩⟩
    cases i with
    | lie idx => exact hi.2
    | cyclic _ _ => exact absurd hi (by simp [onLie, CharTwoOf])
    | alternating _ _ => exact absurd hi (by simp [onLie, CharTwoOf])
    | sporadic _ => exact absurd hi (by simp [onLie, CharTwoOf])
  cases i with
  | cyclic _ _ => exact absurd hi (by simp [onLie, CharTwoOf])
  | alternating _ _ => exact absurd hi (by simp [onLie, CharTwoOf])
  | sporadic _ => exact absurd hi (by simp [onLie, CharTwoOf])
  | lie dd =>
    obtain ⟨hiTri, hiChar⟩ := hi
    obtain ⟨val, hv⟩ := dd
    cases val with
    | trialityD4 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_trialityD4]
        exact hiChar
      obtain ⟨K, hKf, hKfin, σ, hK, hσ, -, ⟨eK⟩⟩ :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
      letI := hKf
      letI := hKfin
      have hdata : TriFieldData q.exponent K σ :=
        ⟨q.exponent_pos, by simpa [hq2] using hK, fun c => by simpa [hq2] using hσ c⟩
      have hcatTri : catalogIs (TriGrp K σ) (onLie fun d => d.characteristic = 2) := by
        obtain ⟨j, hj, ⟨eSJ⟩⟩ := hcat2S
        exact ⟨j, hj, ⟨(eCat.trans eK).symm.trans eSJ⟩⟩
      have hshape := shapeModelDiagAt_tri hp hp2 hL hdata hcatTri
      exact (hI hT) (TriGrp K σ) S (eCat.trans eK).symm p hshape
    | _ => exact absurd hiTri (by simp [KD264Lie.isTrialityIdx])

end CFSG.LocalAnalysis.GLTheoremA.F151

end
