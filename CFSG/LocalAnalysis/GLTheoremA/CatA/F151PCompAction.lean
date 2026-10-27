module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151ExcDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutRest
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LabHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172InnerConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  glaPComponent_isComponent_of_le_layer)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived Outer
  mem_innAutDerived_congr inner_map_congr)
open scoped commutatorElement

private theorem fixSubgroup_conj_eq_centralizer {R : Type} [Group R] (x : R) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set R) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

private theorem exists_congr_indAut_eq_centerQuotientHom {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hqP : CFSG.Open.IsQuasisimple (PQuot p J)) (hqJ : CFSG.Open.IsQuasisimple ↥J)
    {y : G} (hy : y ∈ Subgroup.normalizer (J : Set G)) :
    ∃ (ι : PSimple p J ≃* (↥J ⧸ Subgroup.center ↥J))
      (hstab : MulAut.conj y⁻¹ ∈ CFSG.GroupActions.subgroupStabAut J),
      MulAut.congr ι (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hy) =
        centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj y⁻¹, hstab⟩) := by
  classical
  have hN' : y⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hy
  have hstab : MulAut.conj y⁻¹ ∈ CFSG.GroupActions.subgroupStabAut J := by
    show J.map (MulAut.conj y⁻¹).toMonoidHom = J
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 hN'
  obtain ⟨ι, hι⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.u9_exists_pSimple_equiv_centerQuot
    hp hqP hqJ (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hqP)
    (MonoidHom.id ↥J) Function.surjective_id
  have hι' : ∀ a : ↥J, ι (chevQuotHom p J a) = QuotientGroup.mk a := fun a => hι a
  refine ⟨ι, hstab, ?_⟩
  ext z
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hsymm : ι.symm (QuotientGroup.mk a) = chevQuotHom p J a := by
    rw [← hι' a, MulEquiv.symm_apply_apply]
  rw [hsymm]
  rw [show CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hy =
      chevAut p J ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ from rfl]
  rw [chevAut_chevQuotHom]
  rw [hι' (J.normalizerMonoidHom ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ a)]
  rw [show centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
      ⟨MulAut.conj y⁻¹, hstab⟩) =
      onCenterQuotient (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y⁻¹, hstab⟩) from rfl]
  rw [show (QuotientGroup.mk a : ↥J ⧸ Subgroup.center ↥J) =
      QuotientGroup.mk' (Subgroup.center ↥J) a from rfl, onCenterQuotient_apply_mk]
  congr 1

theorem diagOfCompAction_holds :
    DiagOfCompAction := by
  intro R _ _ p hp hp2 hlayer hchev hA hD4
  intro x y hx hxp hyp hcomm J hJ hN
  have hfix : fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set R) :=
    fixSubgroup_conj_eq_centralizer x
  have hJfix : J ≤ fixSubgroup (MulAut.conj x) := by
    rw [hfix]
    exact hJ.1
  have hJperf : ⁅J, J⁆ = J :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle : J ≤ GLALayer (fixSubgroup (MulAut.conj x)) :=
    hlayer x hx hxp J hJfix hJperf
  have hJcompFix : GLAPComponent p (fixSubgroup (MulAut.conj x)) J := by
    rw [hfix]
    exact hJ
  obtain ⟨hJcompO, -⟩ := glaPComponent_isComponent_of_le_layer hJcompFix hJle
  have hJcomp : CFSG.Assembly.IsComponentOf J (fixSubgroup (MulAut.conj x)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open J _).2 hJcompO
  have hqOpen : CFSG.Open.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hqNat : CFSG.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open hqOpen
  have hqJ : CFSG.Open.IsQuasisimple ↥J := hJcompO.2.2
  have hchevJ : IsChevSimple 2 (PSimple p J) := hchev x hx hxp J hJ
  have hpOdd : Odd p := hp.odd_of_ne_two hp2
  have hpow : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154_indAut_pow_eq_one hN hyp
  have hconclInner (hmem : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)) :
      InnDiagOn p (Subgroup.zpowers y) J :=
    CFSG.LocalAnalysis.GLTheoremA.MI.inner_innDiag_holds hp hJ hchevJ hN
      ((CFSG.LocalAnalysis.GLTheoremA.MI.indAut_mem_inner_iff hp hJ hN).1 hmem)
  by_cases h360 : Nat.card (PSimple p J) = 360
  · obtain ⟨hsimple, hnab⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hJ
    haveI : IsSimpleGroup (PSimple p J) := hsimple
    exact hconclInner (CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
      (CFSG.LocalAnalysis.GLTheoremA.T171Sh.isPGroup_outer_of_card_360 hnab hchevJ
        h360) hpOdd hpow)
  · have hN' : y⁻¹ ∈ Subgroup.normalizer (J : Set R) := Subgroup.inv_mem _ hN
    obtain ⟨ι, hstab, hbridge⟩ :=
      exists_congr_indAut_eq_centerQuotientHom hp hqOpen hqJ hN
    have hcard' : Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 360 := by
      intro h
      exact h360 (by rw [Nat.card_congr ι.toEquiv]; exact h)
    have hwinv : (y⁻¹) ^ p = 1 := by rw [inv_pow, hyp, inv_one]
    have hcomm' : x * y⁻¹ = y⁻¹ * x := (hcomm.inv_right).eq
    have hcenterMem : centerQuotientHom ↥J
        (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj y⁻¹, hstab⟩) ∈
        innAutDerived (↥J ⧸ Subgroup.center ↥J) :=
      hA x y⁻¹ hx hxp hwinv hcomm' J hJcomp hcard' hstab
    have hmemMI : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ∈
        innAutDerived (PSimple p J) := by
      refine (mem_innAutDerived_congr ι).1 ?_
      rw [hbridge]
      exact hcenterMem
    rcases hchevJ with hon | hamb
    · obtain ⟨i, hi, ⟨e⟩⟩ := hon
      cases i with
      | cyclic _ _ => exact absurd hi (by simp [onLie])
      | alternating _ _ => exact absurd hi (by simp [onLie])
      | sporadic _ => exact absurd hi (by simp [onLie])
      | lie dd =>
        obtain ⟨idx, hv⟩ := dd
        have hval := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        cases idx with
        | A n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_A n q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_linear
            p J y hN hp hqNat
            ⟨.lie ⟨.A n q, hv⟩, ⟨n, q, rfl, hq2⟩, ⟨e⟩⟩ hmemMI
        | twistedA n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedA n q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_unitary
            p J y hN hp hqNat
            ⟨.lie ⟨.twistedA n q, hv⟩, ⟨n, q, rfl, hq2⟩, ⟨e⟩⟩ hmemMI
        | B n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_B n q]; exact hi
          have hr : 2 ≤ n := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat
            ⟨.lie ⟨.B n q, hv⟩, ⟨hr, hq2⟩, ⟨e⟩⟩ hmemMI
        | C n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_C n q]; exact hi
          have hr : 3 ≤ n := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat
            ⟨.lie ⟨.C n q, hv⟩, ⟨by omega, hq2⟩, ⟨e⟩⟩ hmemMI
        | D n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_D n q]; exact hi
          by_cases hn4 : n = 4
          · subst hn4
            have hcatD4 : catalogIs (↥J ⧸ Subgroup.center ↥J)
                (onLie fun i : TauCeti.LieTypeIndex =>
                  ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) :=
              ⟨.lie ⟨.D 4 q, hv⟩, ⟨q, rfl, hq2⟩, ⟨ι.symm.trans e⟩⟩
            have hcenterInner : centerQuotientHom ↥J
                (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj y⁻¹, hstab⟩) ∈
                CFSG.ComponentClassification.OuterAutomorphisms.inner
                  (↥J ⧸ Subgroup.center ↥J) :=
              hD4 x y⁻¹ hx hxp hwinv hcomm' J hJcomp hcatD4 hstab hcenterMem
            have hmemInn : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ∈
                CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J) := by
              refine (Subgroup.mem_map_iff_mem (f := (MulAut.congr ι).toMonoidHom)
                (MulAut.congr ι).injective).1 ?_
              rw [inner_map_congr ι]
              change MulAut.congr ι (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN) ∈
                CFSG.ComponentClassification.OuterAutomorphisms.inner
                  (↥J ⧸ Subgroup.center ↥J)
              rw [hbridge]
              exact hcenterInner
            exact hconclInner hmemInn
          · have hr : 4 ≤ n := by
              have h := hval.1
              simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
              omega
            exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
              p J y hN hp hqNat
              ⟨.lie ⟨.D n q, hv⟩, ⟨by omega, hq2⟩, ⟨e⟩⟩ hmemMI
        | twistedD n q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedD n q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat
            ⟨.lie ⟨.twistedD n q, hv⟩,
              ⟨TauCeti.LieTypeIndex.four_le_of_twistedD_inStandardRange hval.1, hq2⟩,
              ⟨e⟩⟩ hmemMI
        | E6 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E6 q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.E6 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | E7 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E7 q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.E7 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | E8 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_E8 q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.E8 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | F4 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_F4 q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.F4 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | G2 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_G2 q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.G2 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | twistedE6 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_twistedE6 q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.twistedE6 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | trialityD4 q =>
          have hq2 : q.p = 2 := by
            rw [← TauCeti.LieTypeIndex.characteristic_trialityD4 q]; exact hi
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.trialityD4 q, hv⟩, hq2, ⟨e⟩⟩ hmemMI
        | suzuki m =>
          have hr : 1 ≤ m := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.suzuki m, hv⟩, hr, ⟨e⟩⟩ hmemMI
        | reeG2 m =>
          exact absurd (hi.symm.trans (TauCeti.LieTypeIndex.characteristic_reeG2 m))
            (by norm_num)
        | reeF4 m =>
          have hr : 1 ≤ m := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innAutDerivedInnDiag_rest
            p J y hN hp hqNat ⟨.lie ⟨.reeF4 m, hv⟩, hr, ⟨e⟩⟩ hmemMI
        | tits =>
          exact hconclInner (CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
            (CFSG.LocalAnalysis.GLTheoremA.T171Sh.isPGroup_outer_of_tits hv e) hpOdd hpow)
    · exact hconclInner (CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
        (CFSG.LocalAnalysis.GLTheoremA.T171Sh.isPGroup_outer_of_ambiguous_two hamb)
        hpOdd hpow)

end CFSG.LocalAnalysis.GLTheoremA.F151

end
