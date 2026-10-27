module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutRest
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172InnerConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShSetupE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)


variable {G : Type} [Group G] [Finite G]

section Certs


theorem not_fgOn_of_isTD4 {J : Subgroup G} {b : G} (h : IsTD4 3 J) : ¬ FGOn 3 b J := by
  rintro (hF | ⟨-, hT, -⟩)
  · exact MI.td4_not_field_holds h hF
  · exact hT ⟨rfl, h⟩

theorem not_fgOn_of_innDiagOn {X J : Subgroup G} {b : G} (hJ : GLAPComponent 3 X J)
    (h : InnDiagOn 3 (Subgroup.zpowers b) J) : ¬ FGOn 3 b J := by
  rintro (hF | ⟨hNI, -, -⟩)
  · exact (MI.field_nonInnDiag_any hJ hF).2 h
  · exact hNI.2 h


theorem not_fgOn_of_innAutDerived (hD4 : D4InnAutDerivedNotFG) {X J : Subgroup G} {b : G}
    (hJ : GLAPComponent 3 X J) (hchev : IsChevSimple 2 (PSimple 3 J)) (hb3 : b ^ 3 = 1)
    (hbN : b ∈ Subgroup.normalizer (J : Set G))
    (hMI : MI.indAut 3 J b hbN ∈ innAutDerived (PSimple 3 J) ∨ Nat.card (PSimple 3 J) = 360) :
    ¬ FGOn 3 b J := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hpOdd : Odd 3 := by decide
  have hpow : MI.indAut 3 J b hbN ^ 3 = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154_indAut_pow_eq_one hbN hb3
  have hqJ : CFSG.IsQuasisimple (PQuot 3 J) :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open (isQuasisimple_pQuot_of_glaPComponent hp hJ)
  have hinner : MI.indAut 3 J b hbN ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 J) →
      ¬ FGOn 3 b J := fun h =>
    not_fgOn_of_innDiagOn hJ
      (MI.inner_innDiag_any hJ hchev hbN ((MI.indAut_mem_inner_iff hp hJ hbN).1 h))
  by_cases h360 : Nat.card (PSimple 3 J) = 360
  · obtain ⟨hsimple, hnab⟩ := chev_pSimple_simple_nonabelian hp hJ
    haveI := hsimple
    exact hinner (CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
      (T171Sh.isPGroup_outer_of_card_360 hnab hchev h360) hpOdd hpow)
  have hmem : MI.indAut 3 J b hbN ∈ innAutDerived (PSimple 3 J) := hMI.resolve_right h360
  rcases hchev with hon | hamb
  · obtain ⟨i, hi, ⟨e⟩⟩ := hon
    cases i with
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
    | lie dd =>
      obtain ⟨idx, hv⟩ := dd
      have hval := (TauCeti.LieTypeIndex.valid_iff _).1 hv
      have hrest : ∀ (hR : T171Sh.RestIndex idx), ¬ FGOn 3 b J := fun hR =>
        not_fgOn_of_innDiagOn hJ (T171Sh.innAutDerivedInnDiag_rest 3 J b hbN hp hqJ
          ⟨.lie ⟨idx, hv⟩, hR, ⟨e⟩⟩ hmem)
      cases idx with
      | A n q =>
        have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_A n q]; exact hi
        exact not_fgOn_of_innDiagOn hJ (T171Sh.innAutDerivedInnDiag_linear 3 J b hbN hp hqJ
          ⟨.lie ⟨.A n q, hv⟩, ⟨n, q, rfl, hq2⟩, ⟨e⟩⟩ hmem)
      | twistedA n q =>
        have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_twistedA n q]; exact hi
        exact not_fgOn_of_innDiagOn hJ (T171Sh.innAutDerivedInnDiag_unitary 3 J b hbN hp hqJ
          ⟨.lie ⟨.twistedA n q, hv⟩, ⟨n, q, rfl, hq2⟩, ⟨e⟩⟩ hmem)
      | D n q =>
        have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_D n q]; exact hi
        by_cases hn4 : n = 4
        · subst hn4
          exact hD4 G X J b hJ ⟨.lie ⟨.D 4 q, hv⟩, ⟨q, rfl, hq2⟩, ⟨e⟩⟩ hb3 hbN hmem
        · have hr : 4 ≤ n := by
            have h := hval.1
            simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
            omega
          exact hrest ⟨by omega, hq2⟩
      | tits =>
        exact hinner (CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
          (T171Sh.isPGroup_outer_of_tits hv e) hpOdd hpow)
      | reeG2 m =>
        exact absurd (hi.symm.trans (TauCeti.LieTypeIndex.characteristic_reeG2 m)) (by norm_num)
      | B n q =>
        have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_B n q]; exact hi
        have hr : 2 ≤ n := by
          have h := hval.1
          simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
          omega
        exact hrest ⟨hr, hq2⟩
      | C n q =>
        have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_C n q]; exact hi
        have hr : 3 ≤ n := by
          have h := hval.1
          simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
          omega
        exact hrest ⟨by omega, hq2⟩
      | twistedD n q =>
        have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_twistedD n q]; exact hi
        exact hrest ⟨TauCeti.LieTypeIndex.four_le_of_twistedD_inStandardRange hval.1, hq2⟩
      | G2 q =>
        exact hrest (show q.p = 2 by rw [← TauCeti.LieTypeIndex.characteristic_G2]; exact hi)
      | F4 q =>
        exact hrest (show q.p = 2 by rw [← TauCeti.LieTypeIndex.characteristic_F4]; exact hi)
      | E6 q =>
        exact hrest (show q.p = 2 by rw [← TauCeti.LieTypeIndex.characteristic_E6]; exact hi)
      | E7 q =>
        exact hrest (show q.p = 2 by rw [← TauCeti.LieTypeIndex.characteristic_E7]; exact hi)
      | E8 q =>
        exact hrest (show q.p = 2 by rw [← TauCeti.LieTypeIndex.characteristic_E8]; exact hi)
      | twistedE6 q =>
        exact hrest (show q.p = 2 by rw [← TauCeti.LieTypeIndex.characteristic_twistedE6]; exact hi)
      | trialityD4 q =>
        exact hrest (show q.p = 2 by rw [← TauCeti.LieTypeIndex.characteristic_trialityD4]; exact hi)
      | suzuki m =>
        have hr : 1 ≤ m := by
          have h := hval.1
          simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
          omega
        exact hrest hr
      | reeF4 m =>
        have hr : 1 ≤ m := by
          have h := hval.1
          simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
          omega
        exact hrest hr
  · exact hinner (CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer
      (T171Sh.isPGroup_outer_of_ambiguous_two hamb) hpOdd hpow)

theorem t158CompE6_of (hData : T158E6LangData) (hK : T171Sh.ExcKernelCompAction)
    (hD4 : D4InnAutDerivedNotFG) (hShort : E6ShortOrbit) (hU : E6OrbitThreeUnique)
    (hO : E6A2OrbitThreeOuter) (hR2 : E6D4T2CosetAction) : T158CompE6 := by
  intro G _ _ L J A d b hP hcat
  obtain ⟨Lf, _, _, _, S, a, i, y, hyStab, hshape, hT, hap, h1, hqs, hyC, hyF, ⟨e⟩, hInn, hComp, hOut⟩ :=
    hData G L J A d b hP hcat
  have hb3 : b ^ 3 = 1 := hP.elem.2 b hP.b_mem
  have hFG : FGOn 3 b J := hP.fg
  by_cases hyM : y ∈ torusGroup Tag.E6 Lf ⊔ rootSpan Tag.E6 Lf (kernelRoots (rootCharHom a))
  ·
    exfalso
    by_cases h360 : Nat.card (PSimple 3 J) = 360
    · exact not_fgOn_of_innAutDerived hD4 hP.pcomp hP.chevJ hb3 hP.b_norm (Or.inr h360) hFG
    · have hR360 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 360 := fun h =>
        h360 ((Nat.card_congr e.toEquiv).trans h)
      have hmain := hK (τ := Tag.E6) (L := Lf) S Nat.prime_five (by norm_num) Nat.prime_three (by norm_num)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hT hap
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap) h1
        (fun h => by cases h) i hqs hR360 hyM hyF hyStab
      exact not_fgOn_of_innAutDerived hD4 hP.pcomp hP.chevJ hb3 hP.b_norm (Or.inl (hInn hmain)) hFG
  · rcases hShort Lf 5 S a hT hap h1 i hqs y hyC hyF hyStab hyM with ⟨h18, h3⟩ | h24
    ·
      exact ⟨hComp fun j _ => hU Lf 5 S a hT hap h18 i h3 j, hOut (hO Lf 5 S hshape a hT hap h18 i h3)⟩
    ·
      exfalso
      rcases hR2 Lf 5 S hshape a hT hap h24 i hqs y hyC hyF hyStab hyM with htd | hmem
      · exact not_fgOn_of_isTD4 ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr e).2 htd) hFG
      · exact not_fgOn_of_innAutDerived hD4 hP.pcomp hP.chevJ hb3 hP.b_norm (Or.inl (hInn hmem)) hFG

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T158

end
