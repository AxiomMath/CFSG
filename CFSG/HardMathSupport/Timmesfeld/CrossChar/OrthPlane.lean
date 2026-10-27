module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthDerived
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthSpecial
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthSplitFour
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityData
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneModel
public import CFSG.LieType.SeitzGeneration.OrthThree
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SeitzGeneration.OrthLift
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical

section Helpers

theorem conj_injective_of_center_eq_bot_orth {G : Type*} [Group G]
    (h : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hcen : c ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun y => by
    have h1 := congrArg (fun φ : MulAut G => φ y) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * c = c * y * c⁻¹ * c := by rw [h1]
      _ = c * y := by group
  rw [h] at hcen
  exact hcen

theorem orderOf_map_eq_of_coprime_ker_orth {G G' : Type*} [Group G] [Group G'] [Finite G]
    (f : G →* G') {p : ℕ} (hp : p.Prime) (hker : Nat.Coprime (Nat.card f.ker) p) {y : G}
    (hy : orderOf y = p) : orderOf (f y) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : f y ^ p = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  refine orderOf_eq_prime h1 fun h2 => ?_
  have hdvd : p ∣ Nat.card f.ker := hy ▸ Subgroup.orderOf_dvd_natCard f.ker h2
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hker.symm hdvd)

theorem not_coprime_card_of_orderOf_orth {G : Type*} [Group G] [Finite G] {S : Subgroup G} {p : ℕ}
    (hp : p.Prime) {y : G} (hyS : y ∈ S) (hy : orderOf y = p) : ¬ Nat.Coprime p (Nat.card S) :=
  fun hc => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc (hy ▸ Subgroup.orderOf_dvd_natCard S hyS))

theorem pow_eq_one_of_mem_iSup_commute_orth {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (C : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y) {n : ℕ}
    (hn : ∀ i, ∀ c ∈ C i, c ^ n = 1) {y : G} (hy : y ∈ ⨆ i, C i) : y ^ n = 1 := by
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)] at hy
  obtain ⟨f, rfl⟩ := hy
  rw [← map_pow]
  have hf : f ^ n = 1 := funext fun i => Subtype.ext (by simpa using hn i (f i) (f i).2)
  rw [hf, map_one]

end Helpers

section Local

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem nontrivial_of_totallySingular_orth
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) : Nontrivial V := by
  obtain ⟨U, hU3, -⟩ := hT
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := Module.finrank_zero_of_subsingleton (R := K) (M := ↥U)
  omega

theorem orderOf_mk_projOrth (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {y : orthDerived Q} (hy : orderOf y = p) :
    orderOf (QuotientGroup.mk y : ProjOrthDerived Q) = p := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, hZ, -⟩ := orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  refine orderOf_map_eq_of_coprime_ker_orth
    (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
      (orthDerived Q))) hp ?_ hy
  rw [QuotientGroup.ker_mk']
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hpos : 0 < Nat.card ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
      (orthDerived Q)) := Nat.card_pos
  have := Nat.le_of_dvd hpos hdvd
  omega

variable (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
  (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
  {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)

include hQ hT hp hp3 hpl in
theorem orthComponentImage_le_fixSub (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn p H E)
    (x : orthDerived Q) (hxp : orderOf x = p)
    (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    (Rep : Finset K[X]) (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep)
    (h : K[X]) (hh : h ∈ Rep) (hne : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) :
    componentImage Q (x : V ≃ₗ[K] V) h ≤ fixSub g := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha := orderOf_mk_projOrth hQ hT hp hp3 hxp
  obtain ⟨-, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl H hH _ ha x rfl hxp
  obtain ⟨-, -, -, -, -, hspec, -, -⟩ := hmain Rep hRep
  obtain ⟨hΩ, -, -, -, hle, -, hcomp⟩ := hspec h hh hne hm
  have hdvd := dvd_card_orthSpecialBlock hx hp hp3 (hRep.1 hh) hne hm
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set s' : orthDerived Q := ⟨(s : V ≃ₗ[K] V), hΩ s.2⟩ with hs'
  have hs'p : orderOf s' = p := by
    rw [← hs, ← Subgroup.orderOf_coe s, ← Subgroup.orderOf_coe s']
  have hρ := orderOf_mk_projOrth hQ hT hp hp3 hs'p
  have hmem : (QuotientGroup.mk s' : ProjOrthDerived Q) ∈ componentImage Q (x : V ≃ₗ[K] V) h :=
    ⟨s', Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
  have ha1 : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ha
    exact hp.one_lt.ne' ha.symm
  refine le_fixSub_of_component hp hinj hg he (fun h1 => ha1 (hinj (by rw [h1, map_one])))
    ?_ hcomp (not_coprime_card_of_orderOf_orth hp hmem hρ)
  rintro _ ⟨t, ht, rfl⟩
  refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hle ht)]

include hQ hT hp hp3 hpl in
theorem orthFixedComponentImage_le_fixSub (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn p H E)
    (x : orthDerived Q) (hxp : orderOf x = p)
    (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    {w : V ≃ₗ[K] V} (hw : w ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1)) (hwp : w ^ p = 1)
    (hw1 : w ≠ 1) (h3 : 3 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V))) :
    fixedComponentImage Q (x : V ≃ₗ[K] V) ≤ fixSub g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha := orderOf_mk_projOrth hQ hT hp hp3 hxp
  have ha1 : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ha
    exact hp.one_lt.ne' ha.symm
  have he1 : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 :=
    fun h1 => ha1 (hinj (by rw [h1, map_one]))
  have hx1 : (x : V ≃ₗ[K] V) ≠ 1 := fun h1 => ha1 (by
    have : x = 1 := Subtype.ext h1
    rw [this, QuotientGroup.mk_one])
  set gW : ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)) :=
    ⟨restrictFixed Q (x : V ≃ₗ[K] V) ⟨w, hw⟩, restrictFixed_mem_orthogonalGroup _⟩ with hgW
  have hgWp : orderOf gW = p := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      change restrictFixed Q (x : V ≃ₗ[K] V) ⟨w, hw⟩ ^ p = 1
      rw [← map_pow]
      have : (⟨w, hw⟩ : ↥(supportedBlock Q (x : V ≃ₗ[K] V) (X - 1))) ^ p = 1 := Subtype.ext hwp
      rw [this, map_one]
    · intro h1
      have h2 : restrictFixed Q (x : V ≃ₗ[K] V) ⟨w, hw⟩ = 1 := congrArg Subtype.val h1
      exact hw1 (hx.eq_one_of_restrictFixed_eq_one hw h2)
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hlist : FixedLayerListed Q (x : V ≃ₗ[K] V) :=
    ⟨h3, fun hsmall => (orthogonal_regular_space_coverage _ hQW h3).1 hsmall gW p hp hp3 hgWp⟩
  obtain ⟨-, -, -, -, -, -, -, hmemS⟩ := hx.fixedLayer_data hlist
  have hwS : w ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V) := hmemS w hw p hp hp3 hwp
  have hwΩ := hx.supportedFixedDerived_le_orthDerived hwS
  set w' : orthDerived Q := ⟨w, hwΩ⟩ with hw'
  have hw'p : orderOf w' = p := orderOf_eq_prime (Subtype.ext hwp)
    (fun h1 => hw1 (congrArg Subtype.val h1))
  have hρw := orderOf_mk_projOrth hQ hT hp hp3 hw'p
  have hmemF : (QuotientGroup.mk w' : ProjOrthDerived Q) ∈
      fixedComponentImage Q (x : V ≃ₗ[K] V) :=
    ⟨w', Subgroup.mem_subgroupOf.mpr hwS, rfl⟩
  have hTC : ∀ S : Subgroup (ProjOrthDerived Q),
      S ≤ Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q)) →
      S.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
        H ⊓ Subgroup.centralizer ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q))) := by
    intro S hS
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hS ht)]
  by_cases hs4 : finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
      ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
        ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0
  ·
    have hq : 3 < Nat.card K := by
      by_contra hq
      have hq2 : 1 < Nat.card K := Finite.one_lt_card
      exact hlist.2 (Or.inr ⟨hs4, by omega⟩)
    obtain ⟨ψ, e, -, -, hsup, hC, hcomm⟩ := orthogonal_inner_plane_split_four_factors hQ hT hp hp3
      hpl H hH _ ha1 x rfl hxp hs4.1 hs4.2 hq
    rw [fixedLayerImage_of_listed hlist] at hsup
    set C : Fin 2 → Subgroup (ProjOrthDerived Q) := fun i =>
      fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp) (splitFourFactors e i)
      with hCdef
    have hcard : ∀ i, Nat.card (C i) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      fun i => card_fixedFactorImage_splitFourFactors _ hx1 e i (hC i).1
    have hpair : Pairwise fun i j : Fin 2 => ∀ u v : ProjOrthDerived Q, u ∈ C i → v ∈ C j →
        Commute u v := by
      intro i j hij u v hu hv
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hcomm u hu v hv
      · exact (hcomm v hv u hu).symm
      · exact absurd rfl hij
    have hpow : ∀ i, ∀ c ∈ C i, c ^ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
      intro i c hc
      rw [← hcard i]
      have := pow_card_eq_one' (G := C i) (x := ⟨c, hc⟩)
      exact congrArg Subtype.val this
    have hdvd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [← hρw]
      refine orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_iSup_commute_orth C hpair hpow ?_)
      rw [hsup]
      exact hmemF
    rw [← hsup]
    refine iSup_le fun i => ?_
    obtain ⟨-, -, -, hle, -, hcomp⟩ := hC i
    refine le_fixSub_of_component hp hinj hg he he1 (hTC _ hle) hcomp fun hc => ?_
    rw [hcard i] at hc
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hdvd)
  · obtain ⟨-, -, hle, -, hcomp⟩ := orthogonal_inner_plane_unsplit_fixed_layer hQ hT hp hp3 hpl
      H hH _ ha1 x rfl hxp hlist hs4
    exact le_fixSub_of_component hp hinj hg he he1 (hTC _ hle) hcomp
      (not_coprime_card_of_orderOf_orth hp hmemF hρw)

end Local

section Fixed

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

theorem orth_exists_supported_of_moves {x z : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hz : z ∈ isometryCentralizer Q x) (hzp : z ^ p = 1) {v : V} (hv : v ∈ fixedSpace x)
    (hzv : z v ≠ v) :
    ∃ w ∈ supportedBlock Q x (X - 1), w ^ p = 1 ∧ w ≠ 1 := by
  set φ := isometryRestrictFixed Q x ⟨z, hz⟩ with hφ
  obtain ⟨w, hw⟩ := restrictFixed_surjective hx φ (isometryRestrictFixed_mem_orthogonalGroup _)
  refine ⟨w.1, w.2, ?_, ?_⟩
  · have h1 : restrictFixed Q x (w ^ p) = 1 := by
      rw [map_pow, hw, hφ, ← map_pow]
      have : (⟨z, hz⟩ : ↥(isometryCentralizer Q x)) ^ p = 1 := Subtype.ext hzp
      rw [this, map_one]
    have h2 : w ^ p = 1 := restrictFixed_injective hx (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  · intro h1
    have h2 : w = 1 := Subtype.ext h1
    apply hzv
    have h3 := congrArg (fun ψ : fixedSpace x ≃ₗ[K] fixedSpace x => (ψ ⟨v, hv⟩ : V)) hw
    simp only [h2, map_one] at h3
    rw [hφ, coe_isometryRestrictFixed] at h3
    exact h3.symm

theorem orthSupportedBlock_X_sub_one_le {x y : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hy : OddOrderIsometry Q p y) (hxy : fixedSpace x ≤ fixedSpace y) :
    supportedBlock Q x (X - 1) ≤ supportedBlock Q y (X - 1) := by
  intro g hg
  obtain ⟨hgM, hgfix⟩ := mem_supportedBlock.mp hg
  obtain ⟨hgO, -⟩ := mem_isometryCentralizer.mp hgM
  obtain ⟨hcx, horthx⟩ := hx.fixed_others
  obtain ⟨-, horthy⟩ := hy.fixed_others
  have hoth : ∀ r ∈ othersSpace y.toLinearMap (X - 1), r ∈ othersSpace x.toLinearMap (X - 1) := by
    intro r hr
    refine hx.perp_fixed_le_others fun u hu => ?_
    rw [QuadraticMap.polar_comm]
    exact horthy u (hxy hu) r hr
  have hyW : ∀ u ∈ fixedSpace x, y u = u := fun u hu => mem_fixedSpace.mp (hxy hu)
  have hyR : ∀ r ∈ othersSpace x.toLinearMap (X - 1), y r ∈ othersSpace x.toLinearMap (X - 1) := by
    intro r hr
    refine hx.perp_fixed_le_others fun u hu => ?_
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hy.mem r u
    rw [hyW u hu] at h1
    rw [h1, QuadraticMap.polar_comm]
    exact horthx u hu r hr
  refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨hgO, fun v => ?_⟩,
    fun r hr => hgfix r (hoth r hr)⟩
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl hcx v
  have hgu : g u ∈ fixedSpace x :=
    mem_fixedSpace_of_apply (Subgroup.mem_inf.mp hgM).2 hu
  rw [map_add, map_add, map_add, map_add, hyW u hu, hyW (g u) hgu, hgfix r hr,
    hgfix (y r) (hyR r hr)]

theorem orthFixedComponentImage_mono {x y : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hy : OddOrderIsometry Q p y) (hxy : fixedSpace x ≤ fixedSpace y) :
    fixedComponentImage Q x ≤ fixedComponentImage Q y := by
  unfold fixedComponentImage
  refine Subgroup.map_mono fun g hg => ?_
  rw [Subgroup.mem_subgroupOf] at hg ⊢
  rw [hx.supportedFixedDerived_eq] at hg
  rw [hy.supportedFixedDerived_eq]
  exact Subgroup.commutator_mono (orthSupportedBlock_X_sub_one_le hx hy hxy)
    (orthSupportedBlock_X_sub_one_le hx hy hxy) hg

end Fixed

theorem layer_le_commutator_top_orth (G : Type*) [Group G] :
    CFSG.layer G ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := by
  refine sSup_le fun L hL => ?_
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  rw [← hperf]
  exact Subgroup.commutator_mono le_top le_top

section Main

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.RankThree.PartOne.KCOrthogonalModel CFSG.RankThree.PartOne.KCOrthogonalD4 in
theorem localDeltaIn_eq_bot_projOrth
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hCL : CommonLayerCentralizerTrivial (ProjOrthDerived Q) p)
    (E₁ : Subgroup (ProjOrthDerived Q)) (hE₁ : IsElemAbelian p E₁) (hc : Nat.card E₁ = p ^ 2)
    {H : Subgroup (MulAut (ProjOrthDerived Q))} (hH : innerAut (ProjOrthDerived Q) ≤ H) :
    localDeltaIn p H (E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))) =
      ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Nontrivial V := nontrivial_of_totallySingular_orth hT
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj := conj_injective_of_center_eq_bot_orth hcenter
  have hH' : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H := hH
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have : CharP K (ringChar K) := ringChar.charP K
  have hE₁' : CFSG.Assembly.IsElemAbelian p E₁ := ⟨hE₁.1, hE₁.2⟩
  obtain ⟨Ã, hÃM, hsyl, e, he, -, -, -, -, hline, -, -, -, -, -⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp hp2 hpl Q hQ E₁ hE₁' hc
  have hK := kernelLineData Q hQ hp hp2 hpl E₁ hE₁' hc Ã ⟨hÃM, hsyl⟩
  have hord : ∀ x : Ã, x ≠ 1 → orderOf (x : orthDerived Q) = p := fun x hx1 => by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hK.exp x) hx1
  have hmemE : ∀ x : Ã, (QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q) ∈ E₁ :=
    fun x => by
      have h1 := he x
      rw [QuotientGroup.mk'_apply] at h1
      rw [← h1]
      exact (e x).2
  have hconjE : ∀ x : Ã, MulAut.conj (QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q) ∈
      E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    fun x => ⟨_, hmemE x, rfl⟩
  have hfix : ∀ M : Subgroup Ã, Nat.card M = p → ∀ x ∈ M, x ≠ 1 →
      fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V) = planeFixSpace Ã ⊔ lineSpace M := by
    intro M hM x hxM hx1
    obtain ⟨h1, h2⟩ := hline M hM x hxM hx1
    rw [← h2, ← h1]
    rfl
  have hoi : ∀ x : Ã, x ≠ 1 → OddOrderIsometry Q p ((x : orthDerived Q) : V ≃ₗ[K] V) :=
    fun x hx1 => oddOrderIsometry_of_orthDerived hp hpl hQ _ (hord x hx1)
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  have hact : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ → ∀ x ∈ M, x ≠ 1 →
      3 ≤ finrank K (fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V)) →
      fixedComponentImage Q ((x : orthDerived Q) : V ≃ₗ[K] V) ≤ fixSub g := by
    intro M hM hMne x hxM hx1 h3
    obtain ⟨z, hzM⟩ : ∃ z : Ã, z ∉ M := by
      by_contra hall
      push Not at hall
      have hMtop : M = ⊤ := eq_top_iff.2 fun z _ => hall z
      have h1 : Nat.card M = Nat.card Ã := by rw [hMtop, Subgroup.card_top]
      rw [hM, hK.card] at h1
      have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
      omega
    have hz1 : z ≠ 1 := fun h => hzM (h ▸ M.one_mem)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
    have hvW : v ∈ fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V) := by
      rw [hfix M hM x hxM hx1]
      exact Submodule.mem_sup_right hv
    have hzv : ((z : orthDerived Q) : V ≃ₗ[K] V) v ≠ v := fun h =>
      hv0 (CFSG.LieType.SeitzGeneration.eq_zero_of_fixed_of_not_mem hp hK hM hz1 hzM hv h)
    have hzC : ((z : orthDerived Q) : V ≃ₗ[K] V) ∈
        isometryCentralizer Q ((x : orthDerived Q) : V ≃ₗ[K] V) := by
      refine Subgroup.mem_inf.2 ⟨orthDerived_le_orthogonalGroup (z : orthDerived Q).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun y : Ã => ((y : orthDerived Q) : V ≃ₗ[K] V)) (hK.comm z x)
    have hzp : ((z : orthDerived Q) : V ≃ₗ[K] V) ^ p = 1 := by
      have := congrArg (fun y : Ã => ((y : orthDerived Q) : V ≃ₗ[K] V)) (hK.exp z)
      simpa using this
    obtain ⟨w, hw, hwp, hw1⟩ := orth_exists_supported_of_moves (hoi x hx1) hzC hzp hvW hzv
    exact orthFixedComponentImage_le_fixSub hQ hT hp hp3 hpl hinj hH' hg _ (hord x hx1) (hconjE x)
      hw hwp hw1 h3
  have hFL : ∀ x : Ã, x ≠ 1 → 3 ≤ finrank K (fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V)) →
      fixedComponentImage Q ((x : orthDerived Q) : V ≃ₗ[K] V) ≤ fixSub g := by
    intro x hx1 h3
    have hxp : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hK.exp x) hx1
    by_cases hne : lineSpace (Subgroup.zpowers x) = ⊥
    · obtain ⟨M₁, -, hM₁, -, -, hM₁ne, -⟩ := hK.two_active
      obtain ⟨y, hyM, hy1⟩ : ∃ y ∈ M₁, y ≠ 1 := by
        by_contra hall
        push Not at hall
        have : M₁ = ⊥ := eq_bot_iff.2 fun y hy => hall y hy
        rw [this, Subgroup.card_bot] at hM₁
        exact hp.one_lt.ne hM₁
      have hxy : fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V) ≤
          fixedSpace ((y : orthDerived Q) : V ≃ₗ[K] V) := by
        rw [hfix _ hxp x (Subgroup.mem_zpowers x) hx1, hne, sup_bot_eq,
          hfix M₁ hM₁ y hyM hy1]
        exact le_sup_left
      have h3y := h3.trans (Submodule.finrank_mono hxy)
      exact (orthFixedComponentImage_mono (hoi x hx1) (hoi y hy1) hxy).trans
        (hact M₁ hM₁ hM₁ne y hyM hy1 h3y)
    · exact hact _ hxp hne x (Subgroup.mem_zpowers x) hx1 h3
  have hKL : ∀ x : Ã, x ≠ 1 →
      ⁅Subgroup.centralizer ({(QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q)} :
          Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({(QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q)} :
          Set (ProjOrthDerived Q))⁆ ≤ fixSub g := fun x hx1 =>
    orth_commutator_centralizer_le_of_blocks hQ hT hp hp3 hpl _ (hord x hx1) (fixSub g)
      (fun Rep hRep h hh hne hm => orthComponentImage_le_fixSub hQ hT hp hp3 hpl hinj hH' hg _
        (hord x hx1) (hconjE x) Rep hRep h hh hne hm) (hFL x hx1)
  have hAinner : E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
      Inn (ProjOrthDerived Q) := by
    rintro _ ⟨k, -, rfl⟩
    exact ⟨k, rfl⟩
  have hAel : IsElementaryAbelian p
      (E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))) := by
    refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).2 ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : MulAut (ProjOrthDerived Q)) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE₁.2 x hx, map_one]
  have hAc : Nat.card (E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))) =
      p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hc]
  have hbot := hCL _ le_rfl _ hAinner hAel hAc
  rw [iInf_centralizer_layerCentralizer_eq_bot_iff] at hbot
  refine hbot g fun a ha ha1 d hd => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  set x : Ã := e.symm ⟨a₀, ha₀⟩ with hxdef
  have hxa : (QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q) = a₀ := by
    have h1 := he x
    rw [QuotientGroup.mk'_apply] at h1
    rw [← h1, hxdef, MulEquiv.apply_symm_apply]
  have hx1 : x ≠ 1 := fun h => ha1 (by
    rw [← hxa, h, OneMemClass.coe_one, QuotientGroup.mk_one, map_one])
  set S : Subgroup (MulAut (ProjOrthDerived Q)) := Inn (ProjOrthDerived Q) ⊓
    Subgroup.centralizer ({MulAut.conj a₀} : Set (MulAut (ProjOrthDerived Q))) with hS
  have hSeq : S = (Subgroup.centralizer ({a₀} : Set (ProjOrthDerived Q))).map
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
    ext φ
    rw [hS, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩
      refine ⟨k, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      apply hinj
      rw [map_mul, map_mul]
      exact hk
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      rw [← map_mul, ← map_mul, hk]
  have hdS : d ∈ ⁅S, S⁆ := by
    have h1 : layerCentralizer (Inn (ProjOrthDerived Q)) (MulAut.conj a₀) ≤ ⁅S, S⁆ := by
      change (CFSG.layer ↥S).map S.subtype ≤ ⁅S, S⁆
      refine (Subgroup.map_mono (layer_le_commutator_top_orth ↥S)).trans ?_
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact h1 hd
  rw [hSeq, ← Subgroup.map_commutator] at hdS
  obtain ⟨n, hn, rfl⟩ := hdS
  have hgn : g n = n := by
    rw [← hxa] at hn
    exact hKL x hx1 hn
  have h1 := mul_conj_mul_inv g n
  rw [hgn] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
