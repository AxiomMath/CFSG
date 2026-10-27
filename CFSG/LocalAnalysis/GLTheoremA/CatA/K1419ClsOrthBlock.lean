module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthModel
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmegaRank
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XType
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.OpenBridges
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166
import CFSG.Goldschmidt.Steps.G310Comp
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)
open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.Classical2 (ProjOrthDerived orthDerived)

private theorem dvd_X_sq_add_X_add_one_of_primaryFactor {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {k : K[X]} (hk : k ∈ primaryFactors x.toLinearMap)
    (hk1 : k ≠ X - 1) : k ∣ (X ^ 2 + X + 1 : K[X]) := by
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * (X ^ 2 + X + 1) := by ring
  have hdvd : k ∣ (X - 1 : K[X]) * (X ^ 2 + X + 1) := by
    rw [← hfac]
    exact hx.dvd_X_pow_sub_one hk
  rcases (irreducible_of_mem_primaryFactors hk).prime.dvd_or_dvd hdvd with h | h
  · exfalso
    exact hk1 (eq_of_monic_of_associated (monic_of_mem_primaryFactors hk) monic_X_sub_one
      ((irreducible_of_mem_primaryFactors hk).associated_of_dvd irreducible_X_sub_one h))
  · exact h

private theorem primaryFactors_three_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    ∀ k ∈ primaryFactors x.toLinearMap, k = X - 1 ∨ k = h ∨ k = reciprocalPolynomial h := by
  classical
  have hmonic : h.Monic := monic_of_mem_primaryFactors hh
  have hirr_h : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hcoeff0 : h.coeff 0 ≠ 0 := hx.coeff_zero_ne hh
  have hh_dvd : h ∣ (X ^ 2 + X + 1 : K[X]) :=
    dvd_X_sq_add_X_add_one_of_primaryFactor hx hh hne1
  have hF_natDegree : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hF_monic : (X ^ 2 + X + 1 : K[X]).Monic := by
    rw [show (X ^ 2 + X + 1 : K[X]) = X ^ 2 + (X + 1) by ring]
    refine Polynomial.monic_X_pow_add (p := (X + 1 : K[X])) ?_
    compute_degree!
  have hF_ne_zero : (X ^ 2 + X + 1 : K[X]) ≠ 0 := hF_monic.ne_zero
  have hF_coeff0 : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by
    rw [coeff_add, coeff_add, coeff_X_pow, coeff_X, coeff_one]
    norm_num
  have hpos : 0 < h.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hirr_h.not_isUnit (isUnit_of_natDegree_eq_zero_of_ne_zero hirr_h.ne_zero h0)
  intro k hk
  by_cases hk1 : k = X - 1
  · exact Or.inl hk1
  · refine Or.inr ?_
    have hkmonic : k.Monic := monic_of_mem_primaryFactors hk
    have hirr_k : Irreducible k := irreducible_of_mem_primaryFactors hk
    have hkpos : 0 < k.natDegree := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hirr_k.not_isUnit (isUnit_of_natDegree_eq_zero_of_ne_zero hirr_k.ne_zero h0)
    have hk_dvd : k ∣ (X ^ 2 + X + 1 : K[X]) :=
      dvd_X_sq_add_X_add_one_of_primaryFactor hx hk hk1
    by_cases hkh : k = h
    · exact Or.inl hkh
    · refine Or.inr ?_
      have hcop : IsCoprime k h :=
        isCoprime_of_irreducible_monic_ne hirr_k hirr_h hkmonic hmonic hkh
      have hkh_dvd : k * h ∣ (X ^ 2 + X + 1 : K[X]) := hcop.mul_dvd hk_dvd hh_dvd
      have hsum : k.natDegree + h.natDegree ≤ 2 := by
        have hle := Polynomial.natDegree_le_of_dvd hkh_dvd hF_ne_zero
        rwa [hF_natDegree, natDegree_mul hirr_k.ne_zero hmonic.ne_zero] at hle
      have hdeg_h1 : h.natDegree = 1 := by omega
      have hdeg_k1 : k.natDegree = 1 := by omega
      have hF_eq : (X ^ 2 + X + 1 : K[X]) = k * h :=
        eq_of_monic_of_dvd_of_natDegree_le (hkmonic.mul hmonic) hF_monic hkh_dvd (by
          have h2 : (k * h).natDegree = k.natDegree + h.natDegree :=
            natDegree_mul hirr_k.ne_zero hmonic.ne_zero
          omega)
      have hconst : k.coeff 0 * h.coeff 0 = 1 := by
        have h := congrArg (fun p : K[X] => p.coeff 0) hF_eq
        rw [mul_coeff_zero, hF_coeff0] at h
        exact h.symm
      have hk0 : k.coeff 0 = (reciprocalPolynomial h).coeff 0 := by
        rw [coeff_zero_reciprocalPolynomial hmonic]
        exact eq_inv_of_mul_eq_one_left hconst
      have hstar_deg1 : (reciprocalPolynomial h).natDegree = 1 := by
        rw [natDegree_reciprocalPolynomial hcoeff0, hdeg_h1]
      have hk_eq : k = X + C (k.coeff 0) := hkmonic.eq_X_add_C hdeg_k1
      have hstar_eq : reciprocalPolynomial h = X + C ((reciprocalPolynomial h).coeff 0) :=
        (monic_reciprocalPolynomial hcoeff0).eq_X_add_C hstar_deg1
      calc k = X + C (k.coeff 0) := hk_eq
        _ = X + C ((reciprocalPolynomial h).coeff 0) := by rw [hk0]
        _ = reciprocalPolynomial h := hstar_eq.symm

private theorem self_mem_supportedBlock {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    x ∈ supportedBlock Q x h := by
  classical
  refine hx.mem_supportedBlock_of_block hh (Subgroup.mem_centralizer_singleton_iff.mpr rfl) ?_ ?_
  · refine fixes_othersSpace_iff.mpr fun k hk hkh hkh' v hv => ?_
    rcases primaryFactors_three_eq hx hh hne1 k hk with hk1 | hk2 | hk2
    · subst hk1
      have hv0 : x.toLinearMap v - v = 0 := by
        have h := mem_primaryComponent.mp hv
        simpa using h
      exact sub_eq_zero.mp hv0
    · exact absurd hk2 hkh
    · exact absurd hk2 hkh'
  · intro u _
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem u

private theorem self_mem_specialBlock {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 3 ∣ primaryMultiplicity x.toLinearMap h) :
    x ∈ specialBlock Q x h := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hx_supp : x ∈ supportedBlock Q x h := self_mem_supportedBlock hx hh hne1
  refine mem_specialBlock.mpr ⟨hx_supp, ?_⟩
  obtain ⟨hroot, hord⟩ := hx.orderOf_root Nat.prime_three hh hne1
  let c : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.root h) hroot
  have hblock : blockGL Q x h ⟨x, hx_supp⟩ = scalarGL x h c := by
    refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
    rw [coe_blockGL, coe_scalarGL]
    exact (coe_root_smul_primaryComponent x.toLinearMap h v).symm
  rw [blockDet_apply, hblock, det_scalarGL]
  have hc3 : c ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one c
  obtain ⟨q, hq⟩ := hm
  have hcu : c ^ primaryMultiplicity x.toLinearMap h = 1 := by
    rw [hq, pow_mul, hc3, one_pow]
  rw [← Units.val_pow_eq_pow_val, hcu, Units.val_one]

theorem orth_component_named {p : ℕ} {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hp : p.Prime) (hp2 : p ≠ 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) :
    ∃ x : ↥(orthDerived Q),
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x = a ∧
      OddOrderIsometry Q p (x : V ≃ₗ[K] V) ∧
      ((∃ h, h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧ h ≠ X - 1 ∧
          CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
          J = componentImage Q (x : V ≃ₗ[K] V) h) ∨
        ∃ (F : Subgroup (V ≃ₗ[K] V)), CFSG.IsQuasisimple ↥F ∧
          F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
          (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal ∧
          J = ((F.subgroupOf (orthDerived Q)).map
            (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  obtain ⟨x, hxa, hx, hcent⟩ : ∃ x : ↥(orthDerived Q), ρ x = a ∧
      OddOrderIsometry Q p (x : V ≃ₗ[K] V) ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).map ρ := by
    by_cases h1 : a = 1
    · refine ⟨1, by rw [h1, map_one], oddOrderIsometry_of_pow_eq_one hp hpℓ hQ 1 (one_pow p), ?_⟩
      have e1 : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) = ⊤ := by
        ext g
        simp [h1, Subgroup.mem_centralizer_iff]
      have e2 : Subgroup.centralizer ({(1 : ↥(orthDerived Q))} : Set ↥(orthDerived Q)) = ⊤ := by
        ext g
        simp [Subgroup.mem_centralizer_iff]
      rw [e1, e2, Subgroup.map_top, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    · obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
        CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
      obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a (orderOf_eq_prime ha h1)
      exact ⟨x, hxa, oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxp, hcent⟩
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  have hNeq : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) = N := by
    rw [hcent]
    exact CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x
  rw [hNeq] at hJ
  obtain ⟨n, F, hFq, hFsup, hFn0⟩ := exists_fixedFactors hx
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i =>
    (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived
  set C : Fin n → Subgroup (ProjOrthDerived Q) := fun i => ((F i).subgroupOf (orthDerived Q)).map ρ
    with hC
  have hCsup : (⨆ i, C i) = fixedLayerImage Q xe := by
    by_cases hlist : FixedLayerListed Q xe
    · rw [fixedLayerImage_of_listed hlist]
      unfold fixedComponentImage
      rw [← hFsup hlist, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
    · have hn := hFn0 hlist
      subst hn
      simp [fixedLayerImage, hlist]
  have hCle : ∀ i, C i ≤ fixedComponentImage Q xe := fun i =>
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      ((hFq i).2.1 (Subgroup.mem_subgroupOf.mp hg))
  have hCcomp : ∀ i, CFSG.Open.IsComponentOf (C i) N := by
    intro i
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q xe).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine isComponentOf_of_normal_normal (hCle i) fixedComponentImage_le_centralizerImage ?_
      hx.normal_fixedComponentImage (isQuasisimple_map_projective (hFΩ i) (hFq i).1)
    rw [Subgroup.normal_subgroupOf_iff (hCle i)]
    intro h k hh hk
    exact hconj _ _ hh hk
  let ι₁ := {r : ↥Rep // r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)}
  have hspecΩ : ∀ r : ι₁, specialBlock Q xe r.1.1 ≤ orthDerived Q := fun r =>
    specialBlock_le_orthDerived_of_perfect r.2.2.1
      ((specialBlock_le_isometryCentralizer r.1.1).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let S : ι₁ → Subgroup (ProjOrthDerived Q) := fun r => componentImage Q xe r.1.1
  have hScomp : ∀ r, CFSG.Open.IsComponentOf (S r) N := fun r =>
    isComponentOf_of_normal_normal componentImage_le_centralizerImage le_rfl normal_componentImage
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (isQuasisimple_map_projective (hspecΩ r) r.2.2)
  set EN : Subgroup (ProjOrthDerived Q) := (⨆ r, S r) ⊔ fixedLayerImage Q xe with hEN
  have hSN : ∀ r, S r ≤ N := fun r => componentImage_le_centralizerImage
  have hENN : EN ≤ N :=
    sup_le (iSup_le hSN) fixedLayerImage_le_centralizerImage
  have hENnormal : (EN.subgroupOf N).Normal :=
    normal_subgroupOf_sup (iSup_le hSN) fixedLayerImage_le_centralizerImage
      (normal_subgroupOf_iSup S hSN fun r => normal_componentImage) hx.normal_fixedLayerImage
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := fun c hc e he =>
    (Subgroup.normal_subgroupOf_iff hENN).mp hENnormal e c he hc
  have hperf : ∀ P : Subgroup (ProjOrthDerived Q), P ≤ N → commutator ↥P = ⊤ → P ≤ EN := by
    intro P hPN hP
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ hp hp2 x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left
        (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
  let Fm : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) := Sum.elim S C
  have hFm : ∀ i, CFSG.Open.IsComponentOf (Fm i) N := by
    rintro (r | i)
    · exact hScomp r
    · exact hCcomp i
  have hiSup : (⨆ i, Fm i) = EN := by
    rw [iSup_sum]
    simp only [Fm, Sum.elim_inl, Sum.elim_inr]
    rw [hCsup]
  obtain ⟨i, rfl⟩ := component_mem_named_factors Fm hFm
    (fun P hPN hP => hiSup ▸ hperf P hPN hP) hJ
  refine ⟨x, hxa, hx, ?_⟩
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · exact Or.inl ⟨h, hxe ▸ hRep.1 hh, hne, hq, rfl⟩
  · exact Or.inr ⟨F i, (hFq i).1, (hFq i).2.1, (hFq i).2.2, rfl⟩

private def OrthConcl {T : Type} [Group T] (f : ℕ) (b : T) (J : Subgroup T) : Prop :=
  (∃ (b' k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b' ∧ Nat.card E = 2 ^ k ∧
      Nonempty (PSimple 3 J ≃* StatedProj (StatedSL b' E)) ∧ (3 ∣ b' → b ∈ J)) ∨
  (∃ (b' k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
      (hτ : ∀ y, τ (τ y) = y), 2 ≤ b' ∧ (∀ y, τ y = y ^ 2 ^ k) ∧ Nat.card E = (2 ^ k) ^ 2 ∧
      Nonempty (PSimple 3 J ≃* heldSU b' E τ hτ ⧸ Subgroup.center (heldSU b' E τ hτ)) ∧
      (3 ∣ b' → b ∈ J)) ∨
  (∃ (s : ℕ) (K' : Type) (_ : Field K') (_ : Finite K'), 2 ≤ s ∧ Nat.card K' = 2 ^ f ∧
      ¬ (s = 2 ∧ Nat.card K' = 2) ∧ Nonempty (PSimple 3 J ≃* StatedProj (StatedSp s K'))) ∨
  (∃ s : ℕ, StatedClassicalModel (PSimple 3 J) .POmegaPlus s 2 f ∨
      StatedClassicalModel (PSimple 3 J) .POmegaMinus s 2 f)

private theorem OrthConcl_congr {T T' : Type} [Group T] [Group T'] [Finite T] (e : T ≃* T')
    (f : ℕ) (b : T) (J : Subgroup T) (hJp : Group.IsPerfect ↥J) :
    OrthConcl f b J ↔ OrthConcl f (e b) (J.map e) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨he⟩ := CFSG.LocalAnalysis.GLTheoremA.S172X.nonempty_pSimple_equiv_map_of_central 3
    e.toMonoidHom
    (fun g hg => by
      rw [show g = 1 from e.injective (hg.trans (map_one (e : T →* T')).symm)]
      exact Subgroup.one_mem _) hJp
  have hmem : ∀ y : T, y ∈ J ↔ e y ∈ J.map e := fun y => by
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      rw [← e.injective hzy]
      exact hz
  constructor
  · rintro (⟨b', k, E, hEf, hEfin, hb2, hEk, ⟨ee⟩, hx⟩ |
      ⟨b', k, E, hEf, hEfin, τ, hτ, hb2, hτk, hEc, ⟨ee⟩, hx⟩ |
      ⟨s, K', hK'f, hK'fin, hs2, hK'c, hne, ⟨ee⟩⟩ | ⟨s, hs⟩)
    · exact Or.inl ⟨b', k, E, hEf, hEfin, hb2, hEk, ⟨he.symm.trans ee⟩,
        fun h3 => (hmem b).mp (hx h3)⟩
    · exact Or.inr (Or.inl ⟨b', k, E, hEf, hEfin, τ, hτ, hb2, hτk, hEc,
        ⟨he.symm.trans ee⟩, fun h3 => (hmem b).mp (hx h3)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, K', hK'f, hK'fin, hs2, hK'c, hne, ⟨he.symm.trans ee⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨s, hs.imp
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv he)
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv he)⟩))
  · rintro (⟨b', k, E, hEf, hEfin, hb2, hEk, ⟨ee⟩, hx⟩ |
      ⟨b', k, E, hEf, hEfin, τ, hτ, hb2, hτk, hEc, ⟨ee⟩, hx⟩ |
      ⟨s, K', hK'f, hK'fin, hs2, hK'c, hne, ⟨ee⟩⟩ | ⟨s, hs⟩)
    · exact Or.inl ⟨b', k, E, hEf, hEfin, hb2, hEk, ⟨he.trans ee⟩,
        fun h3 => (hmem b).mpr (hx h3)⟩
    · exact Or.inr (Or.inl ⟨b', k, E, hEf, hEfin, τ, hτ, hb2, hτk, hEc,
        ⟨he.trans ee⟩, fun h3 => (hmem b).mpr (hx h3)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, K', hK'f, hK'fin, hs2, hK'c, hne, ⟨he.trans ee⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨s, hs.imp
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv he.symm)
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv he.symm)⟩))

private theorem specialBlock_concl {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} (hchar : ringChar K = 2)
    (f : ℕ) (hcard : Nat.card K = 2 ^ f) (b : ProjOrthDerived Q) {J : Subgroup (ProjOrthDerived Q)}
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hnt : Nontrivial (PSimple 3 J))
    {x : ↥(orthDerived Q)}
    (hxa : QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x = b)
    (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h) :
    OrthConcl f b J := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  obtain ⟨ePJ⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter 3 J hJq hnt
  have hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  let f_sb : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) →* ↥J :=
    ((ρ.comp (Subgroup.inclusion hspecΩ)).codRestrict J (fun g =>
      hJeq.symm ▸ Subgroup.mem_map.mpr ⟨Subgroup.inclusion hspecΩ g,
        Subgroup.mem_subgroupOf.mpr g.2, rfl⟩))
  have hf_sb : Function.Surjective f_sb := by
    intro y
    have hy : (y : ProjOrthDerived Q) ∈
        ((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)).map ρ := by
      have h : (y : ProjOrthDerived Q) ∈ componentImage Q (x : V ≃ₗ[K] V) h := by
        rw [← hJeq]; exact y.2
      simpa only [componentImage] using h
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(z : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hz⟩, Subtype.ext ?_⟩
    show ρ (Subgroup.inclusion hspecΩ
      ⟨(z : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hz⟩) = (y : ProjOrthDerived Q)
    rw [show Subgroup.inclusion hspecΩ
      ⟨(z : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hz⟩ = z from Subtype.ext rfl, hzy]
  have hker_sb : f_sb.ker ≤ Subgroup.center ↥(specialBlock Q (x : V ≃ₗ[K] V) h) := by
    intro g hg
    have h1 : Subgroup.inclusion hspecΩ g ∈ (scalars K V).subgroupOf (orthDerived Q) :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hspecΩ g)).mp
        (congrArg Subtype.val (MonoidHom.mem_ker.mp hg))
    obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp h1)
    have hc' : ∀ v : V, (g : V ≃ₗ[K] V) v = c • v := hc
    rw [Subgroup.mem_center_iff]
    intro k
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    change (k : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v) = (g : V ≃ₗ[K] V) ((k : V ≃ₗ[K] V) v)
    rw [hc' v, hc', map_smul]
  obtain ⟨eJS⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hq.1.commutator_eq_top f_sb hf_sb hker_sb
  rcases eq_or_ne h (reciprocalPolynomial h) with hself | hne
  ·
    obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
      hx.exists_selfDual_hermitian (p := 3) (by decide) hh hne1 hself
    have hd : finrank K (AdjoinRoot h) = 2 * d := by
      rw [(AdjoinRoot.powerBasis (irreducible_of_mem_primaryFactors hh).ne_zero).finrank,
        AdjoinRoot.powerBasis_dim, hdeg]
    have hdpos : 1 ≤ d := by
      have := (Fact.out : Irreducible h).natDegree_pos
      omega
    obtain ⟨ℓ, ff, hU, hq0, hbar⟩ :=
      CFSG.RankThree.PartOne.KCOrthogonal.exists_unitaryFieldData (K := K) (E := AdjoinRoot h) hd
    have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
      rw [hbar, frobPow_apply]
    let B : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h →ₛₗ[hU.bar]
        primaryComponent (x : V ≃ₗ[K] V).toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
      LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
        (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
        (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
    have hBH : ∀ u w, B u w = H u w := fun u w => rfl
    have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
    have hBl : B.SeparatingLeft := by
      intro u hu
      refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
      have h1 := hH u ⟨w, hw⟩ 1
      rw [mul_one, one_smul] at h1
      have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
      rw [h2, map_zero] at h1
      exact h1.symm
    have hrange : (specialBlockGL Q (x : V ≃ₗ[K] V) h).range = sesqSpecialUnitaryGroup B := by
      rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
      congr 1
      ext γ
      rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
      exact Iff.rfl
    let e₁ : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
      (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
        (MulEquiv.subgroupCongr hrange)
    haveI := hU.finite
    haveI : Fact ℓ.Prime := ⟨hU.prime⟩
    haveI := hU.charP
    letI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
    have hE : Nat.card (AdjoinRoot h) = (ℓ ^ (ff * d)) ^ 2 := by
      rw [hU.card, ← pow_mul, mul_comm]
    have hK : Fintype.card (AdjoinRoot h) = (ℓ ^ (ff * d)) ^ 2 := by
      rw [Fintype.card_eq_nat_card, hE]
    have hcharE : ringChar (AdjoinRoot h) = ringChar K := (Algebra.ringChar_eq K (AdjoinRoot h)).symm
    have hℓ : ringChar (AdjoinRoot h) = ℓ := ringChar.eq _ ℓ
    have hℓ2 : ℓ = 2 := hℓ.symm.trans (hcharE.trans hchar)
    rcases Nat.lt_or_ge (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) 3 with hm3 | hm3
    ·
      have hm2 : Module.finrank (AdjoinRoot h)
          (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) = 2 := by
        have : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 2 := by omega
        exact this
      obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU
        hBsymm hBl hm2
      letI : Fintype ↥hU.fixedField := Fintype.ofFinite _
      have hcardF : Fintype.card ↥hU.fixedField = ℓ ^ (ff * d) := by
        rw [Fintype.card_eq_nat_card, hU.card_fixedField]
      have h4 : 4 ≤ Fintype.card ↥hU.fixedField := by
        by_contra hlt
        refine false_of_isQuasisimple_of_isSolvable' hq ?_
        haveI := isSolvable_sl_two_of_card_lt_four' (E := ↥hU.fixedField)
          (by rw [Nat.card_eq_fintype_card]; omega)
        exact Group.isSolvable_of_isSolvable_injective (f := (e₁.trans φ).toMonoidHom)
          (e₁.trans φ).injective
      have hcardNat : Nat.card ↥hU.fixedField = 2 ^ (ff * d) := by
        rw [Nat.card_eq_fintype_card, hcardF, hℓ2]
      obtain ⟨eSZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl 2
        (e₁.trans φ)
      exact Or.inl ⟨2, ff * d, ↥hU.fixedField, inferInstance, inferInstance, le_rfl, hcardNat,
        ⟨ePJ.trans (eJS.trans eSZ)⟩, fun h3 => absurd h3 (by decide)⟩
    ·
      have hmq : (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h, ℓ ^ (ff * d)) ≠ (3, 2) := by
        intro he
        have h3 : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3 := (Prod.mk.inj he).1
        have h2 : ℓ ^ (ff * d) = 2 := (Prod.mk.inj he).2
        refine false_of_isQuasisimple_of_isSolvable' hq ?_
        haveI : Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) := by
          refine isSolvable_of_card_primeFactors_le_two ?_
          have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
            (n := primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) rfl (by omega)).2.1
          rw [h3, h2] at hcard
          have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
              ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
          have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
            exact_mod_cast hcard.trans e
          rw [h216]
          decide +kernel
        exact Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective
      obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
      obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU
        e₀ he₀
      have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
          (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) =
          CFSG.Open.StatedSU (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) (ℓ ^ (ff * d))
            (AdjoinRoot h) := by
        rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
        exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
      let e₃ : ↥(CFSG.Open.StatedSU (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)
          (ℓ ^ (ff * d)) (AdjoinRoot h)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
        (e₂.trans (MulEquiv.subgroupCongr hS)).symm
      have hbarQ : ∀ y, hU.barEquiv y = y ^ ℓ ^ (ff * d) := fun y => by
        rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.barEquiv_apply,
          CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
      obtain ⟨eSZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_su
        (Q := ℓ ^ (ff * d)) rfl (e₁.trans e₃.symm) hU.barEquiv hU.bar_bar (fun y => by
          rw [hbarQ y, hℓ2])
      have hcardE : Nat.card (AdjoinRoot h) = (2 ^ (ff * d)) ^ 2 := by
        rw [hE, hℓ2]
      refine Or.inr (Or.inl ⟨primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h, ff * d,
        AdjoinRoot h, inferInstance, inferInstance, hU.barEquiv, hU.bar_bar, by omega, ?_, hcardE,
        ⟨ePJ.trans (eJS.trans eSZ)⟩, ?_⟩)
      · intro y
        rw [hbarQ y, hℓ2]
      · intro h3
        rw [hJeq, ← hxa]
        exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr
          (self_mem_specialBlock hx hh hne1 h3), rfl⟩
  ·
    let bb : Module.Basis (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h)) (AdjoinRoot h)
        (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
    let eSL : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃*
        Matrix.SpecialLinearGroup (Fin (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h))
          (AdjoinRoot h) :=
      ((MulEquiv.ofBijective (specialToSL Q (x : V ≃ₗ[K] V) h)
        ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩).trans
        (Matrix.SpecialLinearGroup.toLin_equiv bb).symm)
    obtain ⟨eSZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl
      (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) eSL
    refine Or.inl ⟨primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h, f * h.natDegree,
      AdjoinRoot h, inferInstance, inferInstance, hm, ?_, ⟨ePJ.trans (eJS.trans eSZ)⟩, ?_⟩
    · rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hcard, pow_mul]
    · intro h3
      rw [hJeq, ← hxa]
      exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr
        (self_mem_specialBlock hx hh hne1 h3), rfl⟩

private def OrthRankP (q : ℕ) (X : Type) [Group X] : Prop :=
  LieFactorData 2 X ∧ OrthFactorRank 2 q X

private theorem fixedFactor_concl {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} (hchar : ringChar K = 2)
    (f : ℕ) (hcard : Nat.card K = 2 ^ f) (b : ProjOrthDerived Q) {J : Subgroup (ProjOrthDerived Q)}
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hnt : Nontrivial (PSimple 3 J))
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn : (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal)
    (hJeq : J = ((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) :
    OrthConcl f b J := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
  have hcomp : OrthCompData (OrthRankP (Nat.card K)) ↥F :=
    orthCompData_fixedFactor_of (P := OrthRankP (Nat.card K)) hx
      (fun L hLn hLq => by
        obtain ⟨X, hXg, hXf, hLie, hRank, fX, hfX, hkX⟩ :=
          omegaFactorRank_holds K (fixedSpace (x : V ≃ₗ[K] V))
            (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)
            hx.polarBilin_fixed_nondegenerate L hLn hLq
        exact ⟨X, hXg, hXf, ⟨by rwa [hchar] at hLie, by rwa [hchar] at hRank⟩, fX, hfX, hkX⟩)
      F hFq hFle hFn
  have hperfP : ∀ (X : Type) [Group X], OrthRankP (Nat.card K) X → commutator X = ⊤ :=
    fun X _ hX => hX.1.perfect
  have hcompJ : OrthCompData (OrthRankP (Nat.card K)) ↥J := by
    rw [hJeq]
    exact OrthCompData.map_projective hperfP hFΩ hcomp
  obtain ⟨X, hXg, hXf, g, hP, hg, hgk⟩ := hcompJ
  rcases hP with ⟨hLie, hRank⟩
  obtain ⟨eY⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hLie.perfect g hg hgk
  obtain ⟨ePJ⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter 3 J hJq hnt
  unfold OrthFactorRank at hRank
  rcases hRank with hSL | hSU | hSp | hOm
  ·
    obtain ⟨m, j, E, hEf, hEfin, hm24, hj1, hcharE, hcardE, h4, ⟨eX⟩⟩ := hSL
    obtain ⟨eSZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl m eX
    refine Or.inl ⟨m, f * j, E, hEf, Finite.of_fintype E, ?_, ?_, ⟨ePJ.trans (eY.trans eSZ)⟩,
      ?_⟩
    · rcases hm24 with rfl | rfl <;> omega
    · rw [Nat.card_eq_fintype_card, hcardE, hcard, pow_mul]
    · intro h3
      rcases hm24 with rfl | rfl <;> exact absurd h3 (by norm_num)
  ·
    obtain ⟨j, q', E, hEf, hEfin, hj1, hcharE, hq', hcardE, ⟨eX⟩⟩ := hSU
    have hq'' : q' = 2 ^ (f * j) := by rw [hq', hcard, pow_mul]
    have hcardEK : Nat.card E = (2 ^ (f * j)) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hcardE, hq'']
    obtain ⟨τ, hτq, hτ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv hcardEK
    obtain ⟨eSZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_su
      (Q := 2 ^ (f * j)) hq'' eX τ hτ hτq
    exact Or.inr (Or.inl ⟨4, f * j, E, hEf, Finite.of_fintype E, τ, hτ, by norm_num, hτq,
      hcardEK, ⟨ePJ.trans (eY.trans eSZ)⟩, fun h3 => absurd h3 (by norm_num)⟩)
  ·
    obtain ⟨K', hK'f, hK'fin, hK'c, hK'r, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hK'card : Nat.card K' = 2 ^ f := hK'c.trans hcard
    have hne' : ¬(s = 2 ∧ Nat.card K' = 2) := fun h => hne (by rw [h.1, h.2])
    obtain ⟨eSZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp hs2 hne'
      (ringChar.of_eq hK'r) eX
    exact Or.inr (Or.inr (Or.inl ⟨s, K', hK'f, Finite.of_fintype K', hs2, hK'card, hne',
      ⟨ePJ.trans (eY.trans eSZ)⟩⟩))
  ·
    obtain ⟨K', hK'f, hK'fin, V', hV'a, hV'm, hV'fin, Q', hK'c, hK'r, hQ', hd, hT', ⟨eX⟩⟩ := hOm
    have hK'card : Nat.card K' = 2 ^ f := hK'c.trans hcard
    obtain ⟨s, hs⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel.exists_statedClassicalModel_quotCenter_orthDerived
        hK'card hQ' hd hT' eX
    exact Or.inr (Or.inr (Or.inr ⟨s, hs.imp
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (ePJ.trans eY).symm)
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (ePJ.trans eY).symm)⟩))

private theorem k1419_orth_model {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hchar : ringChar K = 2) (f : ℕ) (hcard : Nat.card K = 2 ^ f)
    (b : ProjOrthDerived Q) (hb : b ^ 3 = 1) (hb1 : b ≠ 1)
    {J : Subgroup (ProjOrthDerived Q)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({b} : Set (ProjOrthDerived Q))))
    (hnt : Nontrivial (PSimple 3 J)) :
    OrthConcl f b J := by
  have hpℓ : 3 ≠ ringChar K := by rw [hchar]; decide
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJ.2.2
  obtain ⟨x, hxa, hx, hcase⟩ :=
    orth_component_named Nat.prime_three (by decide) hQ hT hpℓ b hb J hJ
  rcases hcase with ⟨h, hh, hne1, hq, hJeq⟩ | ⟨F, hFq, hFle, hFn, hJeq⟩
  · exact specialBlock_concl hchar f hcard b hJq hnt hxa hx hh hne1 hq hJeq
  · exact fixedFactor_concl hchar f hcard b hJq hnt hx hFq hFle hFn hJeq

theorem k1419ClsOrthBlock {G : Type} [Group G] [Finite G] {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f : ℕ} (hG : StatedClassicalModel G t m 2 f)
    (a : G) (ha : a ^ 3 = 1) (ha1 : a ≠ 1) {J : Subgroup G}
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj a)) J) :
    (∃ (b k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b ∧ Nat.card E = 2 ^ k ∧
        Nonempty (PSimple 3 J ≃* StatedProj (StatedSL b E)) ∧ (3 ∣ b → a ∈ J)) ∨
    (∃ (b k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
        (hτ : ∀ y, τ (τ y) = y), 2 ≤ b ∧ (∀ y, τ y = y ^ 2 ^ k) ∧ Nat.card E = (2 ^ k) ^ 2 ∧
        Nonempty (PSimple 3 J ≃* heldSU b E τ hτ ⧸ Subgroup.center (heldSU b E τ hτ)) ∧
        (3 ∣ b → a ∈ J)) ∨
    (∃ (s : ℕ) (K' : Type) (_ : Field K') (_ : Finite K'), 2 ≤ s ∧ Nat.card K' = 2 ^ f ∧
        ¬ (s = 2 ∧ Nat.card K' = 2) ∧ Nonempty (PSimple 3 J ≃* StatedProj (StatedSp s K'))) ∨
    (∃ s : ℕ, StatedClassicalModel (PSimple 3 J) .POmegaPlus s 2 f ∨
        StatedClassicalModel (PSimple 3 J) .POmegaMinus s 2 f) := by
  obtain ⟨K, hKf, hKfin, V, hVa, hVm, hVfin, Q, hQ, hT, hcardK, hring, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_projOrth_model_card (Or.inr ht) hG
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hPIL : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer (MulAut.conj a) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_omega
      (Or.inr ht) hG hp3 (by decide) (by decide) a ha
  have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle := hPIL J hJ.1 hperfJ
  have hJcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hJle).1
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJcomp.2.2
  have hnt : Nontrivial (PSimple 3 J) := by
    have hQJ : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
      CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp3 hJ
    haveI : IsSimpleGroup (PSimple 3 J) := hQJ.2
    infer_instance
  have hJp : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJq.1
  have hfix : fixSubgroup (MulAut.congr e (MulAut.conj a)) =
      (fixSubgroup (MulAut.conj a)).map (e : G →* ProjOrthDerived Q) := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    show e (MulAut.conj a (e.symm x)) = x ↔ MulAut.conj a (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hJ' : CFSG.Open.IsComponentOf (J.map (e : G →* ProjOrthDerived Q))
      (Subgroup.centralizer ({e a} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJcomp
    rw [← hfix, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.congr_conj,
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_conj_eq_centralizer] at h1
    exact h1
  have hnt' : Nontrivial (PSimple 3 (J.map (e : G →* ProjOrthDerived Q))) := by
    obtain ⟨he⟩ := CFSG.LocalAnalysis.GLTheoremA.S172X.nonempty_pSimple_equiv_map_of_central 3
      e.toMonoidHom (fun g hg => by
        rw [show g = 1 from e.injective (hg.trans (map_one (e : G →* ProjOrthDerived Q)).symm)]
        exact Subgroup.one_mem _) hJp
    exact he.symm.nontrivial
  have hea3 : (e a) ^ 3 = 1 := by rw [← map_pow, ha, map_one]
  have hea1 : e a ≠ 1 := fun h => ha1 (e.injective (by rw [h, map_one]))
  have hconcl := k1419_orth_model hQ hT hring f hcardK (e a) hea3 hea1 hJ' hnt'
  exact (OrthConcl_congr e f a J hJp).mpr hconcl

end CFSG.LocalAnalysis.GLTheoremA.K1419
