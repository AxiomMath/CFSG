module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalPartsSO
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthBlocks
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Cubic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalReduceSO
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthOuter
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SympInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SympOuter
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
import CFSG.SignalizerFunctorTheorem.CatalogBridge.HallHigman
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial Module CFSG.Open CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Special

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem not_isQuasisimple_bot' {G : Type*} [Group G] :
    ¬ CFSG.IsQuasisimple ↥(⊥ : Subgroup G) := by
  rintro ⟨-, -, a, b, hab⟩
  apply hab
  haveI : Subsingleton (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) :=
    Quotient.instSubsingletonQuotient _
  exact Subsingleton.elim _ _

theorem cubicPair_specialBlock (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1) :
    CubicPair (specialBlock Q x h) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    rw [hx.specialBlock_eq_bot_of_finrank_eq_one hh h1] at hq
    exact not_isQuasisimple_bot' hq
  have key : ∃ u ∈ specialBlock Q x h, ∃ u' ∈ specialBlock Q x h,
      ((u : V →ₗ[K] V) - 1) ^ 2 = 0 ∧
        ∃ m : V, (u * u') m ≠ (u' * u) m ∧ (u * u') m ≠ -((u' * u) m) := by
    by_cases hself : h = reciprocalPolynomial h
    · exact exists_quad_specialBlock_selfDual hx hp2 hh hne1 hself hℓ hf hK h2 hl hl2 hm
    · exact exists_quad_specialBlock_paired hx hh hself h2 hl hl2 hm
  obtain ⟨u, hu, u', hu', hsq, m, hm1, hm2⟩ := key
  exact ⟨u, hu, u', hu', by rw [pow_succ, hsq, zero_mul], m, hm1, hm2⟩

end Special

section HallHigman

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem not_dvd_orderOf_of_isPGroup_two'' {G : Type*} [Group G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {T : Subgroup G} (hT : IsPGroup 2 T) : ∀ t ∈ T, ¬ q ∣ orderOf t := by
  intro t ht hdvd
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have h1 : orderOf t ∣ 2 ^ j := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hj
    simpa using this
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow (hdvd.trans h1)))

private theorem exists_sq_eq_one_of_mem_scalarKernel
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V] {z : ↥(orthDerived Q)}
    (hz : z ∈ (scalars K V).subgroupOf (orthDerived Q)) :
    ∃ c : K, c ^ 2 = 1 ∧ ∀ v, (z : V ≃ₗ[K] V) v = c • v := by
  have ha : ∃ a : V, Q a ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    apply hu
    apply eq_zero_of_polar_eq_zero hQ
    intro v
    rw [QuadraticMap.polar, h, h, h, sub_zero, sub_zero]
  obtain ⟨a, ha⟩ := ha
  exact CFSG.RankThree.Classical.exists_sq_eq_one_of_mem_scalars (Subgroup.mem_subgroupOf.1 hz)
    (orthDerived_le_orthogonalGroup z.2) ha

theorem commutator_eq_bot_of_cubicPair {q : ℕ} [hq : Fact q.Prime] [CharP K q] (hq5 : 5 ≤ q)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A : Subgroup (V ≃ₗ[K] V)}
    (hAΩ : A ≤ orthDerived Q) (hA : CubicPair A) {J T₀ : Subgroup (ProjOrthDerived Q)}
    (hJ : J = (A.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJT : J ≤ Subgroup.normalizer (T₀ : Set _))
    (hT : IsPGroup 2 T₀) : ⁅T₀, J⁆ = ⊥ := by
  obtain ⟨u, hu, u', hu', hcube, m, hne1, hne2⟩ := hA
  obtain ⟨U, rfl⟩ : ∃ U : ↥(orthDerived Q), (U : V ≃ₗ[K] V) = u := ⟨⟨u, hAΩ hu⟩, rfl⟩
  obtain ⟨U', rfl⟩ : ∃ U' : ↥(orthDerived Q), (U' : V ≃ₗ[K] V) = u' := ⟨⟨u', hAΩ hu'⟩, rfl⟩
  have hq2 : q ≠ 2 := by omega
  haveI : Nontrivial V := ⟨⟨_, _, hne1⟩⟩
  let π : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  let ρ : ↥(orthDerived Q) →* LinearMap.GeneralLinearGroup K V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.toMonoidHom.comp
      (orthDerived Q).subtype
  have hρ : Function.Injective ρ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.injective.comp
      (orthDerived Q).subtype_injective
  have hρv : ∀ g : ↥(orthDerived Q),
      ((ρ g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = ((g : V ≃ₗ[K] V) : V →ₗ[K] V) :=
    fun g => rfl
  have huJ : π U ∈ J := by
    rw [hJ]
    exact ⟨U, hu, rfl⟩
  have hu'J : π U' ∈ J := by
    rw [hJ]
    exact ⟨U', hu', rfl⟩
  have hker : ∀ w ∈ π.ker, ¬ q ∣ orderOf w := by
    intro w hw hdvd
    have hw' : w ∈ (scalars K V).subgroupOf (orthDerived Q) :=
      (QuotientGroup.eq_one_iff w).1 (MonoidHom.mem_ker.1 hw)
    obtain ⟨c, hc2, hc⟩ := exists_sq_eq_one_of_mem_scalarKernel hQ hw'
    have hw2 : w ^ 2 = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      rw [Subgroup.coe_pow, pow_two, LinearEquiv.mul_apply, hc, hc, smul_smul, ← pow_two, hc2,
        one_smul]
      rfl
    have h1 : q ∣ 2 := hdvd.trans (orderOf_dvd_of_pow_eq_one hw2)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 h1)
  have hnc : π U' * π U ≠ π U * π U' := by
    intro h
    obtain ⟨z, hzdef⟩ : ∃ z : ↥(orthDerived Q), z = (U * U')⁻¹ * (U' * U) := ⟨_, rfl⟩
    have hz : z ∈ (scalars K V).subgroupOf (orthDerived Q) := by
      have h3 : π z = 1 := by
        rw [hzdef, map_mul, map_inv, map_mul, map_mul, h, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff z).1 h3
    obtain ⟨c, hc2, hc⟩ := exists_sq_eq_one_of_mem_scalarKernel hQ hz
    have hprod : U' * U = (U * U') * z := by
      rw [hzdef]
      group
    have h1 : ((U' : V ≃ₗ[K] V) * U) m = c • (((U : V ≃ₗ[K] V) * U') m) := by
      have h3 := congrArg (fun g : ↥(orthDerived Q) => (g : V ≃ₗ[K] V) m) hprod
      simp only [Subgroup.coe_mul] at h3
      rw [h3, show ((U : V ≃ₗ[K] V) * U' * z) m = ((U : V ≃ₗ[K] V) * U') ((z : V ≃ₗ[K] V) m)
        from rfl, hc, map_smul]
    rcases sq_eq_one_iff.1 hc2 with hc1 | hc1
    · rw [hc1, one_smul] at h1
      exact hne1 h1.symm
    · rw [hc1, neg_one_smul] at h1
      exact hne2 (by rw [h1, neg_neg])
  have hcube' : (((ρ U : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) - 1) ^ 3 = 0 := by
    rw [hρv]
    exact hcube
  have huq : U ^ q = 1 := by
    apply hρ
    rw [map_pow, map_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact CFSG.SignalizerFunctorTheorem.CatalogBridge.pow_eq_one_of_sub_one_pow_eq_zero (K := K)
      (by rw [show q - 1 = 3 + (q - 4) by omega, pow_add, hcube', zero_mul])
  exact commutator_eq_bot_of_sub_one_pow_lift (k := 3) (by omega) hJq hJT
    (not_dvd_orderOf_of_isPGroup_two'' hq.out hq2 hT) π (QuotientGroup.mk'_surjective _) hker ρ hρ
    huJ ⟨_, hu'J, hnc⟩ huq hcube'

end HallHigman

section Components

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem exists_lift_component_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) :
    ∃ x : V ≃ₗ[K] V, OddOrderIsometry Q p x ∧
      ((∃ h : K[X], h ∈ primaryFactors x.toLinearMap ∧ h ≠ X - 1 ∧
          CFSG.IsQuasisimple ↥(specialBlock Q x h) ∧ J = componentImage Q x h) ∨
        (FixedLayerListed Q x ∧ ∃ F : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F ∧
          F ≤ supportedFixedDerived Q x ∧ (F.subgroupOf (supportedFixedDerived Q x)).Normal ∧
          J = (F.subgroupOf (orthDerived Q)).map
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
    · refine ⟨1, by rw [h1, map_one], oddOrderIsometry_of_pow_eq_one hp hpℓ hQ 1 (one_pow p),
        ?_⟩
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
  obtain ⟨i, hi⟩ := component_mem_named_factors Fm hFm
    (fun P hPN hP => hiSup ▸ hperf P hPN hP) hJ
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · exact ⟨xe, hx, Or.inl ⟨h, hRep.1 hh, hne, hq, hi⟩⟩
  · refine ⟨xe, hx, Or.inr ⟨?_, F i, (hFq i).1, (hFq i).2.1, (hFq i).2.2, hi⟩⟩
    by_contra hlist
    have hn := hFn0 hlist
    have := i.2
    omega

end Components

section Main

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem exists_ne_zero_sq_ne_one' (hK : 4 ≤ Nat.card K) : ∃ l : K, l ≠ 0 ∧ l ^ 2 ≠ 1 := by
  classical
  by_contra h
  push Not at h
  haveI := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := by
    intro l _
    by_cases hl : l = 0
    · simp [hl]
    · rcases sq_eq_one_iff.1 (h l hl) with h1 | h1 <;> simp [h1]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h3 : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
  omega

theorem s2019FixCentralizes_conj_projOrth {q f : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hK : Nat.card K = q ^ f) (hring : ringChar K = q)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (b : ProjOrthDerived Q) (hb : b ^ p = 1) :
    S2019FixCentralizes p (MulAut.conj b) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP K q := hring ▸ ringChar.charP K
  have hq2 : q ≠ 2 := by omega
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K q] at h'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h')
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at h1
      omega
    · exact h0
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ q := by omega
      _ ≤ q ^ f := Nat.le_self_pow (by omega) q
  obtain ⟨l, hl, hl2⟩ := exists_ne_zero_sq_ne_one' hK4
  have hpℓ : p ≠ ringChar K := by rw [hring]; exact hpq
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  intro L hL T₀ hT₀ hLT
  have hperf : ⁅L, L⁆ = L := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hL
  have hle := perfectInLayer_conj_of_equiv hQ hT hp hp2 hpℓ (MulEquiv.refl _) b hb L hL.1 hperf
  obtain ⟨hcomp, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hL hle
  have hcomp' := hcomp
  rw [fixSubgroup_conj_eq_centralizer] at hcomp'
  obtain ⟨x, hx, hcases⟩ := exists_lift_component_cases hp hp2 hQ hT hpℓ b hb L hcomp'
  rcases hcases with ⟨h, hh, hne1, hqs, hLh⟩ | ⟨hlist, F, hFq, hFle, hFn, hLF⟩
  · have hΩ : specialBlock Q x h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hqs.1
        ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    exact commutator_eq_bot_of_cubicPair hq5 hQ hΩ
      (cubicPair_specialBlock hx (hp.odd_of_ne_two hp2) hh hne1 hqs hq hf hK h2 hl hl2) hLh
      hcomp.2.2 hLT hT₀
  · exact commutator_eq_bot_of_cubicPair hq5 hQ (hFle.trans hx.supportedFixedDerived_le_orthDerived)
      (cubicPair_of_fixedFactor hx hlist h2 hFq hFle hFn) hLF hcomp.2.2 hLT hT₀

theorem s2019OrthInner_five : S2019OrthInner (5 ≤ ·) := by
  intro p q hp hp2 hq hq2 hqp hq5 t ht G _ n f hG a ha
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hcard, hring, ⟨e⟩⟩ := exists_projOrth_model_card ht hG
  haveI : Finite G := by
    haveI : Finite V := Module.finite_of_finite K
    haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
    exact Finite.of_equiv _ e.toEquiv.symm
  refine s2019FixCentralizes_of_congr hp e (MulAut.conj a) ?_
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  exact s2019FixCentralizes_conj_projOrth hq hq5 hcard hring hQ hT hp hp2 hqp.symm (e a)
    (by rw [← map_pow, ha, map_one])

theorem s2019FactClassicalOn_orthogonal_of_three (hI3 : S2019OrthInner (· = 3))
    (hD4 : S2019OrthD4Outer) (hSI3 : S2019SympInner (· = 3)) :
    S2019FactClassicalOn .orthogonal :=
  s2019FactClassicalOn_orthogonal s2019OrthInner_five hI3 (s2019OrthOuter _) (s2019OrthOuter _) hD4
    s2019SympInner_five hSI3 (s2019SympOuter _) (s2019SympOuter _)

end Main

end CFSG.LocalAnalysis.GLTheoremA.S2019
