module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
public import CFSG.RankThree.PartOne.KFOUT3.CycUnits
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSpBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Fixed
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open scoped Classical

open Polynomial CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.GroupActions CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms

theorem range_le_commutator_of_commutator_eq_top {P H : Type*} [Group P] [Group H]
    (hP : commutator P = ⊤) (φ : P →* H) : φ.range ≤ commutator H := by
  have h1 : φ.range = (commutator P).map φ := by
    rw [hP, MonoidHom.range_eq_map]
  rw [h1, map_commutator_eq]
  exact Subgroup.commutator_mono le_top le_top

theorem range_le_innAutDerived_of_perfect {P G : Type*} [Group P] [Group G]
    (hP : commutator P = ⊤) (φ : P →* MulAut G) : φ.range ≤ innAutDerived G :=
  (range_le_commutator_of_commutator_eq_top hP φ).trans (commutator_le_innAutDerived G)

theorem range_centerQuotientHom_comp_le_innAutDerived {P G : Type*} [Group P] [Group G]
    (hP : commutator P = ⊤) (φ : P →* MulAut G) :
    ((centerQuotientHom G).comp φ).range ≤
      innAutDerived (G ⧸ Subgroup.center G) :=
  range_le_innAutDerived_of_perfect hP ((centerQuotientHom G).comp φ)

theorem eq_X_sub_one_or_X_sq_add_X_add_one_of_dvd_X_pow_three_sub_one {K : Type} [Field K]
    [Finite K] (hK8 : Nat.card K = 8) {h : K[X]} (hirr : Irreducible h) (hmon : h.Monic)
    (hdvd : h ∣ X ^ 3 - 1) : h = X - 1 ∨ h = X ^ 2 + X + 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [Fintype.card_eq_nat_card, hK8]; norm_num)
  have h3 : ¬ 3 ∣ Nat.card K - 1 := by rw [hK8]; norm_num
  have hirr₀ : Irreducible (X ^ 2 + X + 1 : K[X]) :=
    CFSG.RankThree.PartOne.KFOUT3.irreducible_quad (K := K) h3
  by_cases hX : h = X - 1
  · exact Or.inl hX
  right
  have hdvd' : h ∣ X ^ 3 - C 1 := by simpa using hdvd
  have hdvd₂ : h ∣ X ^ 2 + X + 1 :=
    CFSG.AGLEmbedding.ToralCensus.dvd_X_sq_add_X_add_one hirr hmon hdvd' hX
  exact CFSG.AGLEmbedding.ToralCensus.eq_of_dvd_of_natDegree_eq_two hirr₀
    CFSG.AGLEmbedding.ToralCensus.monic_X_sq_add_X_add_one (dvd_refl _)
    CFSG.AGLEmbedding.ToralCensus.natDegree_X_sq_add_X_add_one hirr hmon hdvd₂

theorem primaryFactor_eq_X_sq_add_X_add_one_of_card_eq_eight {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) (hK8 : Nat.card K = 8) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    h = X ^ 2 + X + 1 ∧ reciprocalPolynomial h = h := by
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hdvd : h ∣ X ^ 3 - 1 := by
    have := hx.dvd_X_pow_sub_one hh
    rwa [show (X ^ 3 - 1 : K[X]) = X ^ 3 - C 1 by rw [map_one]] at this
  rcases eq_X_sub_one_or_X_sq_add_X_add_one_of_dvd_X_pow_three_sub_one hK8 hirr hmon hdvd with
    h1 | h1
  · exact absurd h1 hne
  · exact ⟨h1, by rw [h1, CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one]⟩

theorem exists_component_dichotomy {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (centralizerImage Q (x : V ≃ₗ[K] V))) :
    (∃ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
        J = componentImage Q (x : V ≃ₗ[K] V) h) ∨
      (FixedLayerListed Q (x : V ≃ₗ[K] V) ∧ ∃ F : Subgroup (V ≃ₗ[K] V),
        CFSG.IsQuasisimple ↥F ∧ F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
        (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal ∧
        J = (F.subgroupOf (orthDerived Q)).map
          (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
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
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_solvable_comm_le hQ hp hp2 x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left
        (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.perfect_le_of_le_sup_solvable
      hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
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
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · have hh' : h ∈ primaryFactors xe.toLinearMap := hRep.1 hh
    exact Or.inl ⟨h, hh', hne, hq, rfl⟩
  · have hn : n ≠ 0 := fun h0 => by subst h0; exact i.elim0
    have hlist : FixedLayerListed Q xe := by
      by_contra h
      exact hn (hFn0 h)
    exact Or.inr ⟨hlist, F i, (hFq i).1, (hFq i).2.1, (hFq i).2.2, rfl⟩

private theorem blockComponent_fixed_apply {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {y : V ≃ₗ[K] V} (hy : y ∈ isometryCentralizer Q x)
    (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
    (hv : v ∈ primaryComponent x.toLinearMap a) :
    ((CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 : V ≃ₗ[K] V) v = if a = X - 1 then y v else v := by
  classical
  have hrec : reciprocalPolynomial (X - 1 : K[X]) = X - 1 := reciprocalPolynomial_X_sub_one
  have h := blockComponent_apply_of_mem hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩ (X - 1) ha hv
  simpa [hrec] using h

private theorem blockComponent_fixed_pow_three {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {y : V ≃ₗ[K] V} (hy : y ∈ isometryCentralizer Q x)
    (hy3 : y ^ 3 = 1) :
    ((CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 : V ≃ₗ[K] V) ^ 3 = 1 := by
  classical
  set yW : V ≃ₗ[K] V := (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx
    ⟨y, (Subgroup.mem_inf.mp hy).2⟩ (X - 1)).1 with hyW
  have hyW_apply : ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a), yW v = if a = X - 1 then y v else v :=
    fun a ha v hv => blockComponent_fixed_apply hx hy a ha v hv
  have hmap : ((yW ^ 3 : V ≃ₗ[K] V) : V →ₗ[K] V) = 1 := by
    apply ext_primaryComponent hx.squarefree_minpoly
    intro a ha v hv
    have hyv : y v ∈ primaryComponent x.toLinearMap a :=
      apply_mem_primaryComponent_of_mem_centralizer (Subgroup.mem_inf.mp hy).2 hv
    have hyvv : y (y v) ∈ primaryComponent x.toLinearMap a :=
      apply_mem_primaryComponent_of_mem_centralizer (Subgroup.mem_inf.mp hy).2 hyv
    have hy3v : y (y (y v)) = v := by
      have := congrArg (fun e : V ≃ₗ[K] V => e v) hy3
      simpa [pow_succ, LinearEquiv.mul_apply] using this
    change yW (yW (yW v)) = v
    by_cases haX : a = X - 1
    · rw [hyW_apply a ha v hv, if_pos haX, hyW_apply a ha (y v) hyv, if_pos haX,
        hyW_apply a ha (y (y v)) hyvv, if_pos haX, hy3v]
    · rw [hyW_apply a ha v hv, if_neg haX, hyW_apply a ha v hv, if_neg haX,
        hyW_apply a ha v hv, if_neg haX]
  exact LinearEquiv.ext fun v => by
    have := congrArg (fun f : V →ₗ[K] V => f v) hmap
    simpa using this

private theorem blockComponent_fixed_inv_apply {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) {y : V ≃ₗ[K] V}
    (hy : y ∈ isometryCentralizer Q x) (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap)
    (v : V) (hv : v ∈ primaryComponent x.toLinearMap a) :
    ((CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 : V ≃ₗ[K] V)⁻¹ v = if a = X - 1 then y⁻¹ v else v := by
  classical
  set yW : V ≃ₗ[K] V := (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx
    ⟨y, (Subgroup.mem_inf.mp hy).2⟩ (X - 1)).1 with hyW
  have hyW_apply : ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a), yW v = if a = X - 1 then y v else v :=
    fun a ha v hv => blockComponent_fixed_apply hx hy a ha v hv
  have hyinv : y⁻¹ v ∈ primaryComponent x.toLinearMap a :=
    apply_mem_primaryComponent_of_mem_centralizer (Subgroup.mem_inf.mp (inv_mem hy)).2 hv
  by_cases haX : a = X - 1
  · apply yW.injective
    rw [if_pos haX]
    change yW (yW.symm v) = yW (y.symm v)
    rw [yW.apply_symm_apply, hyW_apply a ha (y.symm v) hyinv, if_pos haX]
    exact (y.apply_symm_apply v).symm
  · apply yW.injective
    rw [if_neg haX]
    change yW (yW.symm v) = yW v
    rw [yW.apply_symm_apply, hyW_apply a ha v hv, if_neg haX]

private theorem blockComponent_fixed_conj_eq {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {y : V ≃ₗ[K] V} (hy : y ∈ isometryCentralizer Q x)
    {f : V ≃ₗ[K] V} (hf : f ∈ supportedBlock Q x (X - 1 : K[X])) :
    y * f * y⁻¹ =
      (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
        (X - 1)).1 * f *
        ((CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx
          ⟨y, (Subgroup.mem_inf.mp hy).2⟩ (X - 1)).1)⁻¹ := by
  classical
  set yW : V ≃ₗ[K] V := (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx
    ⟨y, (Subgroup.mem_inf.mp hy).2⟩ (X - 1)).1 with hyW
  have hyW_apply : ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a), yW v = if a = X - 1 then y v else v :=
    fun a ha v hv => blockComponent_fixed_apply hx hy a ha v hv
  have hyWinv_apply : ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a), yW⁻¹ v = if a = X - 1 then y⁻¹ v else v :=
    fun a ha v hv => blockComponent_fixed_inv_apply hx hy a ha v hv
  have hmap : (((y * f * y⁻¹ : V ≃ₗ[K] V)) : V →ₗ[K] V) =
      (((yW * f * yW⁻¹ : V ≃ₗ[K] V)) : V →ₗ[K] V) := by
    apply ext_primaryComponent hx.squarefree_minpoly
    intro a ha v hv
    have hc := supportedBlock_le_centralizer (X - 1) hf
    have hyinv : y⁻¹ v ∈ primaryComponent x.toLinearMap a :=
      apply_mem_primaryComponent_of_mem_centralizer (Subgroup.mem_inf.mp (inv_mem hy)).2 hv
    by_cases haX : a = X - 1
    · have hfmem : f (y⁻¹ v) ∈ primaryComponent x.toLinearMap a :=
        apply_mem_primaryComponent_of_mem_centralizer hc hyinv
      change y (f (y⁻¹ v)) = yW (f (yW⁻¹ v))
      rw [hyWinv_apply a ha v hv, if_pos haX, hyW_apply a ha (f (y⁻¹ v)) hfmem, if_pos haX]
    · have hfv : f (y⁻¹ v) = y⁻¹ v := by
        refine apply_eq_of_mem_supportedBlock hf ha haX ?_ hyinv
        rwa [reciprocalPolynomial_X_sub_one]
      have hyWinv : yW⁻¹ v ∈ primaryComponent x.toLinearMap a := by
        rw [hyWinv_apply a ha v hv, if_neg haX]; exact hv
      have hfW : f (yW⁻¹ v) = yW⁻¹ v := by
        refine apply_eq_of_mem_supportedBlock hf ha haX ?_ hyWinv
        rwa [reciprocalPolynomial_X_sub_one]
      change y (f (y⁻¹ v)) = yW (f (yW⁻¹ v))
      rw [hfv, hfW]
      change y (y.symm v) = yW (yW.symm v)
      exact (y.apply_symm_apply v).trans (yW.apply_symm_apply v).symm
  exact LinearEquiv.ext fun v => by
    have := congrArg (fun f : V →ₗ[K] V => f v) hmap
    simpa using this

theorem centerQuotientHom_mem_innAutDerived_of_fixedFactor {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) (hK8 : Nat.card K = 8)
    (hlist : FixedLayerListed Q x) {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal)
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
    {y : ↥(orthDerived Q)} (hy : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q x)
    (hy3 : y ^ 3 = 1)
    (hJ : MulAut.conj (QuotientGroup.mk'
      ((scalars K V).subgroupOf (orthDerived Q)) y) ∈ CFSG.GroupActions.subgroupStabAut J) :
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥J
      (CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj (QuotientGroup.mk'
          ((scalars K V).subgroupOf (orthDerived Q)) y), hJ⟩) ∈
      innAutDerived (↥J ⧸ Subgroup.center ↥J) := by
  classical
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set P : Subgroup (V ≃ₗ[K] V) := supportedFixedDerived Q x with hP
  have hPle : P ≤ orthDerived Q := hx.supportedFixedDerived_le_orthDerived
  have hy3V : (y : V ≃ₗ[K] V) ^ 3 = 1 := by
    have := congrArg (fun e : ↥(orthDerived Q) => (e : V ≃ₗ[K] V)) hy3
    simpa using this
  have hX1 : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    refine mem_primaryFactors_of_primaryComponent_ne_bot irreducible_X_sub_one
      monic_X_sub_one ?_
    have hpos : 0 < Module.finrank K (primaryComponent x.toLinearMap (X - 1)) := by
      rw [← fixedSpace_eq_primaryComponent (x := x)]
      exact lt_of_lt_of_le (by norm_num) hlist.1
    exact Submodule.nontrivial_iff_ne_bot.mp (Module.finrank_pos_iff.mp hpos)
  set yW : V ≃ₗ[K] V := (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx
    ⟨(y : V ≃ₗ[K] V), (Subgroup.mem_inf.mp hy).2⟩ (X - 1)).1 with hyW
  have hyWblock : yW ∈ supportedBlock Q x (X - 1) :=
    hx.blockComponent_mem hy hX1
  have hyW3 : yW ^ 3 = 1 := blockComponent_fixed_pow_three hx hy hy3V
  have hyWP : yW ∈ P :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_mem_supportedFixedDerived hx
      Nat.prime_three (by norm_num) (by rw [hK8]; norm_num) hlist.1 hyWblock hyW3
  have hPperf : commutator ↥P = ⊤ := by
    haveI : Group.IsPerfect ↥P :=
      CFSG.RankThree.PartOne.KCOrthComm.isPerfect_supportedFixedDerived hx
        (by rw [hK8]; norm_num) hlist.1
    exact Group.IsPerfect.commutator_eq_top
  have hFnorm : ∀ f ∈ F, ∀ p ∈ P, p * f * p⁻¹ ∈ F := fun f hf p hp =>
    (Subgroup.normal_subgroupOf_iff hFle).mp hFn f p hf hp
  have hstab : ∀ p : ↥P, MulAut.conj (ρ ⟨p.1, hPle p.2⟩) ∈
      CFSG.GroupActions.subgroupStabAut J := by
    intro p
    change J.map (MulAut.conj (ρ ⟨p.1, hPle p.2⟩)).toMonoidHom = J
    rw [hJeq]
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      have hbF : (b : V ≃ₗ[K] V) ∈ F := Subgroup.mem_subgroupOf.mp hb
      have hb' : (⟨p.1, hPle p.2⟩ : ↥(orthDerived Q)) * b *
          (⟨p.1, hPle p.2⟩ : ↥(orthDerived Q))⁻¹ ∈ F.subgroupOf (orthDerived Q) :=
        Subgroup.mem_subgroupOf.mpr (hFnorm b hbF p.1 p.2)
      have hconj : MulAut.conj (ρ ⟨p.1, hPle p.2⟩) (ρ b) =
          ρ ((⟨p.1, hPle p.2⟩ : ↥(orthDerived Q)) * b *
            (⟨p.1, hPle p.2⟩ : ↥(orthDerived Q))⁻¹) := by
        rw [MulAut.conj_apply]
        simp only [← map_mul, ← map_inv]
      change MulAut.conj (ρ ⟨p.1, hPle p.2⟩) (ρ b) ∈
        Subgroup.map ρ (F.subgroupOf (orthDerived Q))
      rw [hconj]
      exact Subgroup.mem_map_of_mem ρ hb'
    · rintro ⟨a, ha, rfl⟩
      have haF : (a : V ≃ₗ[K] V) ∈ F := Subgroup.mem_subgroupOf.mp ha
      have ha' : (⟨p.1, hPle p.2⟩ : ↥(orthDerived Q))⁻¹ * a *
          ⟨p.1, hPle p.2⟩ ∈ F.subgroupOf (orthDerived Q) :=
        Subgroup.mem_subgroupOf.mpr (hFnorm a haF p.1⁻¹ (inv_mem p.2))
      refine Subgroup.mem_map.mpr
        ⟨ρ ((⟨p.1, hPle p.2⟩ : ↥(orthDerived Q))⁻¹ * a * ⟨p.1, hPle p.2⟩), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem ρ ha'
      · change MulAut.conj (ρ ⟨p.1, hPle p.2⟩)
          (ρ ((⟨p.1, hPle p.2⟩ : ↥(orthDerived Q))⁻¹ * a * ⟨p.1, hPle p.2⟩)) =
            ρ a
        rw [MulAut.conj_apply]
        simp only [← map_mul, ← map_inv]
        congr 1
        group
  let Ψ : ↥P →* MulAut (ProjOrthDerived Q) :=
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).comp
      (ρ.comp (Subgroup.inclusion hPle))
  let ψ : ↥P →* ↥(CFSG.GroupActions.subgroupStabAut J) :=
    Ψ.codRestrict (CFSG.GroupActions.subgroupStabAut J) (fun p => hstab p)
  have hψ : ∀ p : ↥P, (ψ p : MulAut (ProjOrthDerived Q)) =
      MulAut.conj (ρ ⟨p.1, hPle p.2⟩) := fun p => rfl
  have hconj_eq : ∀ z ∈ J, MulAut.conj (ρ y) z = MulAut.conj (ρ ⟨yW, hPle hyWP⟩) z := by
    intro z hz
    rw [hJeq] at hz
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hz
    have hfF : (f : V ≃ₗ[K] V) ∈ F := Subgroup.mem_subgroupOf.mp hf
    have hfP : (f : V ≃ₗ[K] V) ∈ P := hFle hfF
    have hfSB : (f : V ≃ₗ[K] V) ∈ supportedBlock Q x (X - 1) :=
      supportedFixedDerived_le_supportedBlock hfP
    have hconjf : y * f * y⁻¹ = (⟨yW, hPle hyWP⟩ : ↥(orthDerived Q)) * f *
        (⟨yW, hPle hyWP⟩ : ↥(orthDerived Q))⁻¹ := by
      apply Subtype.ext
      simpa using blockComponent_fixed_conj_eq hx hy hfSB
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simp only [← map_mul, ← map_inv]
    rw [hconjf]
  have hcomp := range_centerQuotientHom_comp_le_innAutDerived hPperf
    ((CFSG.GroupActions.subgroupStabRestrict J).comp ψ)
  refine hcomp ⟨⟨yW, hyWP⟩, ?_⟩
  simp only [MonoidHom.comp_apply]
  congr 1
  ext z
  rw [CFSG.GroupActions.subgroupStabRestrict_apply,
    CFSG.GroupActions.subgroupStabRestrict_apply, hψ]
  exact (hconj_eq z z.2).symm

private theorem exists_selfDual_unitary_model {K V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f (AdjoinRoot h))
      (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h →
        AdjoinRoot h),
      (∀ u w c, Algebra.trace K (AdjoinRoot h) (H u w * c) =
        QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V)) ∧
      ∃ (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
        B.IsSymm ∧ B.SeparatingLeft ∧ (∀ u w, B u w = H u w) ∧
          (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, -, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : Module.finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
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
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  exact ⟨ℓ, f * d, hU, H, hH, B, hBsymm, hBl, hBH, hrange⟩

theorem exists_selfDual_unitary_of_odd {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
      B.IsSymm ∧ B.SeparatingLeft ∧
        (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
  obtain ⟨ℓ, f, hU, -, -, B, hBs, hBl, -, hrange⟩ :=
    exists_selfDual_unitary_model hx hp2 hh hne1 hself
  exact ⟨ℓ, f, hU, B, hBs, hBl, hrange⟩

theorem centralizerGL_mem_sesqUnitaryGroup {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}
    [Fact (Irreducible h)] {ℓ f : ℕ} {hU : UnitaryFieldData ℓ f (AdjoinRoot h)}
    {H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h}
    (hH : ∀ u w c, Algebra.trace K (AdjoinRoot h) (H u w * c) =
      QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    {B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h}
    (hBH : ∀ u w, B u w = H u w)
    {m : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x) :
    centralizerGL x h ⟨m, (Subgroup.mem_inf.mp hm).2⟩ ∈ sesqUnitaryGroup B := by
  classical
  have hmO : m ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (Subgroup.mem_inf.mp hm).1
  have hmc : m ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hm).2
  set γ : BlockGL x h := centralizerGL x h ⟨m, hmc⟩ with hγ
  have hcoe : ∀ v : primaryComponent x.toLinearMap h, ((γ : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) v : V) = m (v : V) := fun v => coe_centralizerGL x h _ v
  refine mem_sesqUnitaryGroup.mpr fun u w => ?_
  refine eq_of_trace_mul_eq (K := K) (E := AdjoinRoot h) fun c => ?_
  have hpol : QuadraticMap.polar Q ((γ : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) u : V)
      ((c • ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w) :
        primaryComponent x.toLinearMap h) : V) =
      QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V) := by
    have hsm : ((c • ((γ : Module.End (AdjoinRoot h)
        (primaryComponent x.toLinearMap h)) w) : primaryComponent x.toLinearMap h) : V) =
        m ((c • w : primaryComponent x.toLinearMap h) : V) := by
      rw [← hcoe (c • w)]
      exact congrArg Subtype.val (LinearMap.map_smul (γ : Module.End (AdjoinRoot h)
        (primaryComponent x.toLinearMap h)) c w).symm
    rw [hcoe u, hsm]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hmO _ _
  rw [hBH, hH, hBH, hH]
  exact hpol

theorem specialBlockGL_conj {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]} (m : V ≃ₗ[K] V)
    (hm : m ∈ isometryCentralizer Q x) (s : ↥(specialBlock Q x h))
    (hms : m * (s : V ≃ₗ[K] V) * m⁻¹ ∈ specialBlock Q x h) :
    specialBlockGL Q x h ⟨m * (s : V ≃ₗ[K] V) * m⁻¹, hms⟩ =
      centralizerGL x h ⟨m, (Subgroup.mem_inf.mp hm).2⟩ *
        specialBlockGL Q x h s *
        (centralizerGL x h ⟨m, (Subgroup.mem_inf.mp hm).2⟩)⁻¹ := by
  have hmc : m ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hm).2
  have hsc : ((s : V ≃ₗ[K] V)) ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    supportedBlock_le_centralizer h (specialBlock_le_supportedBlock h s.2)
  have hmsc : m * (s : V ≃ₗ[K] V) * m⁻¹ ∈
      Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := mul_mem (mul_mem hmc hsc) (inv_mem hmc)
  have hgl : specialBlockGL Q x h ⟨m * (s : V ≃ₗ[K] V) * m⁻¹, hms⟩ =
      centralizerGL x h ⟨m * (s : V ≃ₗ[K] V) * m⁻¹, hmsc⟩ := rfl
  rw [hgl]
  have hconj : (⟨m * (s : V ≃ₗ[K] V) * m⁻¹, hmsc⟩ :
      ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) =
      ⟨m, hmc⟩ * ⟨(s : V ≃ₗ[K] V), hsc⟩ * ⟨m, hmc⟩⁻¹ := Subtype.ext rfl
  rw [hconj, map_mul, map_mul, map_inv]
  have hs : centralizerGL x h ⟨(s : V ≃ₗ[K] V), hsc⟩ = specialBlockGL Q x h s := rfl
  rw [hs]

theorem exists_sesqSUConjData {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : ↥(orthDerived Q)}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) (hp2 : Odd p) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hq : CFSG.Open.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (y : ↥(orthDerived Q)) (hy : (y : V ≃ₗ[K] V) ∈
      isometryCentralizer Q (x : V ≃ₗ[K] V))
    (J : Subgroup (orthDerived Q ⧸ (scalars K V).subgroupOf (orthDerived Q)))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
    (hJ : MulAut.conj (QuotientGroup.mk' (N := (scalars K V).subgroupOf (orthDerived Q)) y) ∈
        CFSG.GroupActions.subgroupStabAut J) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f (AdjoinRoot h))
      (B : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h →ₛₗ[hU.bar]
        primaryComponent (x : V ≃ₗ[K] V).toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
      B.IsSymm ∧ B.SeparatingLeft ∧
        commutator ↥(sesqSpecialUnitaryGroup B) = ⊤ ∧
        ∃ (g : ↥(sesqUnitaryGroup B))
          (π' : ↥(sesqSpecialUnitaryGroup B) →* ↥J),
          Function.Surjective π' ∧ π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup B) ∧
          ∀ s : ↥(sesqSpecialUnitaryGroup B),
            CFSG.GroupActions.subgroupStabRestrict J
              ⟨MulAut.conj (QuotientGroup.mk'
                (N := (scalars K V).subgroupOf (orthDerived Q)) y), hJ⟩ (π' s) =
              π' (sesqSUConj g s) := by
  classical
  let ρ : ↥(orthDerived Q) →*
      (orthDerived Q ⧸ (scalars K V).subgroupOf (orthDerived Q)) :=
    QuotientGroup.mk' (N := (scalars K V).subgroupOf (orthDerived Q))
  let xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V)
  let A : Subgroup ↥(orthDerived Q) := (specialBlock Q xe h).subgroupOf (orthDerived Q)
  have hleQ : specialBlock Q xe h ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer h hg)).1
  have hleOrth : specialBlock Q xe h ≤ orthDerived Q := by
    haveI : Group.IsPerfect ↥(specialBlock Q xe h) := ⟨hq.1⟩
    calc specialBlock Q xe h = ⁅specialBlock Q xe h, specialBlock Q xe h⁆ :=
          (Subgroup.commutator_eq_self).symm
      _ ≤ orthDerived Q := Subgroup.commutator_mono hleQ hleQ
  have hAJ : A.map ρ = J := by
    rw [hJeq]
    rfl
  obtain ⟨ℓ, f, hU, H, hH, B, hBsymm, hBl, hBH, hrange⟩ :=
    exists_selfDual_unitary_model hx hp2 hh hne1 hself
  have hgin : centralizerGL xe h ⟨(y : V ≃ₗ[K] V),
      (Subgroup.mem_inf.mp hy).2⟩ ∈ sesqUnitaryGroup B :=
    centralizerGL_mem_sesqUnitaryGroup hH hBH hy
  let g : ↥(sesqUnitaryGroup B) := ⟨centralizerGL xe h ⟨(y : V ≃ₗ[K] V),
    (Subgroup.mem_inf.mp hy).2⟩, hgin⟩
  let e : ↥(specialBlock Q xe h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  let e₀ : ↥(specialBlock Q xe h) ≃* ↥A := (Subgroup.subgroupOfEquivOfLe hleOrth).symm
  let π₀ : ↥A →* ↥J :=
    (MulEquiv.subgroupCongr hAJ).toMonoidHom.comp (ρ.subgroupMap A)
  have hker₀ : π₀.ker ≤ Subgroup.center ↥A := by
    intro a ha
    have h2 : (ρ.subgroupMap A) a = 1 := by
      have h := congrArg (MulEquiv.subgroupCongr hAJ).symm ha
      simpa [π₀, ρ] using h
    have h3 : QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
        (a : ↥(orthDerived Q)) = 1 := congrArg Subtype.val h2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp h3)
    rw [Subgroup.mem_center_iff]
    intro b
    refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))
    change (b : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v) = (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v)
    rw [hc v, hc, map_smul]
  let π' : ↥(sesqSpecialUnitaryGroup B) →* ↥J :=
    π₀.comp (e.symm.trans e₀).toMonoidHom
  have hπ₀ : Function.Surjective π₀ :=
    (MulEquiv.subgroupCongr hAJ).surjective.comp (ρ.subgroupMap_surjective A)
  have hπ'surj : Function.Surjective π' :=
    hπ₀.comp (e.symm.trans e₀).surjective
  have hπ'ker : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup B) := by
    intro s hs
    have h1 : (e.symm.trans e₀) s ∈ π₀.ker := hs
    have h2 : (e.symm.trans e₀) s ∈ Subgroup.center ↥A := hker₀ h1
    have h3 : (Subgroup.center ↥A) =
        (Subgroup.center ↥(sesqSpecialUnitaryGroup B)).map
          (e.symm.trans e₀ : ↥(sesqSpecialUnitaryGroup B) →* ↥A) :=
      (Subgroup.map_center_eq (e.symm.trans e₀)).symm
    rw [h3] at h2
    obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp h2
    exact (e.symm.trans e₀).injective hze ▸ hz
  haveI : Group.IsPerfect ↥(specialBlock Q xe h) := ⟨hq.1⟩
  haveI : Group.IsPerfect ↥(sesqSpecialUnitaryGroup B) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hSUperf : commutator ↥(sesqSpecialUnitaryGroup B) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  refine ⟨ℓ, f, hU, B, hBsymm, hBl, hSUperf, g, π', hπ'surj, hπ'ker, ?_⟩
  intro s
  set s' : ↥(specialBlock Q xe h) := e.symm s with hs'
  have hes : e s' = s := e.apply_symm_apply s
  have hgls : specialBlockGL Q xe h s' = (s : BlockGL xe h) := by
    rw [← hes]
    rfl
  have hms : (y : V ≃ₗ[K] V) * (s' : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V)⁻¹ ∈
      specialBlock Q xe h := conj_mem_specialBlock hy s'.2
  have hconj := specialBlockGL_conj (Q := Q) (x := xe) (h := h)
    (y : V ≃ₗ[K] V) hy s' hms
  have hconj' : specialBlockGL Q xe h ⟨(y : V ≃ₗ[K] V) * (s' : V ≃ₗ[K] V) *
      (y : V ≃ₗ[K] V)⁻¹, hms⟩ = (g : BlockGL xe h) * (s : BlockGL xe h) *
        (g : BlockGL xe h)⁻¹ := by
    rw [hconj, hgls]
  have heconj : e ⟨(y : V ≃ₗ[K] V) * (s' : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V)⁻¹, hms⟩ =
      sesqSUConj g s := by
    apply Subtype.ext
    rw [sesqSUConj_apply]
    exact hconj'
  have hesymm : e.symm (sesqSUConj g s) =
      ⟨(y : V ≃ₗ[K] V) * (s' : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V)⁻¹, hms⟩ := by
    rw [← heconj, e.symm_apply_apply]
  refine Subtype.ext ?_
  rw [CFSG.GroupActions.subgroupStabRestrict_apply]
  show (ρ y) * (π' s : ProjOrthDerived Q) * (ρ y)⁻¹ = (π' _ : ProjOrthDerived Q)
  have hπs : (π' s : ProjOrthDerived Q) = ρ (e₀ s' : ↥(orthDerived Q)) := rfl
  have hπc : (π' (sesqSUConj g s) : ProjOrthDerived Q) =
      ρ (e₀ (e.symm (sesqSUConj g s)) : ↥(orthDerived Q)) := rfl
  rw [hπs, hπc, hesymm]
  have hcoe₀ : ∀ a : ↥(specialBlock Q xe h),
      ((e₀ a : ↥A) : ↥(orthDerived Q)) = ⟨a.1, hleOrth a.2⟩ := fun a => rfl
  rw [hcoe₀, hcoe₀]
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
