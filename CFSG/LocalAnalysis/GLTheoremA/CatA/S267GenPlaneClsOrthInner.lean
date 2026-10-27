module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsSpOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsOrthSplit
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.RankThree.PartOne.F106.OddRadOrthInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Module Polynomial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Open (StatedLieTag StatedClassicalModel)

section Fixed

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private noncomputable def commutatorEquivOrthDerived {W : Type} [AddCommGroup W] [Module K W]
    (R : QuadraticForm K W) :
    ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≃* ↥(orthDerived R) :=
  (Subgroup.equivMapOfInjective _ (TauCeti.QuadraticMap.orthogonalGroup R).subtype
    (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))

theorem exists_fixedFactors_normal (hx : OddOrderIsometry Q p x) (hp : Odd p)
    (hodd : Odd (Nat.card K)) :
    ∃ (n : ℕ) (F : Fin n → Subgroup (V ≃ₗ[K] V)),
      (∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
        ((F i).subgroupOf (supportedFixedDerived Q x)).Normal) ∧
      (FixedLayerListed Q x → ⨆ i, F i = supportedFixedDerived Q x) ∧
      (¬ FixedLayerListed Q x → n = 0) ∧
      ∀ i, ∀ c ∈ isometryCentralizer Q x, LinearEquiv.det c = 1 →
        ∀ g ∈ F i, c * g * c⁻¹ ∈ F i := by
  classical
  by_cases hlist : FixedLayerListed Q x
  swap
  · exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun h => absurd h hlist, fun _ => rfl,
      fun i => i.elim0⟩
  have hQW := hx.polarBilin_fixed_nondegenerate
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hone : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) →
      ∃ (n : ℕ) (F : Fin n → Subgroup (V ≃ₗ[K] V)),
        (∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
          ((F i).subgroupOf (supportedFixedDerived Q x)).Normal) ∧
        (FixedLayerListed Q x → ⨆ i, F i = supportedFixedDerived Q x) ∧
        (¬ FixedLayerListed Q x → n = 0) ∧
        ∀ i, ∀ c ∈ isometryCentralizer Q x, LinearEquiv.det c = 1 →
          ∀ g ∈ F i, c * g * c⁻¹ ∈ F i := by
    intro hq
    refine ⟨1, fun _ => supportedFixedDerived Q x, fun _ => ⟨hq, le_rfl, ?_⟩, fun _ => iSup_const,
      fun h => absurd hlist h, fun _ c hc _ g hg => hx.conj_mem_supportedFixedDerived hc hg⟩
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hone' : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype))) → _ := fun hq =>
    hone (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutatorEquivOrthDerived _).trans (supportedFixedDerivedEquiv hx).symm) hq)
  by_cases hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0
  · exact hone (hx.isQuasisimple_supportedFixedDerived hT)
  have h6 : finrank K (fixedSpace x) ≤ 6 :=
    (finite_odd_quadratic_low_Witt_dimension_bound hodd _ hQW).2.2 hT
  have h3 := hlist.1
  have hne := hlist.2
  have hcase : (Odd (Nat.card K) ∧ (finrank K (fixedSpace x) = 3 ∨
        finrank K (fixedSpace x) = 4 ∨ finrank K (fixedSpace x) = 5)) ∨
      (Odd (Nat.card K) ∧ finrank K (fixedSpace x) = 6 ∧
        ¬ ∃ T : Submodule K (fixedSpace x), finrank K T = 3 ∧
          ∀ y ∈ T, (Q.comp (fixedSpace x).subtype) y = 0) ∨
      (finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
        ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0) := by
    by_cases hd6 : finrank K (fixedSpace x) = 6
    · exact Or.inr (Or.inl ⟨hodd, hd6, hT⟩)
    · exact Or.inl ⟨hodd, by omega⟩
  obtain ⟨-, -, h3d, h4s, h4n, h5d, h6d⟩ :=
    orthogonal_low_dimensional_fixed_derived_component_coverage _ hQW hcase
  have hK2 : Nat.card K ≠ 2 := fun h => by
    rw [h] at hodd
    exact Nat.not_even_iff_odd.mpr hodd even_two
  rcases (show finrank K (fixedSpace x) = 3 ∨ finrank K (fixedSpace x) = 4 ∨
      finrank K (fixedSpace x) = 5 ∨ finrank K (fixedSpace x) = 6 by omega)
    with hd | hd | hd | hd
  ·
    obtain ⟨_, _, _, -, -, -, hq⟩ := h3d hodd hd fun hK => hne (Or.inl ⟨hd, hK⟩)
    exact hone' hq
  · by_cases hsplit : ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
        ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0
    ·
      obtain ⟨ψ, e, -, he, hcomm_eq, hqL, hqR, hnL, hnR, -⟩ :=
        h4s hd hsplit hK2 fun hK => hne (Or.inr ⟨⟨hd, hsplit⟩, Or.inr hK⟩)
      have hsup : (⨆ i, splitFourFactors e i) = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace x).subtype)) := by
        rw [hcomm_eq]
        refine le_antisymm (iSup_le fun i => ?_) (sup_le ?_ ?_)
        · fin_cases i
          · exact le_sup_left
          · exact le_sup_right
        · exact le_iSup (splitFourFactors e) 0
        · exact le_iSup (splitFourFactors e) 1
      have hLle : ∀ i, splitFourFactors e i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace x).subtype)) := fun i => hsup ▸ le_iSup (splitFourFactors e) i
      have hL : ∀ i, CFSG.IsQuasisimple ↥(splitFourFactors e i) ∧
          splitFourFactors e i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
            (Q.comp (fixedSpace x).subtype)) ∧
          ((splitFourFactors e i).subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
            (Q.comp (fixedSpace x).subtype)))).Normal := by
        intro i
        fin_cases i
        · exact ⟨hqL, hLle 0, hnL⟩
        · exact ⟨hqR, hLle 1, hnR⟩
      obtain ⟨hsupF, hF⟩ := supportedFactor_family hx (splitFourFactors e) hsup hL
      exact ⟨2, fun i => supportedFactor hx (splitFourFactors e i), hF, fun _ => hsupF,
        fun h => absurd hlist h, fun i c hc hdet g hg =>
          conj_mem_supportedFactor_splitFour hx hp h2 he hc hdet i hg⟩
    ·
      obtain ⟨_, -, _, _, _, -, -, -, hq⟩ := h4n hodd hd hsplit
      exact hone' hq
  ·
    obtain ⟨_, _, _, -, -, -, hq⟩ := h5d hodd hd
    exact hone' hq
  ·
    obtain ⟨_, _, _, _, _, -, -, -, hq⟩ := h6d hodd hd hT
    exact hone' hq

end Fixed

section Components

open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks (exists_solvable_comm_le
  perfect_le_of_le_sup_solvable)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (isComponentOf_of_normal_normal)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (component_mem_named_factors)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem component_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (x : ↥(orthDerived Q))
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep) {n : ℕ}
    {F : Fin n → Subgroup (V ≃ₗ[K] V)}
    (hFq : ∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
      ((F i).subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal)
    (hFsup : FixedLayerListed Q (x : V ≃ₗ[K] V) →
      ⨆ i, F i = supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn0 : ¬ FixedLayerListed Q (x : V ≃ₗ[K] V) → n = 0)
    {J : Subgroup (ProjOrthDerived Q)}
    (hJ : CFSG.Open.IsComponentOf J (centralizerImage Q (x : V ≃ₗ[K] V))) :
    (∃ r ∈ Rep, r ≠ X - 1 ∧ J = componentImage Q (x : V ≃ₗ[K] V) r) ∨
      ∃ i, J = ((F i).subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
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
  rcases i with ⟨⟨h, hh⟩, hne, -⟩ | i
  · exact Or.inl ⟨h, hh, hne, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

private theorem center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_right fun h => ?_
  obtain ⟨a, b, hab⟩ := hna
  have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.mp ha b).symm

private theorem fixSubgroup_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem compNormal_conj_projOrth {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    (hodd : Odd (Nat.card K)) (a : ProjOrthDerived Q) (hca : MulAut.conj a ^ p = 1)
    (ha1 : a ≠ 1) : CompNormal (MulAut.conj a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hcenter, hZ2, hsimple, hnonab, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have ha : a ^ p = 1 := by
    have hc : a ^ p ∈ Subgroup.center (ProjOrthDerived Q) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut (ProjOrthDerived Q) => φ g)
        (show MulAut.conj (a ^ p) = 1 by rw [map_pow]; exact hca)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h1]
        _ = a ^ p * g := by group
    haveI := hsimple
    rw [center_eq_bot_of_simple hnonab, Subgroup.mem_bot] at hc
    exact hc
  obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a (orderOf_eq_prime ha ha1)
  have hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V) := oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxp
  have hxp1 : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨n, F, hFq, hFsup, hFn0, hFnorm⟩ :=
    exists_fixedFactors_normal hx (hp.odd_of_ne_two hp2) hodd
  let Fm : ↥Rep ⊕ Fin n → Subgroup ↥(orthDerived Q) :=
    Sum.elim (fun r => (specialBlock Q (x : V ≃ₗ[K] V) r.1).subgroupOf (orthDerived Q))
      (fun i => (F i).subgroupOf (orthDerived Q))
  refine compNormal_of_lift (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
    (QuotientGroup.mk'_surjective _) (MulAut.conj x) (MulAut.conj a) (fun g => ?_) (p := p)
    (by rw [← map_pow, hxp1, map_one]) (fun z hz => ?_) (fun z hz hzp => ?_) Fm
    (fun i c hc g hg => ?_) (fun J hJ => ?_)
  ·
    simp only [MulAut.conj_apply, map_mul, map_inv, QuotientGroup.mk'_apply, hxa]
  ·
    rw [QuotientGroup.ker_mk', ← hcenter] at hz
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp hz x, mul_inv_cancel_right]
  ·
    rw [QuotientGroup.ker_mk'] at hz
    have h1 : orderOf z ∣ Nat.card ((scalars K V).subgroupOf (orthDerived Q)) :=
      Subgroup.orderOf_dvd_natCard _ hz
    have hle := Nat.le_of_dvd Nat.card_pos h1
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hzp) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      have := hp.two_le
      omega
  ·
    have hcx : c * x = x * c := by
      have h := mem_fixSubgroup.mp hc
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hcI : (c : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) :=
      Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup c.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcx)⟩
    have hdet : LinearEquiv.det (c : V ≃ₗ[K] V) = 1 := by
      have h1 : orthDerived Q ≤ commutator (V ≃ₗ[K] V) :=
        Subgroup.commutator_mono le_top le_top
      exact MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker LinearEquiv.det (h1 c.2))
    rcases i with r | i
    · exact Subgroup.mem_subgroupOf.mpr
        (conj_mem_specialBlock hcI (Subgroup.mem_subgroupOf.mp hg))
    · exact Subgroup.mem_subgroupOf.mpr (hFnorm i _ hcI hdet _ (Subgroup.mem_subgroupOf.mp hg))
  ·
    have hfix : fixSubgroup (MulAut.conj a) = centralizerImage Q (x : V ≃ₗ[K] V) := by
      rw [fixSubgroup_conj_eq_centralizer, hcent]
      exact map_centralizer_eq_centralizerImage x
    rw [hfix] at hJ
    rcases component_cases hp hp2 hQ x hx hRep hFq hFsup hFn0 hJ with ⟨r, hr, -, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨Sum.inl ⟨r, hr⟩, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩

end Components

section Model

private theorem congr_conj {S G : Type*} [Group S] [Group G] (e : S ≃* G) (a : S) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
  ext y
  simp [MulAut.conj_apply]

private theorem exists_projOrth_model {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      Nat.card K = ℓ ^ f ∧ ringChar K = ℓ ∧ Nonempty (G ≃* ProjOrthDerived Q) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h3 : 3 ≤ n ∧ ℓ ≠ 2 := hadm.2.2
    have hring : ringChar K = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two (by rw [hring]; exact hadm.1), hring]
      exact h3.2
    obtain ⟨hQ, hT⟩ := regular_quadOdd (K := K) (n := n) h2 h3.1
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      hring, ⟨e.trans (statedProjOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadOdd n K))⟩⟩
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar K = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := regular_quadPlus (K := K) (n := n) (by omega)
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      hring, ⟨e.trans (statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n) (K := K)))⟩⟩
  · obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar K = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := regular_quadMinus (K := K) (n := n) h4 hirr
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      hring, ⟨e.trans (statedProjOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c))⟩⟩

theorem compNormal_conj_omega {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hℓ2 : ℓ ≠ 2) (hpℓ : p ≠ ℓ) (a : G)
    (ha : MulAut.conj a ^ p = 1) (ha1 : a ≠ 1) : CompNormal (MulAut.conj a) := by
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hcard, hring, ⟨e⟩⟩ := exists_projOrth_model ht hG
  have hℓ : ℓ.Prime := by
    rw [← hring]
    exact CharP.char_is_prime K (ringChar K)
  have hodd : Odd (Nat.card K) := by
    rw [hcard]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  refine CompNormal.of_congr e ?_
  rw [congr_conj]
  exact compNormal_conj_projOrth hp hp2 hQ hT (hring ▸ hpℓ) hodd (e a)
    (by rw [← congr_conj, ← map_pow, ha, map_one])
    fun h => ha1 (e.injective (h.trans (map_one e).symm))

end Model

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
