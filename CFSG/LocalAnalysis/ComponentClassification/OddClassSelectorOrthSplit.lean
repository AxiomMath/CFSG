module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthWitness
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentInitial.CentralQuotientComponentLift
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

theorem restrict_component {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] (e : G ≃* G₁ × G₂)
    {L : Subgroup G} (hL : CFSG.IsComponent L) (h2 : ∀ x ∈ L, (e x).2 = 1) :
    ∃ ρ : L →* G₁, Function.Injective ρ ∧ CFSG.IsComponent ρ.range ∧ ∀ x : L, ρ x = (e x).1 := by
  set ρ : L →* G₁ := (MonoidHom.fst G₁ G₂).comp (e.toMonoidHom.comp L.subtype) with hρ
  have hρi : Function.Injective ρ := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact Prod.ext hxy (by rw [h2 x x.2, h2 y y.2])
  have hrange : ρ.range = (L.map e.toMonoidHom).map (MonoidHom.fst G₁ G₂) := by
    rw [hρ, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨ρ, hρi, ⟨?_, ?_⟩, fun _ => rfl⟩
  · exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (MonoidHom.ofInjective hρi)).1 hL.1
  · rw [hrange]
    exact (LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent e hL).2.map
      Prod.fst_surjective

section Split

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem false_of_split {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ finrank K V) {M F : Submodule K V} (hMF : IsCompl M F)
    (horth : ∀ m ∈ M, ∀ f ∈ F, polar Q m f = 0)
    (hMnd : (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate)
    (hFnd : (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate)
    {Y : Subgroup (V ≃ₗ[K] V)} (hYO : Y ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hYF : ∀ y ∈ Y, ∀ f ∈ F, y f = f)
    (ρ : Y →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype))
    (hρi : Function.Injective ρ) (hρc : CFSG.IsComponent ρ.range)
    {A : Type} [Group A] {X : Subgroup A} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X)
    (hN : ∀ t s : V ≃ₗ[K] V,
      t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      t * t = 1 → (∀ c : K, (t : V →ₗ[K] V) ≠ c • LinearMap.id) → (∀ y ∈ Y, y * t = t * y) →
      s * t = t * s → s ∈ normalizer (Y : Set (V ≃ₗ[K] V))) : False := by
  classical
  have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hQM : (Q.comp M.subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hMnd
  have hdimV : finrank K M + finrank K F = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hMF
  have : Nontrivial ρ.range := CFSG.LocalCores.isQuasisimple_nontrivial hρc.1
  rcases Nat.lt_or_ge (finrank K M) 3 with hM | hM
  ·
    have hsol : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype)) :=
      ((CatalogueBOrthogonalAssembly.odd_orthogonal_all_dimensional_isometry_p_components
        hodd (Q.comp M.subtype) hQM).2 (by omega)).1
    exact LocalAnalysis.ComponentInitial.not_isComponent_of_isSolvable _ hρc
  rcases Nat.lt_or_ge (finrank K F) 3 with hF | hF
  ·
    have h5 : 5 ≤ finrank K M := by omega
    have hq := OddSelector.commutator_orthogonalGroup_quasisimple hodd (Q.comp M.subtype) hQM h5
    have hrange : ρ.range = commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype))
      := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hρc hq
    obtain ⟨τ, hτ⟩ := OddSelector.exists_sp_four_hom hodd (Q.comp M.subtype) hQM h5
    have : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
      OddSelector.isPerfect_statedSp le_rfl hodd
    have hτr : ∀ x, τ x ∈ ρ.range := fun x => by
      rw [hrange]
      exact OddSelector.map_mem_commutator_of_isPerfect τ x
    set τ' := τ.codRestrict ρ.range hτr with hτ'
    set ψ := (MonoidHom.ofInjective hρi).symm with hψ
    set σ' := σ.comp (ψ.toMonoidHom.comp τ') with hσ'
    have hker : σ'.ker ≤ center (CFSG.Assembly.LowTwoRank.StatedSp 2 K) := by
      intro x hx
      have h1 : ψ (τ' x) ∈ center Y := hσk hx
      refine hτ x fun y => ?_
      have h2 := mem_center_iff.mp h1 (ψ (τ' y))
      have h3 : τ' y * τ' x = τ' x * τ' y := ψ.injective (by rw [map_mul, map_mul]; exact h2)
      exact congrArg Subtype.val h3
    exact false_of_smallSource hs
      (OddSelector.not_small_source_of_sp_cover le_rfl hℓ hℓ2 he hK σ' hker)
  ·
    have hY1 := eq_one_of_normalizer hk2 hMF horth hMnd hFnd hM hF hYO hYF hN
    obtain ⟨⟨_, ⟨y, rfl⟩⟩, hy⟩ := exists_ne (1 : ρ.range)
    apply hy
    apply Subtype.ext
    change ρ y = 1
    have : y = 1 := Subtype.ext (hY1 y y.2)
    rw [this, map_one]

theorem orth_split_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) (b : Kˣ)
    (hb : (d : K) = (b : K) ^ 2) (hμ : (μ : K) / (d : K) = 1)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X)
    (hN : ∀ t s : V ≃ₗ[K] V,
      t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      t * t = 1 → (∀ c : K, (t : V →ₗ[K] V) ≠ c • LinearMap.id) → (∀ y ∈ Y, y * t = t * y) →
      s * t = t * s → s ∈ normalizer (Y : Set (V ≃ₗ[K] V))) : False := by
  classical
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A d μ hsquare hsim hnonscalar
  obtain ⟨hc, -, -, hpos, -⟩ := hsq b hb
  obtain ⟨horth, hndP, hndN, E, hE1, hE2, -⟩ := hpos hμ
  have hYO : Y ≤ (TauCeti.QuadraticMap.orthogonalGroup Q) := hY.1.trans inf_le_left
  have hY₂ : CFSG.Assembly.IsComponentOf
      (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype)
      (orthogonalOperatorCentralizer Q A.toLinearMap) := by
    have h := isComponentOf_comap_of_le_range (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective hY
      (by rw [Subgroup.range_subtype]; exact inf_le_left)
    have hC : ((TauCeti.QuadraticMap.orthogonalGroup Q) ⊓
        CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap).comap
          (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
        (orthogonalOperatorCentralizer Q A.toLinearMap) := by
      rw [Subgroup.comap_inf]
      have hOO : (TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = ⊤ :=
        Subgroup.subgroupOf_self (TauCeti.QuadraticMap.orthogonalGroup Q)
      rw [hOO, top_inf_eq]
      rfl
    rwa [hC] at h
  have hY₁ : CFSG.IsComponent
      ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hY₂.1).mp hY₂
  set eY : ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (orthogonalOperatorCentralizer Q A.toLinearMap)) ≃* Y :=
    (Subgroup.subgroupOfEquivOfLe hY₂.1).trans (Subgroup.subgroupOfEquivOfLe hYO) with heY
  have heYv : ∀ x : (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (orthogonalOperatorCentralizer Q A.toLinearMap),
      ((eY x : Y) : V ≃ₗ[K] V) = ((x : (orthogonalOperatorCentralizer Q A.toLinearMap)) :
        (TauCeti.QuadraticMap.orthogonalGroup Q)).val := fun _ => rfl
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      (LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent E hY₁) with h2 | h1
  ·
    have h2' : ∀ x ∈ (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap), (E x).2 = 1 := fun x hx =>
      h2 _ (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component E hY₁ h2'
    have hYF : ∀ y ∈ Y, ∀ f ∈ (negativeSquareKernel A b), y f = f := by
      intro y hy f hf
      set x : (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap) := eY.symm ⟨y, hy⟩
      have hx : ((x : (orthogonalOperatorCentralizer Q A.toLinearMap)) :
          (TauCeti.QuadraticMap.orthogonalGroup Q)).val = y := by
        have := heYv x
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm
      have h3 := hE2 (x : (orthogonalOperatorCentralizer Q A.toLinearMap)) ⟨f, hf⟩
      rw [h2' x x.2] at h3
      rw [← hx]
      exact h3.symm
    refine false_of_split hℓ hℓ2 he hK hd hc horth hndP hndN hYO hYF
      (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσk hs hN
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
      ← MonoidHom.range_eq_map]
    exact hρ₁c
  ·
    set E' := E.trans (MulEquiv.prodComm) with hE'
    have h1' : ∀ x ∈ (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap), (E' x).2 = 1 := fun x hx =>
      h1 _ (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component E' hY₁ h1'
    have hYF : ∀ y ∈ Y, ∀ f ∈ (positiveSquareKernel A b), y f = f := by
      intro y hy f hf
      set x : (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap) := eY.symm ⟨y, hy⟩
      have hx : ((x : (orthogonalOperatorCentralizer Q A.toLinearMap)) :
          (TauCeti.QuadraticMap.orthogonalGroup Q)).val = y := by
        have := heYv x
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm
      have h3 := hE1 (x : (orthogonalOperatorCentralizer Q A.toLinearMap)) ⟨f, hf⟩
      have h4 : (E x).1 = 1 := h1' x x.2
      rw [h4] at h3
      rw [← hx]
      exact h3.symm
    have horth' : ∀ m ∈ (negativeSquareKernel A b), ∀ f ∈ (positiveSquareKernel A b),
        polar Q m f = 0 := fun m hm f hf => by
      rw [polar_comm]
      exact horth f hf m hm
    refine false_of_split hℓ hℓ2 he hK hd hc.symm horth' hndN hndP hYO hYF
      (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσk hs hN
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
      ← MonoidHom.range_eq_map]
    exact hρ₁c

end Split

end CFSG.ComponentClassification.OddClassSelector
