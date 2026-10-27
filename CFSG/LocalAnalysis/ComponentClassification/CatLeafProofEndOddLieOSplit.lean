module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthPaired
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthUnitary

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddO

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.OddClassSelector
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem dims_of_component {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) {M : Submodule K V}
    (hMnd : (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate)
    {Y : Subgroup (V ≃ₗ[K] V)} (ρ : Y →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype))
    (hρi : Function.Injective ρ) (hρc : CFSG.IsComponent ρ.range)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : 3 ≤ finrank K M ∧ finrank K M ≤ 4 := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hQM : (Q.comp M.subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hMnd
  constructor
  · by_contra hM
    have hsol : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype)) :=
      ((CatalogueBOrthogonalAssembly.odd_orthogonal_all_dimensional_isometry_p_components
        hodd (Q.comp M.subtype) hQM).2 (by omega)).1
    exact LocalAnalysis.ComponentInitial.not_isComponent_of_isSolvable _ hρc
  · by_contra hM
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

theorem split_reduce {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (c μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V)) (b : Kˣ)
    (hb : (c : K) = (b : K) ^ 2) (hμ : (μ : K) / (c : K) = 1)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) :
    ∃ (s : K) (M F : Submodule K V), (s = b ∨ s = -b) ∧
      M = Module.End.eigenspace A.toLinearMap s ∧
      F = Module.End.eigenspace A.toLinearMap (-s) ∧ IsCompl M F ∧
      (∀ m ∈ M, ∀ f ∈ F, polar Q m f = 0) ∧
      (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate ∧
      (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate ∧
      (∀ y ∈ Y, ∀ f ∈ F, y f = f) ∧
      ∃ ρ : Y →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype),
        Function.Injective ρ ∧ CFSG.IsComponent ρ.range ∧
        (∀ (y : Y) (m : M), (((ρ y).val m : M) : V) = (y : V ≃ₗ[K] V) m) ∧
        3 ≤ finrank K M ∧ finrank K M ≤ 4 := by
  classical
  have hb0 : (b : K) ≠ 0 := b.ne_zero
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A c μ hsquare hsim hnonscalar
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
  have heYv : ∀ y : Y, (y : V ≃ₗ[K] V) =
      (((eY.symm y : (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap)) :
          orthogonalOperatorCentralizer Q A.toLinearMap) :
            TauCeti.QuadraticMap.orthogonalGroup Q).val := by
    intro y
    have h : ((eY (eY.symm y) : Y) : V ≃ₗ[K] V) = _ := rfl
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      (LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent E hY₁) with h2 | h1
  ·
    have h2' : ∀ x ∈ (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap), (E x).2 = 1 := fun x hx =>
      h2 _ (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨ρ₁, hρ₁i, hρ₁c, hρ₁⟩ := restrict_component E hY₁ h2'
    have hρc : CFSG.IsComponent (ρ₁.comp eY.symm.toMonoidHom).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    have hdims := dims_of_component hℓ hℓ2 he hK hndP (ρ₁.comp eY.symm.toMonoidHom)
      (hρ₁i.comp eY.symm.injective) hρc σ hσk hs
    refine ⟨b, positiveSquareKernel A b, negativeSquareKernel A b, Or.inl rfl,
      positiveSquareKernel_eq A b hb0, negativeSquareKernel_eq A b hb0, hc, horth, hndP, hndN,
      ?_, ρ₁.comp eY.symm.toMonoidHom, hρ₁i.comp eY.symm.injective, hρc, ?_, hdims⟩
    · intro y hy f hf
      have h3 := hE2 (eY.symm ⟨y, hy⟩ : orthogonalOperatorCentralizer Q A.toLinearMap) ⟨f, hf⟩
      rw [h2' _ (eY.symm ⟨y, hy⟩).2] at h3
      have h5 : y = _ := heYv ⟨y, hy⟩
      rw [h5]
      exact h3.symm
    · intro y m
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hρ₁, hE1, heYv y]
  ·
    set E' := E.trans (MulEquiv.prodComm) with hE'
    have h1' : ∀ x ∈ (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap), (E' x).2 = 1 := fun x hx =>
      h1 _ (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨ρ₁, hρ₁i, hρ₁c, hρ₁⟩ := restrict_component E' hY₁ h1'
    have hρc : CFSG.IsComponent (ρ₁.comp eY.symm.toMonoidHom).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    have hdims := dims_of_component hℓ hℓ2 he hK hndN (ρ₁.comp eY.symm.toMonoidHom)
      (hρ₁i.comp eY.symm.injective) hρc σ hσk hs
    have horth' : ∀ m ∈ (negativeSquareKernel A b), ∀ f ∈ (positiveSquareKernel A b),
        polar Q m f = 0 := fun m hm f hf => by
      rw [polar_comm]
      exact horth f hf m hm
    refine ⟨-b, negativeSquareKernel A b, positiveSquareKernel A b, Or.inr rfl,
      negativeSquareKernel_eq A b hb0, by rw [neg_neg]; exact positiveSquareKernel_eq A b hb0,
      hc.symm, horth', hndN, hndP, ?_, ρ₁.comp eY.symm.toMonoidHom,
      hρ₁i.comp eY.symm.injective, hρc, ?_, hdims⟩
    · intro y hy f hf
      have h3 := hE1 (eY.symm ⟨y, hy⟩ : orthogonalOperatorCentralizer Q A.toLinearMap) ⟨f, hf⟩
      have h4 : (E (eY.symm ⟨y, hy⟩ : orthogonalOperatorCentralizer Q A.toLinearMap)).1 = 1 :=
        h1' _ (eY.symm ⟨y, hy⟩).2
      rw [h4] at h3
      have h5 : y = _ := heYv ⟨y, hy⟩
      rw [h5]
      exact h3.symm
    · intro y m
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hρ₁]
      change (((E _).2.val m : negativeSquareKernel A b) : V) = _
      rw [hE2, heYv y]

theorem split_data_of_component {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (c : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V))
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X) :
    ∃ (s : K) (M F : Submodule K V), s * s = 1 ∧
      M = Module.End.eigenspace A.toLinearMap s ∧
      F = Module.End.eigenspace A.toLinearMap (-s) ∧ IsCompl M F ∧
      (∀ m ∈ M, ∀ f ∈ F, polar Q m f = 0) ∧
      (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate ∧
      (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate ∧
      (∀ y ∈ Y, ∀ f ∈ F, y f = f) ∧
      ∃ ρ : Y →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype),
        Function.Injective ρ ∧ CFSG.IsComponent ρ.range ∧
        (∀ (y : Y) (m : M), (((ρ y).val m : M) : V) = (y : V ≃ₗ[K] V) m) ∧
        3 ≤ finrank K M ∧ finrank K M ≤ 4 := by
  classical
  have hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = ((1 : Kˣ) : K) * Q.polarBilin x y := by
    intro x y
    rw [Units.val_one, one_mul, polarBilin_apply_apply, polarBilin_apply_apply]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hAO x y
  obtain ⟨hpm, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A c 1 hsquare hsim hnonscalar
  have hc1 : ((1 : Kˣ) : K) / (c : K) = 1 → (c : K) = 1 := fun h => by
    rw [Units.val_one] at h
    exact ((div_eq_one_iff_eq c.ne_zero).mp h).symm
  by_cases hsq : IsSquare (c : K)
  · obtain ⟨b0, hb0⟩ := hsq
    have hb00 : b0 ≠ 0 := by
      rintro rfl
      exact Units.ne_zero c (by rw [hb0, mul_zero])
    have hb : (c : K) = ((Units.mk0 b0 hb00 : Kˣ) : K) ^ 2 := by
      rw [Units.val_mk0, hb0, _root_.sq]
    rcases hpm with h1 | h1
    · obtain ⟨s, M, F, hsb, hrest⟩ :=
        split_reduce hℓ hℓ2 he hK hd hQ A c 1 hsquare hsim hnonscalar _ hb h1 hY σ hσk hs
      have hbb : ((Units.mk0 b0 hb00 : Kˣ) : K) * ((Units.mk0 b0 hb00 : Kˣ) : K) = 1 := by
        rw [Units.val_mk0, ← hb0, hc1 h1]
      refine ⟨s, M, F, ?_, hrest⟩
      rcases hsb with rfl | rfl
      · exact hbb
      · rw [neg_mul_neg]
        exact hbb
    · exact (orth_paired_false hℓ hℓ2 he hK hd hQ A c 1 hsquare hsim hnonscalar _ hb h1 hY σ
        hσk hs).elim
  · rcases hpm with h1 | h1
    · exact absurd ⟨1, by rw [hc1 h1, one_mul]⟩ hsq
    · exact (orth_unitary_false hℓ hℓ2 he hK hd hQ A c 1 hsquare hsim hnonscalar hsq h1 hY σ
        hσs hσk hs).elim

end CFSG.ComponentClassification.CatLeafProof.EndOddO
