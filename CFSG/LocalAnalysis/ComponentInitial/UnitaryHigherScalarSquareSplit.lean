module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareEigen
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

theorem nondegenerate_domRestrict_of_orth (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {W₁ W₂ : Submodule K V} (hc : IsCompl W₁ W₂) (horth : ∀ v ∈ W₁, ∀ w ∈ W₂, B v w = 0) :
    (B.domRestrict₁₂ W₁ W₁).Nondegenerate := by
  have hleft : ∀ x : W₁, (∀ y : W₁, B (x : V) (y : V) = 0) → x = 0 := by
    intro x hx
    refine Subtype.ext (hBnd.1 (x : V) fun w => ?_)
    obtain ⟨y, z, hy, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
    rw [map_add, horth x x.2 z hz, add_zero]
    exact hx ⟨y, hy⟩
  refine ⟨fun x hx => hleft x hx, fun y hy => hleft y fun x => ?_⟩
  exact bilin_eq_zero_swap hB (hy x)

theorem exists_bilin_split_equiv (h2 : (2 : K) ≠ 0) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} {l : K} (hl0 : l ≠ 0)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = (l ^ 2) • 1)
    (hTB : ∀ v w, B (invSMulOp l (A : Module.End K V) v) (invSMulOp l (A : Module.End K V) w) =
      B v w) :
    (∀ v ∈ eigenPlus l (A : Module.End K V), ∀ w ∈ eigenMinus l (A : Module.End K V),
      B v w = 0) ∧
    (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
      (eigenPlus l (A : Module.End K V))).IsAlt ∧
    (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
      (eigenMinus l (A : Module.End K V))).IsAlt ∧
    (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
      (eigenPlus l (A : Module.End K V))).Nondegenerate ∧
    (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
      (eigenMinus l (A : Module.End K V))).Nondegenerate ∧
    ∃ e : similitudeCentralizer B A ≃*
        sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
          (eigenPlus l (A : Module.End K V))) ×
        sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
          (eigenMinus l (A : Module.End K V))),
      ∀ g : similitudeCentralizer B A,
        (eigenPlus l (A : Module.End K V)).subtype ∘ₗ
            (((e g).1 : LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V))) :
              Module.End K (eigenPlus l (A : Module.End K V))) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ
            (eigenPlus l (A : Module.End K V)).subtype ∧
        (eigenMinus l (A : Module.End K V)).subtype ∘ₗ
            (((e g).2 : LinearMap.GeneralLinearGroup K (eigenMinus l (A : Module.End K V))) :
              Module.End K (eigenMinus l (A : Module.End K V))) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ
            (eigenMinus l (A : Module.End K V)).subtype := by
  obtain ⟨A', hA'⟩ : ∃ A' : Module.End K V, A' = (A : Module.End K V) := ⟨_, rfl⟩
  rw [← hA'] at hAA hTB ⊢
  have hc : IsCompl (eigenPlus l A') (eigenMinus l A') :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA)
  have horth : ∀ v ∈ eigenPlus l A', ∀ w ∈ eigenMinus l A', B v w = 0 :=
    fun v hv w hw => bilin_eq_zero_of_eigen_one h2 hTB hv hw
  have horth' : ∀ v ∈ eigenMinus l A', ∀ w ∈ eigenPlus l A', B v w = 0 :=
    fun v hv w hw => bilin_eq_zero_swap hB (horth w hw v hv)
  have hWp : ∀ g ∈ similitudeCentralizer B A, ∀ v ∈ eigenPlus l A',
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ eigenPlus l A' :=
    fun g hg v hv => by
      rw [hA'] at hv ⊢
      exact mapsTo_eigenPlus_of_mem l hg hv
  have hWm : ∀ g ∈ similitudeCentralizer B A, ∀ v ∈ eigenMinus l A',
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ eigenMinus l A' :=
    fun g hg v hv => by
      rw [hA'] at hv ⊢
      exact mapsTo_eigenMinus_of_mem l hg hv
  have hmemP : ∀ g : similitudeCentralizer B A, subgroupRestrictHom _ hWp g ∈
      sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l A') (eigenPlus l A')) :=
    fun g x y => (g.2.1 : _) x y
  have hmemM : ∀ g : similitudeCentralizer B A, subgroupRestrictHom _ hWm g ∈
      sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l A') (eigenMinus l A')) :=
    fun g x y => (g.2.1 : _) x y
  obtain ⟨φ, hφ⟩ : ∃ φ : similitudeCentralizer B A →*
      sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l A') (eigenPlus l A')) ×
        sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l A') (eigenMinus l A')),
      φ = ((subgroupRestrictHom _ hWp).codRestrict _ hmemP).prod
        ((subgroupRestrictHom _ hWm).codRestrict _ hmemM) := ⟨_, rfl⟩
  have hinj : Function.Injective φ := by
    intro g g' hgg'
    rw [hφ] at hgg'
    have h1 := congrArg Prod.fst hgg'
    have h3 := congrArg Prod.snd hgg'
    refine Subtype.ext (Units.ext (endo_ext_of_isCompl hc (fun x hx => ?_) (fun x hx => ?_)))
    · exact congrArg (fun u : sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l A')
        (eigenPlus l A')) => ((((u : LinearMap.GeneralLinearGroup K (eigenPlus l A')) :
          Module.End K (eigenPlus l A')) ⟨x, hx⟩ : eigenPlus l A') : V)) h1
    · exact congrArg (fun u : sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l A')
        (eigenMinus l A')) => ((((u : LinearMap.GeneralLinearGroup K (eigenMinus l A')) :
          Module.End K (eigenMinus l A')) ⟨x, hx⟩ : eigenMinus l A') : V)) h3
  have hsurj : Function.Surjective φ := by
    rintro ⟨g₁, g₂⟩
    obtain ⟨G, hG⟩ : ∃ G : LinearMap.GeneralLinearGroup K V,
        G = glOfIsCompl hc (g₁ : LinearMap.GeneralLinearGroup K (eigenPlus l A'))
          (g₂ : LinearMap.GeneralLinearGroup K (eigenMinus l A')) := ⟨_, rfl⟩
    have hGl : ∀ x (hx : x ∈ eigenPlus l A'), (G : Module.End K V) x =
        (((g₁ : LinearMap.GeneralLinearGroup K (eigenPlus l A')) :
          Module.End K (eigenPlus l A')) ⟨x, hx⟩ : V) := fun x hx => by
      rw [hG]
      exact glOfIsCompl_apply_left hc _ _ ⟨x, hx⟩
    have hGr : ∀ x (hx : x ∈ eigenMinus l A'), (G : Module.End K V) x =
        (((g₂ : LinearMap.GeneralLinearGroup K (eigenMinus l A')) :
          Module.End K (eigenMinus l A')) ⟨x, hx⟩ : V) := fun x hx => by
      rw [hG]
      exact glOfIsCompl_apply_right hc _ _ ⟨x, hx⟩
    have hGU : G ∈ sesqUnitaryGroup B := by
      intro v w
      obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
      obtain ⟨x', y', hx', hy', rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
      have i1 := g₁.2 ⟨x, hx⟩ ⟨x', hx'⟩
      have i2 := g₂.2 ⟨y, hy⟩ ⟨y', hy'⟩
      simp only [LinearMap.domRestrict₁₂_apply] at i1 i2
      simp only [map_add, LinearMap.add_apply]
      rw [hGl x hx, hGr y hy, hGl x' hx', hGr y' hy']
      rw [horth _ (((g₁ : LinearMap.GeneralLinearGroup K (eigenPlus l A')) :
          Module.End K (eigenPlus l A')) ⟨x, hx⟩).2 _
          (((g₂ : LinearMap.GeneralLinearGroup K (eigenMinus l A')) :
          Module.End K (eigenMinus l A')) ⟨y', hy'⟩).2,
        horth' _ (((g₂ : LinearMap.GeneralLinearGroup K (eigenMinus l A')) :
          Module.End K (eigenMinus l A')) ⟨y, hy⟩).2 _
          (((g₁ : LinearMap.GeneralLinearGroup K (eigenPlus l A')) :
          Module.End K (eigenPlus l A')) ⟨x', hx'⟩).2,
        horth x hx y' hy', horth' y hy x' hx', i1, i2]
    have hGC : G ∈ similitudeCentralizer B A := by
      refine ⟨hGU, Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext ?_)⟩
      change (G : Module.End K V) * (A : Module.End K V) = (A : Module.End K V) *
        (G : Module.End K V)
      rw [← hA']
      refine commute_of_mapsTo_eigen h2 hl0 hAA (fun v hv => ?_) (fun v hv => ?_)
      · rw [hGl v hv]
        exact (((g₁ : LinearMap.GeneralLinearGroup K (eigenPlus l A')) :
          Module.End K (eigenPlus l A')) ⟨v, hv⟩).2
      · rw [hGr v hv]
        exact (((g₂ : LinearMap.GeneralLinearGroup K (eigenMinus l A')) :
          Module.End K (eigenMinus l A')) ⟨v, hv⟩).2
    refine ⟨⟨G, hGC⟩, ?_⟩
    rw [hφ]
    refine Prod.ext (Subtype.ext (Units.ext (LinearMap.ext fun x => Subtype.ext ?_)))
      (Subtype.ext (Units.ext (LinearMap.ext fun x => Subtype.ext ?_)))
    · exact hGl x x.2
    · exact hGr x x.2
  have hrestrictAlt : ∀ W : Submodule K V, (B.domRestrict₁₂ W W).IsAlt := fun W x => hB x
  refine ⟨horth, hrestrictAlt _, hrestrictAlt _,
    nondegenerate_domRestrict_of_orth hB hBnd hc horth,
    nondegenerate_domRestrict_of_orth hB hBnd hc.symm horth',
    MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun g => ⟨LinearMap.ext fun v => ?_,
      LinearMap.ext fun v => ?_⟩⟩
  · change ((((φ g).1 : LinearMap.GeneralLinearGroup K (eigenPlus l A')) :
      Module.End K (eigenPlus l A')) v : V) = _
    rw [hφ]
    rfl
  · change ((((φ g).2 : LinearMap.GeneralLinearGroup K (eigenMinus l A')) :
      Module.End K (eigenMinus l A')) v : V) = _
    rw [hφ]
    rfl

theorem bilin_finrank_le_of_pairing [FiniteDimensional K V] {W₁ W₂ : Submodule K V}
    (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0) : finrank K W₂ ≤ finrank K W₁ := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W₂ →ₗ[K] (W₁ →ₗ[K] K),
      Ψ = (LinearMap.lcomp K K W₁.subtype) ∘ₗ B ∘ₗ W₂.subtype := ⟨_, rfl⟩
  have hΨapp : ∀ (w : W₂) (v : W₁), Ψ w v = B (w : V) (v : V) := fun w v => by rw [hΨ]; rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine Subtype.ext (hpair _ w.2 fun v hv => ?_)
    rw [← hΨapp w ⟨v, hv⟩, hw, LinearMap.zero_apply]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Subspace.dual_finrank_eq] at this

theorem exists_bilin_dual_action [FiniteDimensional K V] (hB : B.IsAlt) {W₁ W₂ : Submodule K V}
    (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0) (hdim : finrank K W₂ = finrank K W₁)
    (gp : LinearMap.GeneralLinearGroup K W₁) :
    ∃ gn : LinearMap.GeneralLinearGroup K W₂, ∀ (x : W₁) (y : W₂),
      B (((gp : Module.End K W₁) x : W₁) : V) (((gn : Module.End K W₂) y : W₂) : V) =
        B (x : V) (y : V) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W₂ →ₗ[K] (W₁ →ₗ[K] K),
      Ψ = (LinearMap.lcomp K K W₁.subtype) ∘ₗ B ∘ₗ W₂.subtype := ⟨_, rfl⟩
  have hΨapp : ∀ (w : W₂) (v : W₁), Ψ w v = B (w : V) (v : V) := fun w v => by rw [hΨ]; rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine Subtype.ext (hpair _ w.2 fun v hv => ?_)
    rw [← hΨapp w ⟨v, hv⟩, hw, LinearMap.zero_apply]
  have hdim' : finrank K W₂ = finrank K (W₁ →ₗ[K] K) := by
    rw [Subspace.dual_finrank_eq, hdim]
  obtain ⟨e, he⟩ : ∃ e : W₂ ≃ₗ[K] (W₁ →ₗ[K] K), e = LinearEquiv.ofBijective Ψ
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hinj⟩ :=
    ⟨_, rfl⟩
  have heΨ : ∀ w, e w = Ψ w := fun w => by rw [he]; rfl
  obtain ⟨θ, hθ⟩ : ∃ θ : W₂ →ₗ[K] (W₁ →ₗ[K] K),
      θ = (LinearMap.lcomp K K ((gp⁻¹ : LinearMap.GeneralLinearGroup K W₁) :
        Module.End K W₁)) ∘ₗ Ψ := ⟨_, rfl⟩
  have hθapp : ∀ (y : W₂) (v : W₁), θ y v =
      B (y : V) ((((gp⁻¹ : LinearMap.GeneralLinearGroup K W₁) : Module.End K W₁) v : W₁) : V) :=
    fun y v => by rw [hθ]; exact hΨapp y _
  obtain ⟨gmap, hgmap⟩ : ∃ gmap : Module.End K W₂, gmap = e.symm.toLinearMap ∘ₗ θ := ⟨_, rfl⟩
  have hspec : ∀ (y : W₂) (v : W₁), B ((gmap y : W₂) : V) (v : V) = θ y v := fun y v => by
    rw [← hΨapp, ← heΨ, hgmap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  have hgmapinj : Function.Injective gmap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    refine Subtype.ext (hpair _ y.2 fun v hv => ?_)
    have h1 := hspec y (((gp : LinearMap.GeneralLinearGroup K W₁) : Module.End K W₁) ⟨v, hv⟩)
    rw [hy, Submodule.coe_zero, map_zero, LinearMap.zero_apply, hθapp, ← Module.End.mul_apply,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply] at h1
    exact h1.symm
  obtain ⟨gmapE, hgmapE⟩ := (⟨LinearEquiv.ofInjectiveEndo gmap hgmapinj, rfl⟩ :
    ∃ x : W₂ ≃ₗ[K] W₂, x = LinearEquiv.ofInjectiveEndo gmap hgmapinj)
  refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv K W₂).symm gmapE, fun x y => ?_⟩
  have hy : (((LinearMap.GeneralLinearGroup.generalLinearEquiv K W₂).symm gmapE :
      LinearMap.GeneralLinearGroup K W₂) : Module.End K W₂) y = gmap y := by
    rw [hgmapE]
    rfl
  rw [hy, ← LinearMap.IsAlt.neg hB, hspec, hθapp, ← Module.End.mul_apply, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Module.End.one_apply, LinearMap.IsAlt.neg hB]

theorem exists_bilin_paired_equiv [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {A : LinearMap.GeneralLinearGroup K V} {l : K} (hl0 : l ≠ 0)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = (l ^ 2) • 1)
    (hTB : ∀ v w, B (invSMulOp l (A : Module.End K V) v) (invSMulOp l (A : Module.End K V) w) =
      -B v w) :
    (∀ v ∈ eigenPlus l (A : Module.End K V), ∀ w ∈ eigenPlus l (A : Module.End K V),
      B v w = 0) ∧
    (∀ v ∈ eigenMinus l (A : Module.End K V), ∀ w ∈ eigenMinus l (A : Module.End K V),
      B v w = 0) ∧
    finrank K (eigenPlus l (A : Module.End K V)) = finrank K (eigenMinus l (A : Module.End K V)) ∧
    2 * finrank K (eigenPlus l (A : Module.End K V)) = finrank K V ∧
    (∀ v ∈ eigenPlus l (A : Module.End K V),
      (∀ w ∈ eigenMinus l (A : Module.End K V), B v w = 0) → v = 0) ∧
    (∀ w ∈ eigenMinus l (A : Module.End K V),
      (∀ v ∈ eigenPlus l (A : Module.End K V), B v w = 0) → w = 0) ∧
    ∃ e : similitudeCentralizer B A ≃*
        LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V)),
      (∀ g : similitudeCentralizer B A,
        (eigenPlus l (A : Module.End K V)).subtype ∘ₗ
            ((e g : LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V))) :
              Module.End K (eigenPlus l (A : Module.End K V))) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ
            (eigenPlus l (A : Module.End K V)).subtype) ∧
      (∀ (g : similitudeCentralizer B A) (w : V), w ∈ eigenMinus l (A : Module.End K V) →
        ∀ w' ∈ eigenMinus l (A : Module.End K V),
          ((∀ v ∈ eigenPlus l (A : Module.End K V),
            B (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) w' = B v w) ↔
            w' = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w)) := by
  obtain ⟨A', hA'⟩ : ∃ A' : Module.End K V, A' = (A : Module.End K V) := ⟨_, rfl⟩
  rw [← hA'] at hAA hTB ⊢
  have hc : IsCompl (eigenPlus l A') (eigenMinus l A') :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA)
  have hisoP : ∀ v ∈ eigenPlus l A', ∀ w ∈ eigenPlus l A', B v w = 0 :=
    fun v hv w hw => bilin_eq_zero_of_eigen_neg_plus h2 hTB hv hw
  have hisoM : ∀ v ∈ eigenMinus l A', ∀ w ∈ eigenMinus l A', B v w = 0 :=
    fun v hv w hw => bilin_eq_zero_of_eigen_neg_minus h2 hTB hv hw
  have hpairPM : ∀ v ∈ eigenPlus l A', (∀ w ∈ eigenMinus l A', B v w = 0) → v = 0 := by
    intro v hv h0
    refine hBnd.1 v fun w => ?_
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
    rw [map_add, hisoP v hv x hx, h0 y hy, add_zero]
  have hpairMP : ∀ w ∈ eigenMinus l A', (∀ v ∈ eigenPlus l A', B w v = 0) → w = 0 := by
    intro w hw h0
    refine hBnd.1 w fun v => ?_
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
    rw [map_add, h0 x hx, hisoM w hw y hy, add_zero]
  have hpairMP' : ∀ w ∈ eigenMinus l A', (∀ v ∈ eigenPlus l A', B v w = 0) → w = 0 :=
    fun w hw h0 => hpairMP w hw fun v hv => bilin_eq_zero_swap hB (h0 v hv)
  have hdim : finrank K (eigenPlus l A') = finrank K (eigenMinus l A') :=
    le_antisymm (bilin_finrank_le_of_pairing hpairPM) (bilin_finrank_le_of_pairing hpairMP)
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hWp : ∀ g ∈ similitudeCentralizer B A, ∀ v ∈ eigenPlus l A',
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ eigenPlus l A' :=
    fun g hg v hv => by
      rw [hA'] at hv ⊢
      exact mapsTo_eigenPlus_of_mem l hg hv
  have hWm : ∀ g ∈ similitudeCentralizer B A, ∀ v ∈ eigenMinus l A',
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ eigenMinus l A' :=
    fun g hg v hv => by
      rw [hA'] at hv ⊢
      exact mapsTo_eigenMinus_of_mem l hg hv
  obtain ⟨φ, hφ⟩ : ∃ φ : similitudeCentralizer B A →* LinearMap.GeneralLinearGroup K
      (eigenPlus l A'), φ = subgroupRestrictHom _ hWp := ⟨_, rfl⟩
  have hφapp : ∀ (g : similitudeCentralizer B A) (v : eigenPlus l A'),
      (((φ g : LinearMap.GeneralLinearGroup K (eigenPlus l A')) :
        Module.End K (eigenPlus l A')) v : V) =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
    fun g v => by rw [hφ]; rfl
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr fun g hg => ?_
    have hg1 : ∀ v ∈ eigenPlus l A', ((g : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) v = v := fun v hv => by
      rw [← hφapp g ⟨v, hv⟩, hg]
      rfl
    refine Subtype.ext (Units.ext (endo_ext_of_isCompl hc (fun x hx => hg1 x hx)
      (fun y hy => ?_)))
    change ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) y = y
    have hgy := hWm g g.2 y hy
    refine sub_eq_zero.mp (hpairMP' _ (sub_mem hgy hy) fun v hv => ?_)
    have h1 := (g.2.1 : _) v y
    rw [hg1 v hv] at h1
    rw [map_sub, h1, sub_self]
  have hsurj : Function.Surjective φ := by
    intro gp
    obtain ⟨gn, hgn⟩ := exists_bilin_dual_action hB hpairMP hdim.symm gp
    obtain ⟨G, hG⟩ : ∃ G : LinearMap.GeneralLinearGroup K V, G = glOfIsCompl hc gp gn :=
      ⟨_, rfl⟩
    have hGl : ∀ x (hx : x ∈ eigenPlus l A'), (G : Module.End K V) x =
        (((gp : Module.End K (eigenPlus l A')) ⟨x, hx⟩ : eigenPlus l A') : V) :=
      fun x hx => by rw [hG]; exact glOfIsCompl_apply_left hc _ _ ⟨x, hx⟩
    have hGr : ∀ x (hx : x ∈ eigenMinus l A'), (G : Module.End K V) x =
        (((gn : Module.End K (eigenMinus l A')) ⟨x, hx⟩ : eigenMinus l A') : V) :=
      fun x hx => by rw [hG]; exact glOfIsCompl_apply_right hc _ _ ⟨x, hx⟩
    have hGU : G ∈ sesqUnitaryGroup B := by
      intro v w
      obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
      obtain ⟨x', y', hx', hy', rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
      have i1 := hgn ⟨x, hx⟩ ⟨y', hy'⟩
      have i2 := hgn ⟨x', hx'⟩ ⟨y, hy⟩
      simp only [map_add, LinearMap.add_apply]
      rw [hGl x hx, hGr y hy, hGl x' hx', hGr y' hy',
        hisoP _ ((gp : Module.End K (eigenPlus l A')) ⟨x, hx⟩).2 _
          ((gp : Module.End K (eigenPlus l A')) ⟨x', hx'⟩).2,
        hisoM _ ((gn : Module.End K (eigenMinus l A')) ⟨y, hy⟩).2 _
          ((gn : Module.End K (eigenMinus l A')) ⟨y', hy'⟩).2,
        hisoP x hx x' hx', hisoM y hy y' hy', i1, ← LinearMap.IsAlt.neg hB, i2,
        LinearMap.IsAlt.neg hB]
    have hGC : G ∈ similitudeCentralizer B A := by
      refine ⟨hGU, Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext ?_)⟩
      change (G : Module.End K V) * (A : Module.End K V) = (A : Module.End K V) *
        (G : Module.End K V)
      rw [← hA']
      refine commute_of_mapsTo_eigen h2 hl0 hAA (fun v hv => ?_) (fun v hv => ?_)
      · rw [hGl v hv]
        exact ((gp : Module.End K (eigenPlus l A')) ⟨v, hv⟩).2
      · rw [hGr v hv]
        exact ((gn : Module.End K (eigenMinus l A')) ⟨v, hv⟩).2
    refine ⟨⟨G, hGC⟩, Units.ext (LinearMap.ext fun x => Subtype.ext ?_)⟩
    rw [hφapp]
    exact hGl x x.2
  refine ⟨hisoP, hisoM, hdim, by omega, hpairPM, hpairMP',
    MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun g => LinearMap.ext fun v => hφapp g v,
    fun g w hw w' hw' => ⟨fun H => ?_, ?_⟩⟩
  · have hgw := hWm g g.2 w hw
    refine sub_eq_zero.mp (hpairMP' _ (sub_mem hw' hgw) fun z hz => ?_)
    obtain ⟨u, hu⟩ : ∃ u : V, u = (((g⁻¹ : similitudeCentralizer B A) :
        LinearMap.GeneralLinearGroup K V) : Module.End K V) z := ⟨_, rfl⟩
    have hu' : u ∈ eigenPlus l A' := by
      rw [hu]
      exact hWp _ (inv_mem g.2) z hz
    have hzz : ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) u = z := by
      rw [hu]
      change ((((g : LinearMap.GeneralLinearGroup K V) *
        (g : LinearMap.GeneralLinearGroup K V)⁻¹ : LinearMap.GeneralLinearGroup K V)) :
          Module.End K V) z = z
      rw [mul_inv_cancel]
      rfl
    rw [← hzz, map_sub, H u hu', (g.2.1 : _) u w, sub_self]
  · rintro rfl v _
    exact (g.2.1 : _) v w

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
