module

public import CFSG.GH74.GLS.Stage4.T2F1LocH90
public import CFSG.GH74.GLS.Stage4.T2F1LocCoh
public import CFSG.GH74.GLS.Stage4.T2F1LocDich

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Rest
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

theorem list_prod_range {M : Type} [CommMonoid M] (g : ℕ → M) (r : ℕ) :
    ((List.range r).map g).prod = ∏ i ∈ Finset.range r, g i := by
  induction r with
  | zero => simp
  | succ r ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

section Pow

variable {G : Type} [Group G] {F : Type} [Field F]

theorem conj_pow_map (φ : SL2 F →* G) (f : G) (σ : F ≃+* F)
    (hσ : ∀ M : SL2 F, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M))
    (k : ℕ) (M : SL2 F) :
    f ^ k * φ M * (f ^ k)⁻¹ =
      φ (Matrix.SpecialLinearGroup.map ((σ ^ k : F ≃+* F) : F →+* F) M) := by
  induction k generalizing M with
  | zero =>
    simp only [pow_zero, inv_one, one_mul, mul_one]
    congr 1
  | succ k ih =>
    have e : f ^ (k + 1) * φ M * (f ^ (k + 1))⁻¹ = f * (f ^ k * φ M * (f ^ k)⁻¹) * f⁻¹ := by
      rw [pow_succ']; group
    rw [e, ih, hσ]
    congr 1
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, pow_succ']

@[expose] def dHom (F : Type) [Field F] : Fˣ →* SL2 F where
  toFun := sl2D
  map_one' := sl2D_one
  map_mul' a b := (sl2D_mul a b).symm

theorem dHom_apply (s : Fˣ) : dHom F s = sl2D s := rfl

theorem h90_of_coord [Finite F] {φ : SL2 F →* G} (hφ : Function.Injective φ) {σ : F ≃+* F} {r : ℕ}
    (hr : orderOf σ = r) {f : G}
    (hσ : ∀ M : SL2 F, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M)) :
    ∀ y ∈ (tSub F).map φ,
      ((List.range r).map fun k => f ^ k * y * (f ^ k)⁻¹).prod = 1 →
        ∃ x ∈ (tSub F).map φ, y = x * (f * x * f⁻¹)⁻¹ := by
  rintro y ⟨M, hM, rfl⟩ hprod
  obtain ⟨s, rfl⟩ := mem_tSub.1 hM
  have hk : ∀ k : ℕ, f ^ k * φ (sl2D s) * (f ^ k)⁻¹ =
      (φ.comp (dHom F)) (Units.map ((σ ^ k : F ≃+* F) : F →* F) s) := by
    intro k
    rw [conj_pow_map φ f σ hσ k, map_sl2D]
    rfl
  simp only [hk] at hprod
  set ψ : Fˣ →* G := φ.comp (dHom F) with hψ
  set u : ℕ → Fˣ := fun k => Units.map ((σ ^ k : F ≃+* F) : F →* F) s with hu
  have h1 : ψ ((List.range r).map u).prod = 1 := by
    rw [map_list_prod, List.map_map]; exact hprod
  have h2 : ((List.range r).map u).prod = 1 := by
    have h3 : φ (dHom F ((List.range r).map u).prod) = φ 1 := by
      rw [map_one]; exact h1
    have h4 := hφ h3
    exact t2A_sl2D_injective (by rw [← dHom_apply, h4, ← sl2D_one])
  have h5 : ∏ i ∈ Finset.range r, (σ ^ i) (s : F) = 1 := by
    rw [← list_prod_range (fun i => (σ ^ i) (s : F)) r]
    have := congrArg (Units.coeHom F) h2
    rw [map_list_prod, map_one, List.map_map] at this
    have hfun : (fun i : ℕ => (σ ^ i) (s : F)) = ⇑(Units.coeHom F) ∘ u := rfl
    rw [hfun]
    exact this
  obtain ⟨y', hy0, hy'⟩ := hilbert90_finiteField σ hr h5
  let yu : Fˣ := Units.mk0 y' hy0
  refine ⟨φ (sl2D yu), ⟨sl2D yu, sl2D_mem_tSub yu, rfl⟩, ?_⟩
  have hf' : f * φ (sl2D yu) * f⁻¹ = φ (sl2D (Units.map (σ : F →* F) yu)) := by
    rw [hσ, map_sl2D]
    rfl
  rw [hf', ← map_inv, ← map_mul]
  congr 1
  rw [t2A_sl2D_inv, sl2D_mul]
  congr 1
  apply Units.ext
  have hσy : σ y' ≠ 0 := (map_ne_zero σ).2 hy0
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, yu, Units.val_mk0]
  exact (eq_mul_inv_iff_mul_eq₀ hσy).2 hy'

end Pow

section Fuse

theorem exists_fusion_elt {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} (hSec : Ch6Sec5 N u)
    {f : G} (hf : f ∈ N.F) {r : ℕ} (hr : Odd r) (hfr : f ^ r = 1)
    (hw₁w₂ : N.w₁ * N.w₂ = N.w₂ * N.w₁) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    {φ₁ : SL2 F₁ →* G} (hφ₁ : Function.Injective φ₁) {σ₁ : F₁ ≃+* F₁} (hr₁ : orderOf σ₁ = r)
    (hHK₁ : N.H ⊓ N.K₁ = (tSub F₁).map φ₁)
    (hσ₁ : ∀ M : SL2 F₁, f * φ₁ M * f⁻¹ = φ₁ (Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) M))
    {φ₂ : SL2 F₂ →* G} (hφ₂ : Function.Injective φ₂) {σ₂ : F₂ ≃+* F₂} (hr₂ : orderOf σ₂ = r)
    (hHK₂ : N.H ⊓ N.K₂ = (tSub F₂).map φ₂)
    (hσ₂ : ∀ M : SL2 F₂, f * φ₂ M * f⁻¹ = φ₂ (Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) M)) :
    ∃ a' : G, f * a' = a' * f ∧ a'⁻¹ * N.z * a' = u ∧ a'⁻¹ * u * a' = N.z * u := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have hW := hSec.weyl
  obtain ⟨h₀, hh₀, hfa⟩ := comm_a_mod_H_of_sec hSec hf hr hfr hw₁w₂
  have hzz : N.z * N.z = 1 := by
    have h := pow_orderOf_eq_one N.z
    rw [hLoc.z_ord, sq] at h
    exact h
  have hfH : ∀ x ∈ N.H, f * x * f⁻¹ ∈ N.H := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hF5.F_normH hf) x).1 hx
  have hfK₁ : ∀ x ∈ N.K₁, f * x * f⁻¹ ∈ N.K₁ := by
    have := conj_mem_sup (hF5.F_normX₁ f hf) (hF5.F_normX₁' f hf)
    rw [← hLoc.K₁_eq] at this
    exact this
  have hfK₂ : ∀ x ∈ N.K₂, f * x * f⁻¹ ∈ N.K₂ := by
    have := conj_mem_sup (hF5.F_normX₂ f hf) (hF5.F_normX₂' f hf)
    rw [← hLoc.K₂_eq] at this
    exact this
  have hz₁ : (N.H ⊓ N.K₁) ⊓ (N.H ⊓ N.K₂) ≤ Subgroup.zpowers N.z := fun x hx =>
    hLoc.K_inter ⟨hx.1.2, hx.2.2⟩
  have h90₁ : ∀ y ∈ N.H ⊓ N.K₁, Odd (orderOf y) →
      ((List.range r).map fun k => f ^ k * y * (f ^ k)⁻¹).prod = 1 →
        ∃ x ∈ N.H ⊓ N.K₁, y = x * (f * x * f⁻¹)⁻¹ := by
    intro y hy _ hp
    rw [hHK₁] at hy ⊢
    exact h90_of_coord hφ₁ hr₁ hσ₁ y hy hp
  have h90₂ : ∀ y ∈ N.H ⊓ N.K₂, Odd (orderOf y) →
      ((List.range r).map fun k => f ^ k * y * (f ^ k)⁻¹).prod = 1 →
        ∃ x ∈ N.H ⊓ N.K₂, y = x * (f * x * f⁻¹)⁻¹ := by
    intro y hy _ hp
    rw [hHK₂] at hy ⊢
    exact h90_of_coord hφ₂ hr₂ hσ₂ y hy hp
  obtain ⟨x, hxH, hx⟩ := exists_fixed_in_coset (H := N.H) (H₁ := N.H ⊓ N.K₁) (H₂ := N.H ⊓ N.K₂)
    (a := N.a) (f := f) (z := N.z) (r := r) hLoc.H_comm inf_le_left inf_le_left hLoc.H_idx hzz hz₁
    hfH (fun y hy => ⟨hfH y hy.1, hfK₁ y hy.2⟩) (fun y hy => ⟨hfH y hy.1, hfK₂ y hy.2⟩) hfr hr
    ⟨h₀, hh₀, hfa⟩ h90₁ h90₂
  have hu : N.a⁻¹ * N.z * N.a = u := hSec.u_eq
  have hcyc : N.a⁻¹ * u * N.a = N.z * u := by
    have := hW.a_cycle
    rwa [hSec.u_eq] at this
  refine ⟨N.a * x, ?_, ?_, ?_⟩
  · have : f * (N.a * x) * f⁻¹ * f = N.a * x * f := by rw [hx]
    calc f * (N.a * x) = f * (N.a * x) * f⁻¹ * f := by group
      _ = N.a * x * f := this
  · have hc : x * u = u * x := hLoc.H_comm x hxH u hLoc.u_mem_H
    calc (N.a * x)⁻¹ * N.z * (N.a * x) = x⁻¹ * (N.a⁻¹ * N.z * N.a) * x := by group
      _ = x⁻¹ * u * x := by rw [hu]
      _ = u := by rw [mul_assoc, ← hc]; group
  · have hc : x * (N.z * u) = (N.z * u) * x :=
      hLoc.H_comm x hxH _ (N.H.mul_mem hLoc.z_mem_H hLoc.u_mem_H)
    calc (N.a * x)⁻¹ * u * (N.a * x) = x⁻¹ * (N.a⁻¹ * u * N.a) * x := by group
      _ = x⁻¹ * (N.z * u) * x := by rw [hcyc]
      _ = N.z * u := by rw [mul_assoc, ← hc]; group

end Fuse

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
