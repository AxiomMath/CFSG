module

public import CFSG.GH74.GLS.IVK.Prod32.CaPart
public import CFSG.GH74.GLS.IVK.Prod32.Compat

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass squareClassMap)
open CFSG.GH74.GLS.IVK.Lifted (gammaOf slFieldAut slFieldAut_apply)
open scoped commutatorElement

section Transport

variable {F : Type} [Field F] [Finite F]


theorem outHom_conj (hF : GoodF F) (β α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    outHom hF (β⁻¹ * α * β) = outHom hF α := by
  have : IsCyclic (F ≃+* F) := CFSG.ABGDGroups.isCyclic_ringEquiv F
  have hcomm : ∀ x y : SquareClass F × (F ≃+* F), x * y = y * x := by
    intro x y
    refine Prod.ext (mul_comm _ _) ?_
    exact (IsCyclic.isMulCommutative (α := F ≃+* F)).is_comm.comm _ _
  rw [map_mul, map_mul, map_inv, mul_assoc, hcomm (outHom hF α), inv_mul_cancel_left]

end Transport

section TransportH

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}
  {F : Type} [Field F] [Finite F]

@[expose] noncomputable def swapEquiv (hS : Setting H K₁ K₂ z) {t : H}
    (htN : t ∉ normalizer (K₁ : Set H)) : ↥K₂ ≃* ↥K₁ where
  toFun y := ⟨t⁻¹ * y * t, by
    have hN' : t⁻¹ ∉ normalizer (K₁ : Set H) := fun h => htN (by simpa using Subgroup.inv_mem _ h)
    have := hS.conj_mem_swap₂ hN' y.2
    simpa using this⟩
  invFun x := ⟨t * x * t⁻¹, hS.conj_mem_swap₁ htN x.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' y y' := Subtype.ext (by simp [mul_assoc])

theorem swapEquiv_apply (hS : Setting H K₁ K₂ z) {t : H} (htN : t ∉ normalizer (K₁ : Set H))
    (y : ↥K₂) : ((swapEquiv hS htN y : ↥K₁) : H) = t⁻¹ * y * t := rfl

theorem exists_twist (h : Hyp H K₁ K₂ z T a) (ê₁ : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F)
    {σ : F ≃+* F} (hact : SLAct K₁ a ê₁ σ) (hσ : σ ≠ 1) {a' : H}
    (ha'N : a' ∈ normalizer (K₁ : Set H)) (ha'2 : a' * a' = 1) (hk : a' * a ∈ K₁ ⊔ K₂) :
    ∃ β : MulAut (SpecialLinearGroup (Fin 2) F),
      β⁻¹ * MulAut.congr ê₁ (K₁.normalizerMonoidHom ⟨a', ha'N⟩) * β = slFieldAut σ := by
  have hS := h.setting
  set α' : MulAut (SpecialLinearGroup (Fin 2) F) :=
    MulAut.congr ê₁ (K₁.normalizerMonoidHom ⟨a', ha'N⟩) with hα'
  obtain ⟨k₁, hk₁, k₂, hk₂, hkk⟩ := (mem_sup_of_comm hS.comm _).mp hk
  have haa := h.a_inv
  have ha'eq : a' = (k₁ * k₂) * a⁻¹ := by rw [← hkk]; group
  have hα'b : ∀ b : SpecialLinearGroup (Fin 2) F,
      α' b = ê₁ ⟨k₁, hk₁⟩ * slFieldAut σ b * (ê₁ ⟨k₁, hk₁⟩)⁻¹ := by
    intro b
    set u : ↥K₁ := ê₁.symm b with hu
    have hu1 : a * (u : H) * a⁻¹ ∈ K₁ := hact.norm _ u.2
    have h2 : a' * (u : H) * a'⁻¹ = k₁ * (a * (u : H) * a⁻¹) * k₁⁻¹ := by
      have hc := hS.comm (a * (u : H) * a⁻¹) hu1 k₂ hk₂
      rw [ha'eq]
      calc k₁ * k₂ * a⁻¹ * ↑u * (k₁ * k₂ * a⁻¹)⁻¹
          = k₁ * (k₂ * (a⁻¹ * ↑u * a) * k₂⁻¹) * k₁⁻¹ := by group
        _ = k₁ * (a * ↑u * a⁻¹) * k₁⁻¹ := by
          have h3 : a⁻¹ * (u : H) * a = a * (u : H) * a⁻¹ := by rw [haa]
          rw [h3]
          have h4 : k₂ * (a * ↑u * a⁻¹) * k₂⁻¹ = a * ↑u * a⁻¹ := by
            rw [← hc]; group
          rw [h4]
    have h1 : α' b = ê₁ (⟨k₁, hk₁⟩ * ⟨a * u * a⁻¹, hu1⟩ * ⟨k₁, hk₁⟩⁻¹) := by
      rw [hα', congr_apply_eq]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, InvMemClass.coe_inv]
      exact h2
    rw [h1, map_mul, map_mul, map_inv, hact.act u hu1, hu, MulEquiv.apply_symm_apply]
  have hrep : ∀ b : SpecialLinearGroup (Fin 2) F, SpecialLinearGroup.toGL (α' b) =
      SpecialLinearGroup.toGL (ê₁ ⟨k₁, hk₁⟩) *
        GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) *
          (SpecialLinearGroup.toGL (ê₁ ⟨k₁, hk₁⟩))⁻¹ := by
    intro b
    rw [hα'b b, map_mul, map_mul, map_inv, slFieldAut_apply,
      CFSG.Semidihedral.MatrixCoverData.toGL_field_map F σ b]
    rfl
  have hout := outHom_of_rep hF hrep
  have hdet : Matrix.GeneralLinearGroup.det (SpecialLinearGroup.toGL (ê₁ ⟨k₁, hk₁⟩)) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact (ê₁ ⟨k₁, hk₁⟩).det_coe
  rw [hdet, map_one] at hout
  have hσ' : (gammaOf hF.odd hF.gt3 α').right = σ := by
    rw [← outHom_snd hF, hout]
  have hα2 : α' * α' = 1 := by
    have := congr_sq ê₁ ha'N K₁.one_mem (p := 1) (fun y hy => by
      have h1 := ha'2
      calc a' * (a' * y * a'⁻¹) * a'⁻¹ = (a' * a') * y * (a' * a')⁻¹ := by group
        _ = 1 * y * 1⁻¹ := by rw [h1])
    rw [hα', this]
    have h1 : ê₁ ⟨1, K₁.one_mem⟩ = 1 := by
      have : (⟨1, K₁.one_mem⟩ : ↥K₁) = 1 := rfl
      rw [this, map_one]
    rw [h1, map_one]
  obtain ⟨β, hβ⟩ := CFSG.GH74.GLS.IVK.Lifted.exists_conj_slFieldAut hF.odd hF.gt3 α' hα2
    (by rw [hσ']; exact hσ)
  exact ⟨β, by rw [hσ'] at hβ; exact hβ⟩

theorem exists_transport (h : Hyp H K₁ K₂ z T a) (ê₁ : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F)
    (hF : GoodF F) {σ : F ≃+* F} (hact : SLAct K₁ a ê₁ σ) (hσ : σ ≠ 1) {t : H}
    (htN : t ∉ normalizer (K₁ : Set H)) (hV' : (t⁻¹ * a * t) * a ∈ K₁ ⊔ K₂) :
    ∃ ê₂ : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F, SLAct K₂ a ê₂ σ ∧
      ∀ (x : H) (hx : x ∈ normalizer (K₁ : Set H)) (hx' : t⁻¹ * x * t ∈ normalizer (K₁ : Set H)),
        coordHom K₂ ê₂ hF ⟨x, h.setting.normalizer₁₂ hx⟩ = coordHom K₁ ê₁ hF ⟨t⁻¹ * x * t, hx'⟩ := by
  have hS := h.setting
  have haN : a ∈ normalizer (K₁ : Set H) := mem_normalizer_of_conj_le hact.norm
  have hidx : (normalizer (K₁ : Set H)).index = 2 := by
    have hle : (normalizer (K₁ : Set H)).index ≤ 2 := hS.index_le_two
    have hne : (normalizer (K₁ : Set H)).index ≠ 1 := fun h1 =>
      htN (by rw [Subgroup.index_eq_one.mp h1]; trivial)
    have hpos : (normalizer (K₁ : Set H)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hNn : (normalizer (K₁ : Set H)).Normal := Subgroup.normal_of_index_eq_two hidx
  have ha'N : t⁻¹ * a * t ∈ normalizer (K₁ : Set H) := by
    have := hNn.conj_mem a haN t⁻¹
    simpa using this
  have ha'2 : (t⁻¹ * a * t) * (t⁻¹ * a * t) = 1 := by
    calc (t⁻¹ * a * t) * (t⁻¹ * a * t) = t⁻¹ * (a * a) * t := by group
      _ = 1 := by rw [h.a_mul_a]; group
  obtain ⟨β, hβ⟩ := exists_twist h ê₁ hF hact hσ ha'N ha'2 hV'
  let ê₂ : ↥K₂ ≃* SpecialLinearGroup (Fin 2) F := (swapEquiv hS htN).trans (ê₁.trans β⁻¹)
  have hê₂ : ∀ y : ↥K₂, ê₂ y = β⁻¹ (ê₁ (swapEquiv hS htN y)) := fun y => rfl
  refine ⟨ê₂, ⟨fun x hx => hS.conj_mem₂ haN hx, fun x hx => ?_⟩, fun x hx hx' => ?_⟩
  ·
    set u := ê₁ (swapEquiv hS htN x) with hu
    have e1 : swapEquiv hS htN ⟨a * x * a⁻¹, hx⟩ =
        K₁.normalizerMonoidHom ⟨t⁻¹ * a * t, ha'N⟩ (swapEquiv hS htN x) := by
      apply Subtype.ext
      simp only [swapEquiv_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
      group
    have e2 : ê₁ (swapEquiv hS htN ⟨a * x * a⁻¹, hx⟩) =
        MulAut.congr ê₁ (K₁.normalizerMonoidHom ⟨t⁻¹ * a * t, ha'N⟩) u := by
      rw [e1, congr_apply_eq, hu, MulEquiv.symm_apply_apply]
    have e3 := congrArg (fun f : MulAut (SpecialLinearGroup (Fin 2) F) => f (β⁻¹ u)) hβ
    simp only [MulAut.mul_apply, MulAut.apply_inv_self] at e3
    rw [hê₂, hê₂, e2, ← e3]
  ·
    have hc : MulAut.congr ê₂ (K₂.normalizerMonoidHom ⟨x, hS.normalizer₁₂ hx⟩) =
        β⁻¹ * MulAut.congr ê₁ (K₁.normalizerMonoidHom ⟨t⁻¹ * x * t, hx'⟩) * β := by
      apply MulEquiv.ext
      intro b
      rw [MulAut.mul_apply, MulAut.mul_apply, congr_apply_eq, congr_apply_eq]
      set y : ↥K₂ := ê₂.symm b with hy
      have hyb : ê₁ (swapEquiv hS htN y) = β b := by
        have : ê₂ y = b := by rw [hy]; exact MulEquiv.apply_symm_apply _ _
        rw [hê₂] at this
        rw [← this]; simp
      have e1 : swapEquiv hS htN (K₂.normalizerMonoidHom ⟨x, hS.normalizer₁₂ hx⟩ y) =
          K₁.normalizerMonoidHom ⟨t⁻¹ * x * t, hx'⟩ (swapEquiv hS htN y) := by
        apply Subtype.ext
        simp only [swapEquiv_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
        group
      have e2 : ê₁ (swapEquiv hS htN (K₂.normalizerMonoidHom ⟨x, hS.normalizer₁₂ hx⟩ y)) =
          MulAut.congr ê₁ (K₁.normalizerMonoidHom ⟨t⁻¹ * x * t, hx'⟩) (β b) := by
        rw [e1, congr_apply_eq, ← hyb, MulEquiv.symm_apply_apply]
      rw [hê₂, e2]
      rfl
    show outHom hF (MulAut.congr ê₂ (K₂.normalizerMonoidHom ⟨x, hS.normalizer₁₂ hx⟩)) =
      outHom hF (MulAut.congr ê₁ (K₁.normalizerMonoidHom ⟨t⁻¹ * x * t, hx'⟩))
    rw [hc, outHom_conj]

end TransportH
end CFSG.GH74.GLS.IVK.Prod3
