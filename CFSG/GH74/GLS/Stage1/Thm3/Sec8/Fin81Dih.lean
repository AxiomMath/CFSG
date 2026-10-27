module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ref
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylModel
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Nilpotent

public section

open Equiv

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

open CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.ShapeModel

@[expose] def da : Perm (Fin 4) := swap 0 1
@[expose] def dw : Perm (Fin 4) := swap 0 2 * swap 1 3
@[expose] def dc : Perm (Fin 4) := da * dw

@[expose] def deltaFun : DihedralGroup 4 → Perm (Fin 4)
  | .r k => dc ^ k.val
  | .sr k => da * dc ^ k.val

@[expose] def delta : DihedralGroup 4 →* Perm (Fin 4) where
  toFun := deltaFun
  map_one' := by decide
  map_mul' := by decide

theorem delta_injective : Function.Injective delta := by decide

theorem delta_mem : ∀ d : DihedralGroup 4, delta d ∈ R0 := by decide

theorem delta_surj : ∀ π : Perm (Fin 4), π ∈ R0 → ∃ d, delta d = π := by decide

section DihHom

variable {H : Type*} [Group H]

@[expose] def dihedralHom (ρ τ : H) (hρ : ρ ^ 4 = 1) (hτ : τ * τ = 1) (hτρ : τ * ρ * τ⁻¹ = ρ⁻¹) :
    DihedralGroup 4 →* H where
  toFun
    | .r k => cycHom 4 ρ hρ (Multiplicative.ofAdd k)
    | .sr k => τ * cycHom 4 ρ hρ (Multiplicative.ofAdd k)
  map_one' := by
    show cycHom 4 ρ hρ (Multiplicative.ofAdd 0) = 1
    simp
  map_mul' := by
    have hconj : ∀ x : Multiplicative (ZMod 4),
        τ * cycHom 4 ρ hρ x * τ⁻¹ = cycHom 4 ρ hρ x⁻¹ := by
      intro x
      obtain ⟨n, rfl⟩ := exists_intCast 4 x
      have h1 : (Multiplicative.ofAdd (n : ZMod 4))⁻¹ = Multiplicative.ofAdd (((-n : ℤ) : ZMod 4)) := by
        rw [← ofAdd_neg]; push_cast; rfl
      rw [h1, cycHom_intCast, cycHom_intCast, ← conj_zpow, hτρ, inv_zpow, zpow_neg]
    have hconj' : ∀ x : Multiplicative (ZMod 4),
        cycHom 4 ρ hρ x * τ = τ * cycHom 4 ρ hρ x⁻¹ := by
      intro x
      have h1 := hconj x⁻¹
      rw [inv_inv] at h1
      calc cycHom 4 ρ hρ x * τ = (τ * cycHom 4 ρ hρ x⁻¹ * τ⁻¹) * τ := by rw [h1]
        _ = τ * cycHom 4 ρ hρ x⁻¹ := by group
    intro a b
    rcases a with i | i <;> rcases b with j | j
    · show cycHom 4 ρ hρ (Multiplicative.ofAdd (i + j)) = _
      rw [ofAdd_add, map_mul]
    · show τ * cycHom 4 ρ hρ (Multiplicative.ofAdd (j - i)) = _
      show _ = cycHom 4 ρ hρ (Multiplicative.ofAdd i) * (τ * cycHom 4 ρ hρ (Multiplicative.ofAdd j))
      rw [← mul_assoc, hconj', mul_assoc, ← map_mul]
      congr 2
      rw [← ofAdd_neg, ← ofAdd_add]
      congr 1
      ring
    · show τ * cycHom 4 ρ hρ (Multiplicative.ofAdd (i + j)) = _
      show _ = (τ * cycHom 4 ρ hρ (Multiplicative.ofAdd i)) * cycHom 4 ρ hρ (Multiplicative.ofAdd j)
      rw [mul_assoc, ← map_mul, ofAdd_add]
    · show cycHom 4 ρ hρ (Multiplicative.ofAdd (j - i)) = _
      show _ = (τ * cycHom 4 ρ hρ (Multiplicative.ofAdd i)) * (τ * cycHom 4 ρ hρ (Multiplicative.ofAdd j))
      rw [mul_assoc, ← mul_assoc (cycHom 4 ρ hρ (Multiplicative.ofAdd i)), hconj', ← mul_assoc, ← mul_assoc τ τ, hτ, one_mul, ← map_mul]
      congr 2
      simp only [toAdd_ofAdd, toAdd_inv]
      ring

end DihHom

@[expose] noncomputable def eR : DihedralGroup 4 ≃* R0 :=
  MulEquiv.ofBijective (delta.codRestrict R0 delta_mem)
    ⟨fun x y h => delta_injective (congrArg Subtype.val h), fun r => by
      obtain ⟨d, hd⟩ := delta_surj r.1 r.2
      exact ⟨d, Subtype.ext hd⟩⟩

theorem da_mem : da ∈ R0 := by decide
theorem dw_mem : dw ∈ R0 := by decide

@[expose] def aR : R0 := ⟨da, da_mem⟩
@[expose] def wR : R0 := ⟨dw, dw_mem⟩

theorem R0_words : ∀ r : R0, r = 1 ∨ r = aR ∨ r = wR ∨ r = aR * wR ∨ r = wR * aR ∨
    r = aR * wR * aR ∨ r = wR * aR * wR ∨ r = aR * wR * aR * wR := by decide

theorem eR_symm_aR : eR.symm aR = DihedralGroup.sr 0 := by
  apply eR.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  decide

theorem eR_symm_wR : eR.symm wR = DihedralGroup.sr 1 := by
  apply eR.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  decide

theorem exists_hom_M128 {H : Type*} [Group H] (α : Multiplicative V4 →* H) (τ ω : H)
    (hτ : τ * τ = 1) (hω : ω * ω = 1) (hτω : (τ * ω) ^ 4 = 1)
    (hcτ : ∀ v, τ * α v * τ⁻¹ = α (ψ aR v)) (hcω : ∀ v, ω * α v * ω⁻¹ = α (ψ wR v)) :
    ∃ Φ : M128 →* H, (∀ v, Φ (SemidirectProduct.inl v) = α v) ∧
      Φ (SemidirectProduct.inr aR) = τ ∧ Φ (SemidirectProduct.inr wR) = ω := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hωi : ω⁻¹ = ω := inv_eq_of_mul_eq_one_right hω
  have hτρ : τ * (τ * ω) * τ⁻¹ = (τ * ω)⁻¹ := by
    rw [mul_inv_rev, hτi, hωi, ← mul_assoc, hτ, one_mul]
  let fgD : DihedralGroup 4 →* H := dihedralHom (τ * ω) τ hτω hτ hτρ
  let fg : R0 →* H := fgD.comp eR.symm.toMonoidHom
  have hfg_a : fg aR = τ := by
    show fgD (eR.symm aR) = τ
    rw [eR_symm_aR]
    show τ * cycHom 4 (τ * ω) hτω (Multiplicative.ofAdd 0) = τ
    simp
  have hfg_w : fg wR = ω := by
    show fgD (eR.symm wR) = ω
    rw [eR_symm_wR]
    show τ * cycHom 4 (τ * ω) hτω (Multiplicative.ofAdd 1) = ω
    rw [cycHom_ofAdd_one, ← mul_assoc, hτ, one_mul]
  have hCp : ∀ r : R0, ∀ v, fg r * α v * (fg r)⁻¹ = α (ψ r v) := by
    have hmul : ∀ r₁ r₂ : R0, (∀ v, fg r₁ * α v * (fg r₁)⁻¹ = α (ψ r₁ v)) →
        (∀ v, fg r₂ * α v * (fg r₂)⁻¹ = α (ψ r₂ v)) →
        ∀ v, fg (r₁ * r₂) * α v * (fg (r₁ * r₂))⁻¹ = α (ψ (r₁ * r₂) v) := by
      intro r₁ r₂ h₁ h₂ v
      calc fg (r₁ * r₂) * α v * (fg (r₁ * r₂))⁻¹
          = fg r₁ * (fg r₂ * α v * (fg r₂)⁻¹) * (fg r₁)⁻¹ := by rw [map_mul]; group
        _ = fg r₁ * α (ψ r₂ v) * (fg r₁)⁻¹ := by rw [h₂ v]
        _ = α (ψ r₁ (ψ r₂ v)) := h₁ _
        _ = α (ψ (r₁ * r₂) v) := by rw [map_mul]; rfl
    have h1 : ∀ v, fg 1 * α v * (fg 1)⁻¹ = α (ψ 1 v) := by
      intro v; simp
    have ha : ∀ v, fg aR * α v * (fg aR)⁻¹ = α (ψ aR v) := by
      intro v; rw [hfg_a]; exact hcτ v
    have hw : ∀ v, fg wR * α v * (fg wR)⁻¹ = α (ψ wR v) := by
      intro v; rw [hfg_w]; exact hcω v
    intro r
    rcases R0_words r with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact ha
    · exact hw
    · exact hmul _ _ ha hw
    · exact hmul _ _ hw ha
    · exact hmul _ _ (hmul _ _ ha hw) ha
    · exact hmul _ _ (hmul _ _ hw ha) hw
    · exact hmul _ _ (hmul _ _ (hmul _ _ ha hw) ha) hw
  have hcompat : ∀ r : R0, α.comp (ψ r).toMonoidHom = (MulAut.conj (fg r)).toMonoidHom.comp α := by
    intro r
    refine MonoidHom.ext fun v => ?_
    show α (ψ r v) = fg r * α v * (fg r)⁻¹
    exact (hCp r v).symm
  refine ⟨SemidirectProduct.lift α fg hcompat, fun v => ?_, ?_, ?_⟩
  · exact SemidirectProduct.lift_inl _ _ _ v
  · rw [SemidirectProduct.lift_inr]; exact hfg_a
  · rw [SemidirectProduct.lift_inr]; exact hfg_w

@[expose] def zeta : M128 := SemidirectProduct.inl (Multiplicative.ofAdd ((0 : ZMod 4), (2 : ZMod 4)))

theorem zeta_ne_one : zeta ≠ 1 := by decide

theorem zeta_mul_self : zeta * zeta = 1 := by decide

@[expose] def isCentralPair (v : Multiplicative V4) (r : R0) : Prop :=
  ∀ (v' : Multiplicative V4) (r' : R0),
    (((⟨v, r⟩ : M128) * ⟨v', r'⟩).left = ((⟨v', r'⟩ : M128) * ⟨v, r⟩).left ∧
      ((⟨v, r⟩ : M128) * ⟨v', r'⟩).right = ((⟨v', r'⟩ : M128) * ⟨v, r⟩).right)

instance (v : Multiplicative V4) (r : R0) : Decidable (isCentralPair v r) := by
  unfold isCentralPair; infer_instance

theorem center_M128_aux : ∀ (v : Multiplicative V4) (r : R0), isCentralPair v r →
    ((v = 1 ∧ r = 1) ∨ (v = Multiplicative.ofAdd ((0 : ZMod 4), (2 : ZMod 4)) ∧ r = 1)) := by
  decide +kernel

theorem center_M128 : ∀ x : M128, (∀ y : M128, x * y = y * x) → x = 1 ∨ x = zeta := by
  intro x hx
  have h := center_M128_aux x.left x.right (show isCentralPair x.left x.right from fun v' r' => by
    have := hx ⟨v', r'⟩
    exact ⟨congrArg SemidirectProduct.left this, congrArg SemidirectProduct.right this⟩)
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact SemidirectProduct.ext h1 h2
  · right; exact SemidirectProduct.ext h1 h2

theorem isPGroup_M128 : IsPGroup 2 M128 :=
  IsPGroup.of_card (n := 7) (by rw [card_M128]; norm_num)

theorem injective_of_zeta {H : Type*} [Group H] (Φ : M128 →* H) (h : Φ zeta ≠ 1) :
    Function.Injective Φ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hnil : Group.IsNilpotent M128 := isPGroup_M128.isNilpotent
  have hker : Φ.ker ≠ ⊥ := by
    intro hbot
    apply hx1
    have : x ∈ Φ.ker := hx
    rw [hbot] at this
    exact this
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hker
  obtain ⟨y, hy⟩ : ∃ y : M128, (y ∈ Φ.ker ∧ y ∈ Subgroup.center M128) ∧ y ≠ 1 := by
    by_contra hcon
    apply hne
    rw [eq_bot_iff]
    intro y hy
    by_contra hy1
    exact hcon ⟨y, hy, hy1⟩
  have hyc : ∀ g : M128, y * g = g * y := fun g => (Subgroup.mem_center_iff.1 hy.1.2 g).symm
  rcases center_M128 y hyc with h1 | h1
  · exact absurd h1 hy.2
  · apply h
    rw [← h1]
    exact hy.1.1

theorem psi_apply (r : R0) (v : Multiplicative V4) : ψ r v = refAct (r : Perm (Fin 4)) v := rfl

theorem refAct_apply_ofAdd (π : Perm (Fin 4)) (v : V4) :
    refAct π (Multiplicative.ofAdd v) = Multiplicative.ofAdd (actV π v) := rfl

theorem actV_aR (x y : ZMod 4) : actV (aR : Perm (Fin 4)) (x, y) = (-x, y - x) := by
  revert x y; decide

theorem actV_wR (x y : ZMod 4) : actV (wR : Perm (Fin 4)) (x, y) = (-x - 2 * y, -y) := by
  revert x y; decide

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
