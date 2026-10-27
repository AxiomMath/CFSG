module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Mod44Group

public section

namespace CFSG.OddStandard.Seitz77

namespace Mod44

open Matrix

variable {Ĥ : Type*} [Group Ĥ]

theorem core (ρ : Ĥ →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ)
    (Λ' Λ'' : Subgroup Ĥ) [IsSimpleGroup Λ'] [IsSimpleGroup Λ''] (h60 : Nat.card Λ' = 60)
    (hcomm : ∀ x ∈ Λ', ∀ y ∈ Λ'', x * y = y * x) (hsup : Λ' ⊔ Λ'' = ⊤) (hinf : Λ' ⊓ Λ'' = ⊥)
    (τ : GL (Fin 8) (ZMod 2)) (hτ : τ * τ = 1) {h' h'' : Ĥ} (hmem' : h' ∈ Λ')
    (hmem'' : h'' ∈ Λ'') (hord : orderOf h' = 3) (hconj : ρ h'' = τ * ρ h' * τ⁻¹)
    (hfpf : ∀ v, (ρ (h' * h'') : Mat8) *ᵥ v = v → v = 0) :
    fixSp (ρ h' : Mat8) ⊓ fixSp (ρ h'' : Mat8) = ⊥ ∧
    Module.finrank (ZMod 2) (fixSp (ρ h' : Mat8)) = 4 ∧
    Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) = 4 ∧
    (fixSp (ρ h'' : Mat8)).map (Matrix.mulVecLin (τ : Mat8)) = fixSp (ρ h' : Mat8) ∧
    (∀ x : Ĥ, ∀ v ∈ fixSp (ρ h'' : Mat8), (ρ x : Mat8) *ᵥ v ∈ fixSp (ρ h'' : Mat8)) ∧
    ∀ x ∈ Λ'', ∀ v ∈ fixSp (ρ h'' : Mat8), (ρ x : Mat8) *ᵥ v = v := by
  have hh3 : h' ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one h'
  have h'ne1 : h' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have h''ne1 : h'' ≠ 1 := by
    intro h
    apply h'ne1
    apply hρ
    have h2 : ρ h'' = 1 := by rw [h, map_one]
    rw [hconj, conj_eq_one_iff] at h2
    rw [h2, map_one]
  have hT : (τ : Mat8) * (τ : Mat8) = 1 := by rw [← Units.val_mul, hτ, Units.val_one]
  have hBT : (τ : Mat8) * (ρ h' : Mat8) * (τ : Mat8) = (ρ h'' : Mat8) := by
    rw [hconj, Units.val_mul, Units.val_mul, inv_eq_of_mul_eq_one_right hτ]
  have hAT : (τ : Mat8) * (ρ h'' : Mat8) * (τ : Mat8) = (ρ h' : Mat8) := by
    rw [← hBT, ← mul_assoc, ← mul_assoc, hT, one_mul, mul_assoc, hT, mul_one]
  have hA3 : (ρ h' : Mat8) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hh3, map_one, Units.val_one]
  have hB3 : (ρ h'' : Mat8) ^ 3 = 1 := by
    have h1 : (ρ h'') ^ 3 = 1 := by
      rw [hconj, conj_pow, ← map_pow, hh3, map_one, mul_one, mul_inv_cancel]
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have hcommAB : (ρ h' : Mat8) * (ρ h'' : Mat8) = (ρ h'' : Mat8) * (ρ h' : Mat8) := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hcomm h' hmem' h'' hmem'']
  have hfpf' : ∀ v, ((ρ h' : Mat8) * (ρ h'' : Mat8)) *ᵥ v = v → v = 0 :=
    fun v hv => hfpf v (by rwa [map_mul, Units.val_mul])
  have hAB0 : fixSp (ρ h' : Mat8) ⊓ fixSp (ρ h'' : Mat8) = ⊥ := fixSp_inf_eq_bot hfpf'
  have hfr : Module.finrank (ZMod 2) (fixSp (ρ h' : Mat8)) =
      Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) := finrank_fixSp_eq hT hBT
  have hinvB : ∀ x ∈ Λ', ∀ v ∈ fixSp (ρ h'' : Mat8), (ρ x : Mat8) *ᵥ v ∈ fixSp (ρ h'' : Mat8) := by
    intro x hx v hv
    refine mulVec_mem_fixSp ?_ hv
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hcomm x hx h'' hmem'']
  have hle4 : Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) ≤ 4 := by
    have := finrank_add_le_eight _ _ hAB0
    omega
  have hd4 : Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) = 4 := by
    by_contra hne
    have hle3 : Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) ≤ 3 := by omega
    have htriv := small_invariant_trivial ρ Λ' h60 _ hinvB hle3
    have hBA : fixSp (ρ h'' : Mat8) ≤ fixSp (ρ h' : Mat8) :=
      fun v hv => mem_fixSp.mpr (htriv h' hmem' v hv)
    have hBbot : fixSp (ρ h'' : Mat8) = ⊥ := by
      rw [eq_bot_iff, ← hAB0]
      exact le_inf hBA le_rfl
    have hr0 : Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) = 0 := by
      rw [hBbot]
      exact finrank_bot _ _
    have hAbot : fixSp (ρ h' : Mat8) = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      omega
    have hfA : ∀ v, (ρ h' : Mat8) *ᵥ v = v → v = 0 := fun v hv => by
      have : v ∈ fixSp (ρ h' : Mat8) := mem_fixSp.mpr hv
      rwa [hAbot, Submodule.mem_bot] at this
    have hfB : ∀ v, (ρ h'' : Mat8) *ᵥ v = v → v = 0 := fun v hv => by
      have : v ∈ fixSp (ρ h'' : Mat8) := mem_fixSp.mpr hv
      rwa [hBbot, Submodule.mem_bot] at this
    have hAB_eq := eq_of_fpf hA3 hB3 hcommAB hfA hfB hfpf'
    have h'eq : h' = h'' := hρ (Units.ext hAB_eq)
    have : h' ∈ Λ' ⊓ Λ'' := ⟨hmem', h'eq ▸ hmem''⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact h'ne1 this
  have hd4' : Module.finrank (ZMod 2) (fixSp (ρ h' : Mat8)) = 4 := hfr.trans hd4
  have hsup' : fixSp (ρ h' : Mat8) ⊔ fixSp (ρ h'' : Mat8) = ⊤ :=
    sup_eq_top_of_finrank hAB0 hd4' hd4
  have hinvB' : ∀ x ∈ Λ'', ∀ v ∈ fixSp (ρ h'' : Mat8),
      (ρ x : Mat8) *ᵥ v ∈ fixSp (ρ h'' : Mat8) := by
    intro x hx
    refine invariant_of_comm hcommAB ?_ hsup' hd4' hd4
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hcomm h' hmem' x hx]
  have hstab : ∀ x : Ĥ, x ∈ stabSub ρ (fixSp (ρ h'' : Mat8)) := by
    have h1 : Λ' ≤ stabSub ρ (fixSp (ρ h'' : Mat8)) :=
      fun x hx => (mem_stabSub ρ).mpr ⟨hinvB x hx, hinvB x⁻¹ (Λ'.inv_mem hx)⟩
    have h2 : Λ'' ≤ stabSub ρ (fixSp (ρ h'' : Mat8)) :=
      fun x hx => (mem_stabSub ρ).mpr ⟨hinvB' x hx, hinvB' x⁻¹ (Λ''.inv_mem hx)⟩
    intro x
    exact sup_le h1 h2 (hsup ▸ Subgroup.mem_top x)
  refine ⟨hAB0, hd4', hd4, map_fixSp hT hAT,
    fun x v hv => ((mem_stabSub ρ).mp (hstab x)).left v hv, ?_⟩
  exact trivial_of_simple ρ Λ'' _ hinvB' hmem'' h''ne1 (fun v hv => mem_fixSp.mp hv)

end Mod44

end CFSG.OddStandard.Seitz77
