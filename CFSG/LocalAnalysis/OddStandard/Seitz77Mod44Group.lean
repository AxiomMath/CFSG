module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Mod44Fix
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.OddStandard.Seitz77

namespace Mod44

open Matrix

section Action

variable {Ĥ : Type*} [Group Ĥ] (ρ : Ĥ →* GL (Fin 8) (ZMod 2))

theorem rho_mul_mulVec (x y : Ĥ) (v : Vec8) :
    (ρ (x * y) : Mat8) *ᵥ v = (ρ x : Mat8) *ᵥ ((ρ y : Mat8) *ᵥ v) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem rho_one_mulVec (v : Vec8) : (ρ 1 : Mat8) *ᵥ v = v := by
  rw [map_one, Units.val_one, Matrix.one_mulVec]

theorem rho_inv_mulVec (x : Ĥ) (v : Vec8) :
    (ρ x⁻¹ : Mat8) *ᵥ ((ρ x : Mat8) *ᵥ v) = v := by
  rw [← rho_mul_mulVec, inv_mul_cancel, rho_one_mulVec]

theorem rho_mulVec_inv (x : Ĥ) (v : Vec8) :
    (ρ x : Mat8) *ᵥ ((ρ x⁻¹ : Mat8) *ᵥ v) = v := by
  rw [← rho_mul_mulVec, mul_inv_cancel, rho_one_mulVec]

def stabSub (F : Submodule (ZMod 2) Vec8) : Subgroup Ĥ where
  carrier := {x | (∀ v ∈ F, (ρ x : Mat8) *ᵥ v ∈ F) ∧ ∀ v ∈ F, (ρ x⁻¹ : Mat8) *ᵥ v ∈ F}
  one_mem' := ⟨fun v hv => by rw [rho_one_mulVec]; exact hv,
    fun v hv => by rw [inv_one, rho_one_mulVec]; exact hv⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [rho_mul_mulVec]
      exact hx1 _ (hy1 v hv)
    · rw [_root_.mul_inv_rev, rho_mul_mulVec]
      exact hy2 _ (hx2 v hv)
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, fun v hv => by simpa using hx1 v hv⟩

theorem mem_stabSub {F : Submodule (ZMod 2) Vec8} {x : Ĥ} :
    x ∈ stabSub ρ F ↔
      (∀ v ∈ F, (ρ x : Mat8) *ᵥ v ∈ F) ∧ ∀ v ∈ F, (ρ x⁻¹ : Mat8) *ᵥ v ∈ F :=
  Iff.rfl

def vecStab (v : Vec8) : Subgroup Ĥ where
  carrier := {z | (ρ z : Mat8) *ᵥ v = v}
  one_mem' := rho_one_mulVec ρ v
  mul_mem' := by
    intro a b ha hb
    have ha' : (ρ a : Mat8) *ᵥ v = v := ha
    have hb' : (ρ b : Mat8) *ᵥ v = v := hb
    show (ρ (a * b) : Mat8) *ᵥ v = v
    rw [rho_mul_mulVec, hb', ha']
  inv_mem' := by
    intro z hz
    have hz' : (ρ z : Mat8) *ᵥ v = v := hz
    have h := rho_inv_mulVec ρ z v
    rw [hz'] at h
    exact h

theorem mem_vecStab {v : Vec8} {z : Ĥ} :
    z ∈ vecStab ρ v ↔ (ρ z : Mat8) *ᵥ v = v :=
  Iff.rfl

theorem trivial_of_simple (Λ : Subgroup Ĥ) [IsSimpleGroup Λ] (Y : Submodule (ZMod 2) Vec8)
    (hY : ∀ x ∈ Λ, ∀ v ∈ Y, (ρ x : Mat8) *ᵥ v ∈ Y) {g : Ĥ} (hg : g ∈ Λ) (hg1 : g ≠ 1)
    (hgY : ∀ v ∈ Y, (ρ g : Mat8) *ᵥ v = v) : ∀ x ∈ Λ, ∀ v ∈ Y, (ρ x : Mat8) *ᵥ v = v := by
  let N : Subgroup Λ :=
    { carrier := {x | ∀ v ∈ Y, (ρ (x : Ĥ) : Mat8) *ᵥ v = v}
      one_mem' := fun v _ => rho_one_mulVec ρ v
      mul_mem' := by
        intro x y hx hy v hv
        rw [Subgroup.coe_mul, rho_mul_mulVec, hy v hv, hx v hv]
      inv_mem' := by
        intro x hx v hv
        have h := rho_inv_mulVec ρ (x : Ĥ) v
        rwa [hx v hv] at h }
  have : N.Normal := ⟨fun n hn g v hv => by
    have hgv : (ρ ((g⁻¹ : Λ) : Ĥ) : Mat8) *ᵥ v ∈ Y := hY _ (g⁻¹).prop v hv
    rw [Subgroup.coe_mul, Subgroup.coe_mul, rho_mul_mulVec, rho_mul_mulVec, hn _ hgv]
    exact rho_mulVec_inv ρ (g : Ĥ) v⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    apply hg1
    have h1 : (⟨g, hg⟩ : Λ) ∈ N := hgY
    rw [h] at h1
    simpa using h1
  · intro x hx v hv
    have h1 : (⟨x, hx⟩ : Λ) ∈ N := h ▸ Subgroup.mem_top _
    exact h1 v hv

theorem small_invariant_trivial (Λ : Subgroup Ĥ) [IsSimpleGroup Λ] (h60 : Nat.card Λ = 60)
    (Y : Submodule (ZMod 2) Vec8) (hY : ∀ x ∈ Λ, ∀ v ∈ Y, (ρ x : Mat8) *ᵥ v ∈ Y)
    (hd : Module.finrank (ZMod 2) Y ≤ 3) : ∀ x ∈ Λ, ∀ v ∈ Y, (ρ x : Mat8) *ᵥ v = v := by
  have : Finite Λ := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Λ) 5 (by rw [h60]; norm_num)
  have hg5 : (g : Ĥ) ^ 5 = 1 := by
    have : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
    exact congrArg Subtype.val this
  have hg1 : (g : Ĥ) ≠ 1 := by
    intro h
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    omega
  have hmat : (ρ (g : Ĥ) : Mat8) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hg5, map_one, Units.val_one]
  have hle := le_fixSp_of_pow_five_eq_one _ hmat Y (hY _ g.prop) hd
  exact trivial_of_simple ρ Λ Y hY g.prop hg1 (fun v hv => mem_fixSp.mp (hle hv))

end Action

open scoped Pointwise

theorem exists_conj_mem_zpowers {Ĥ : Type*} [Group Ĥ] (Λ : Subgroup Ĥ) (h60 : Nat.card Λ = 60)
    {h g : Ĥ} (hh : h ∈ Λ) (hg : g ∈ Λ) (ho : orderOf h = 3) (go : orderOf g = 3) :
    ∃ x ∈ Λ, x * h * x⁻¹ ∈ Subgroup.zpowers g := by
  have : Finite Λ := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : (Nat.card Λ).factorization 3 = 1 := by
    rw [h60, show (60 : ℕ) = 3 * 20 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let h₀ : Λ := ⟨h, hh⟩
  let g₀ : Λ := ⟨g, hg⟩
  have ho₀ : orderOf h₀ = 3 := by rw [← ho]; exact Subgroup.orderOf_mk h hh
  have go₀ : orderOf g₀ = 3 := by rw [← go]; exact Subgroup.orderOf_mk g hg
  let P : Sylow 3 Λ := Sylow.ofCard (Subgroup.zpowers h₀) (by rw [Nat.card_zpowers, ho₀, hf]; rfl)
  let Q : Sylow 3 Λ := Sylow.ofCard (Subgroup.zpowers g₀) (by rw [Nat.card_zpowers, go₀, hf]; rfl)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq Λ P Q
  have hmem : MulAut.conj x • h₀ ∈ ((x • P : Sylow 3 Λ) : Subgroup Λ) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul h₀ (MulAut.conj x) _ (Subgroup.mem_zpowers h₀)
  rw [hx] at hmem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨x, x.prop, Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩⟩
  have := congrArg Subtype.val hn
  simpa [g₀, h₀] using this

end Mod44

end CFSG.OddStandard.Seitz77
