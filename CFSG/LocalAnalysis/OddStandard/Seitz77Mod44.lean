module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Mod44Core

public section

namespace CFSG.OddStandard.Seitz77

open Matrix Mod44

section Defs

variable {Ĥ : Type*} [Group Ĥ]

structure Mod44Half (ρ : Ĥ →* GL (Fin 8) (ZMod 2)) (Λ' Λ'' : Subgroup Ĥ)
    (F : Submodule (ZMod 2) (Fin 8 → ZMod 2)) : Prop where
  finrank_eq : Module.finrank (ZMod 2) F = 4
  mem_iff : ∀ v, v ∈ F ↔ ∀ x ∈ Λ'', (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v
  invariant : ∀ x : Ĥ, ∀ v ∈ F, (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v ∈ F
  faithful : ∀ x ∈ Λ', (∀ v ∈ F, (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v) → x = 1
  fixedPointFree : ∀ x ∈ Λ', orderOf x = 3 → ∀ v ∈ F,
    (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v → v = 0
  irreducible : ∀ Y : Submodule (ZMod 2) (Fin 8 → ZMod 2), Y ≤ F →
    (∀ x ∈ Λ', ∀ v ∈ Y, (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v ∈ Y) → Y = ⊥ ∨ Y = F

structure Mod44Split (ρ : Ĥ →* GL (Fin 8) (ZMod 2)) (Λ' Λ'' : Subgroup Ĥ)
    (τ : GL (Fin 8) (ZMod 2)) (F' F'' : Submodule (ZMod 2) (Fin 8 → ZMod 2)) : Prop where
  isCompl : IsCompl F' F''
  left : Mod44Half ρ Λ' Λ'' F'
  right : Mod44Half ρ Λ'' Λ' F''
  map_left : F'.map (Matrix.mulVecLin (τ : Matrix (Fin 8) (Fin 8) (ZMod 2))) = F''
  map_right : F''.map (Matrix.mulVecLin (τ : Matrix (Fin 8) (Fin 8) (ZMod 2))) = F'

end Defs

namespace Mod44

section Half

variable {Ĥ : Type*} [Group Ĥ]

theorem half (ρ : Ĥ →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ)
    (Λ' Λ'' : Subgroup Ĥ) [IsSimpleGroup Λ'] (h60 : Nat.card Λ' = 60) {h' h'' : Ĥ}
    (hmem' : h' ∈ Λ') (hmem'' : h'' ∈ Λ'') (hord : orderOf h' = 3)
    (hinf : fixSp (ρ h' : Mat8) ⊓ fixSp (ρ h'' : Mat8) = ⊥)
    (hsup : fixSp (ρ h' : Mat8) ⊔ fixSp (ρ h'' : Mat8) = ⊤)
    (hdim : Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) = 4)
    (hinv : ∀ x : Ĥ, ∀ v ∈ fixSp (ρ h'' : Mat8), (ρ x : Mat8) *ᵥ v ∈ fixSp (ρ h'' : Mat8))
    (htriv'' : ∀ x ∈ Λ'', ∀ v ∈ fixSp (ρ h'' : Mat8), (ρ x : Mat8) *ᵥ v = v)
    (htriv' : ∀ x ∈ Λ', ∀ v ∈ fixSp (ρ h' : Mat8), (ρ x : Mat8) *ᵥ v = v) :
    Mod44Half ρ Λ' Λ'' (fixSp (ρ h'' : Mat8)) where
  finrank_eq := hdim
  mem_iff v := ⟨fun hv x hx => htriv'' x hx v hv, fun h => mem_fixSp.mpr (h h'' hmem'')⟩
  invariant := hinv
  faithful := by
    intro x hx hxF
    have hall : ∀ v, (ρ x : Mat8) *ᵥ v = v := by
      intro v
      have hv : v ∈ fixSp (ρ h' : Mat8) ⊔ fixSp (ρ h'' : Mat8) := hsup ▸ Submodule.mem_top
      obtain ⟨g, hg, f, hf, rfl⟩ := Submodule.mem_sup.mp hv
      rw [Matrix.mulVec_add, htriv' x hx g hg, hxF f hf]
    apply hρ
    rw [map_one]
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [hall v, Units.val_one, Matrix.one_mulVec]
  fixedPointFree := by
    intro x hx hxo v hv hxv
    obtain ⟨y, hy, hyx⟩ := exists_conj_mem_zpowers Λ' h60 hmem' hx hord hxo
    have hxS : x ∈ vecStab ρ v := (mem_vecStab ρ).mpr hxv
    have hS : y * h' * y⁻¹ ∈ vecStab ρ v := Subgroup.zpowers_le.mpr hxS hyx
    have h1 : (ρ y : Mat8) *ᵥ ((ρ h' : Mat8) *ᵥ ((ρ y⁻¹ : Mat8) *ᵥ v)) = v := by
      rw [← rho_mul_mulVec, ← rho_mul_mulVec]
      exact (mem_vecStab ρ).mp hS
    have h2 : (ρ h' : Mat8) *ᵥ ((ρ y⁻¹ : Mat8) *ᵥ v) = (ρ y⁻¹ : Mat8) *ᵥ v := by
      have := congrArg (fun w => (ρ y⁻¹ : Mat8) *ᵥ w) h1
      simpa only [rho_inv_mulVec] using this
    have hw : (ρ y⁻¹ : Mat8) *ᵥ v ∈ fixSp (ρ h' : Mat8) ⊓ fixSp (ρ h'' : Mat8) :=
      ⟨mem_fixSp.mpr h2, hinv y⁻¹ v hv⟩
    rw [hinf, Submodule.mem_bot] at hw
    have := rho_mulVec_inv ρ y v
    rwa [hw, Matrix.mulVec_zero, eq_comm] at this
  irreducible := by
    intro Y hYF hYinv
    by_cases hd : Module.finrank (ZMod 2) Y ≤ 3
    · left
      have htriv := small_invariant_trivial ρ Λ' h60 Y hYinv hd
      rw [eq_bot_iff, ← hinf]
      exact le_inf (fun v hv => mem_fixSp.mpr (htriv h' hmem' v hv)) hYF
    · right
      have hle : Module.finrank (ZMod 2) Y ≤ Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) :=
        Submodule.finrank_mono hYF
      have h4 : Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) (fixSp (ρ h'' : Mat8)) := by
        omega
      exact Submodule.eq_of_le_of_finrank_eq hYF h4

end Half

end Mod44

variable {Ĥ : Type*} [Group Ĥ]

theorem mod44 (ρ : Ĥ →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ)
    (Λ' Λ'' : Subgroup Ĥ) [IsSimpleGroup Λ'] [IsSimpleGroup Λ''] (h60' : Nat.card Λ' = 60)
    (h60'' : Nat.card Λ'' = 60) (hcomm : ∀ x ∈ Λ', ∀ y ∈ Λ'', x * y = y * x)
    (hsup : Λ' ⊔ Λ'' = ⊤) (hinf : Λ' ⊓ Λ'' = ⊥) (τ : GL (Fin 8) (ZMod 2)) (hτ : τ * τ = 1)
    (h' h'' : Ĥ) (hmem' : h' ∈ Λ') (hmem'' : h'' ∈ Λ'') (hord : orderOf h' = 3)
    (hconj : ρ h'' = τ * ρ h' * τ⁻¹)
    (hfpf : ∀ v, (ρ (h' * h'') : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v → v = 0) :
    ∃ F' F'' : Submodule (ZMod 2) (Fin 8 → ZMod 2), Mod44Split ρ Λ' Λ'' τ F' F'' ∧
      (∀ v, v ∈ F' ↔ (ρ h'' : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v) ∧
      (∀ v, v ∈ F'' ↔ (ρ h' : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v) := by
  have hord'' : orderOf h'' = 3 := by
    have h1 := orderOf_injective (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective (ρ h')
    have h2 : (MulAut.conj τ).toMonoidHom (ρ h') = ρ h'' := by
      rw [hconj]
      rfl
    rw [h2, orderOf_injective ρ hρ, orderOf_injective ρ hρ] at h1
    rw [h1, hord]
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hconj' : ρ h' = τ * ρ h'' * τ⁻¹ := by
    rw [hconj, hτinv]
    calc ρ h' = (τ * τ) * ρ h' * (τ * τ) := by rw [hτ, one_mul, mul_one]
      _ = τ * (τ * ρ h' * τ) * τ := by simp only [mul_assoc]
  have hcomm'' : ∀ x ∈ Λ'', ∀ y ∈ Λ', x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hsup'' : Λ'' ⊔ Λ' = ⊤ := by rw [sup_comm]; exact hsup
  have hinf'' : Λ'' ⊓ Λ' = ⊥ := by rw [inf_comm]; exact hinf
  have hfpf'' : ∀ v, (ρ (h'' * h') : Mat8) *ᵥ v = v → v = 0 := by
    rw [← hcomm h' hmem' h'' hmem'']
    exact hfpf
  obtain ⟨hAB0, hdA, hdB, hmapB, hinvB, htrivB⟩ :=
    core ρ hρ Λ' Λ'' h60' hcomm hsup hinf τ hτ hmem' hmem'' hord hconj hfpf
  obtain ⟨hBA0, -, -, hmapA, hinvA, htrivA⟩ :=
    core ρ hρ Λ'' Λ' h60'' hcomm'' hsup'' hinf'' τ hτ hmem'' hmem' hord'' hconj' hfpf''
  have hsupAB : fixSp (ρ h' : Mat8) ⊔ fixSp (ρ h'' : Mat8) = ⊤ :=
    sup_eq_top_of_finrank hAB0 hdA hdB
  have hsupBA : fixSp (ρ h'' : Mat8) ⊔ fixSp (ρ h' : Mat8) = ⊤ := by
    rw [sup_comm]; exact hsupAB
  refine ⟨fixSp (ρ h'' : Mat8), fixSp (ρ h' : Mat8), ⟨IsCompl.of_eq hBA0 hsupBA, ?_, ?_, hmapB,
    hmapA⟩, fun v => mem_fixSp, fun v => mem_fixSp⟩
  · exact half ρ hρ Λ' Λ'' h60' hmem' hmem'' hord hAB0 hsupAB hdB hinvB htrivB htrivA
  · exact half ρ hρ Λ'' Λ' h60'' hmem'' hmem' hord'' hBA0 hsupBA hdA hinvA htrivA htrivB

theorem mod44_of_forall (ρ : Ĥ →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ)
    (Λ' Λ'' : Subgroup Ĥ) [IsSimpleGroup Λ'] [IsSimpleGroup Λ''] (h60' : Nat.card Λ' = 60)
    (h60'' : Nat.card Λ'' = 60) (hcomm : ∀ x ∈ Λ', ∀ y ∈ Λ'', x * y = y * x)
    (hsup : Λ' ⊔ Λ'' = ⊤) (hinf : Λ' ⊓ Λ'' = ⊥) (τ : GL (Fin 8) (ZMod 2)) (hτ : τ * τ = 1)
    (hexch : ∀ x ∈ Λ', ∃ y ∈ Λ'', ρ y = τ * ρ x * τ⁻¹)
    (hfpf : ∀ h' ∈ Λ', orderOf h' = 3 → ∀ h'' ∈ Λ'', ρ h'' = τ * ρ h' * τ⁻¹ →
      ∀ v, (ρ (h' * h'') : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v → v = 0) :
    ∃ F' F'' : Submodule (ZMod 2) (Fin 8 → ZMod 2), Mod44Split ρ Λ' Λ'' τ F' F'' := by
  have : Finite Λ' := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Λ') 3 (by rw [h60']; norm_num)
  have hgo : orderOf (g : Ĥ) = 3 := by rw [Subgroup.orderOf_coe]; exact hg
  obtain ⟨h'', hmem'', hconj⟩ := hexch g g.prop
  obtain ⟨F', F'', h, -, -⟩ := mod44 ρ hρ Λ' Λ'' h60' h60'' hcomm hsup hinf τ hτ g h'' g.prop
    hmem'' hgo hconj (hfpf g g.prop hgo h'' hmem'' hconj)
  exact ⟨F', F'', h⟩

end CFSG.OddStandard.Seitz77
