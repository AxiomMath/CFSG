module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12Defs
public import CFSG.LargeExtraspecial.S14W4SetDict
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {K : Type*} [Group K] [Finite K]

structure LatData (T : Setting K) (R : Subgroup K) (W₁ W₂ : Submodule (ZMod 2) T.Qt) : Prop where
  conj_mem : ∀ k : T.M, ∀ r ∈ R, (k : K) * r * (k : K)⁻¹ ∈ R
  inv₁ : W4Dict.IsInv T R W₁
  inv₂ : W4Dict.IsInv T R W₂
  inf : W₁ ⊓ W₂ = ⊥
  sup : W₁ ⊔ W₂ = ⊤
  finrank₁ : finrank (ZMod 2) W₁ = 4
  finrank₂ : finrank (ZMod 2) W₂ = 4
  ts₁ : ∀ w ∈ W₁, T.q w = 0
  ts₂ : ∀ w ∈ W₂, T.q w = 0
  all : ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → W = ⊥ ∨ W = W₁ ∨ W = W₂ ∨ W = ⊤

namespace LatData

variable {T : Setting K} {R : Subgroup K} {W₁ W₂ : Submodule (ZMod 2) T.Qt}

theorem symm (L : LatData T R W₁ W₂) : LatData T R W₂ W₁ :=
  ⟨L.conj_mem, L.inv₂, L.inv₁, by rw [inf_comm]; exact L.inf, by rw [sup_comm]; exact L.sup,
    L.finrank₂, L.finrank₁, L.ts₂, L.ts₁, fun W hW => by
      rcases L.all W hW with h | h | h | h <;> tauto⟩

variable (L : LatData T R W₁ W₂)
include L

theorem finrank_Qt : finrank (ZMod 2) T.Qt = 8 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  rw [L.inf, L.sup, finrank_bot, finrank_top, L.finrank₁, L.finrank₂, add_zero] at h
  exact h

theorem isInv_map (m : T.M) {W : Submodule (ZMod 2) T.Qt} (hW : W4Dict.IsInv T R W) :
    W4Dict.IsInv T R (W.map ((T.ρ m : T.O) : T.Qt →ₗ[ZMod 2] T.Qt)) := by
  rintro r hr _ ⟨w, hw, rfl⟩
  have hr' : ((m⁻¹ * r * m : T.M) : K) ∈ R := by
    have := L.conj_mem m⁻¹ r hr
    simpa [mul_assoc] using this
  refine ⟨((T.ρ (m⁻¹ * r * m) : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w, hW _ hr' w hw, ?_⟩
  change ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) (((T.ρ (m⁻¹ * r * m) : T.O) :
    T.Qt ≃ₗ[ZMod 2] T.Qt) w) = ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt)
      (((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w)
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
    ← map_mul, ← map_mul]
  congr 3
  group

theorem eq_or_eq_of_finrank {W : Submodule (ZMod 2) T.Qt} (hW : W4Dict.IsInv T R W)
    (h4 : finrank (ZMod 2) W = 4) : W = W₁ ∨ W = W₂ := by
  rcases L.all W hW with h | h | h | h
  · rw [h, finrank_bot] at h4
    omega
  · exact Or.inl h
  · exact Or.inr h
  · rw [h, finrank_top, L.finrank_Qt] at h4
    omega

theorem map_eq (m : T.M) :
    (W₁.map ((T.ρ m : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₁ ∧
        W₂.map ((T.ρ m : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₂) ∨
      (W₁.map ((T.ρ m : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₂ ∧
        W₂.map ((T.ρ m : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = W₁) := by
  have h1 := L.eq_or_eq_of_finrank (L.isInv_map m L.inv₁)
    (by rw [LinearEquiv.finrank_map_eq, L.finrank₁])
  have h2 := L.eq_or_eq_of_finrank (L.isInv_map m L.inv₂)
    (by rw [LinearEquiv.finrank_map_eq, L.finrank₂])
  have hinj := Submodule.map_injective_of_injective
    (f := ((T.ρ m : T.O) : T.Qt →ₗ[ZMod 2] T.Qt)) (LinearEquiv.injective _)
  have hne : W₁ ≠ W₂ := fun h => by
    have := L.inf
    rw [h, inf_idem] at this
    have h4 := L.finrank₂
    rw [this, finrank_bot] at h4
    omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (hinj (h1.trans h2.symm)) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (hinj (h1.trans h2.symm)) hne

omit L in
theorem map_eq_of_mapsTo {s : T.O} {W : Submodule (ZMod 2) T.Qt}
    (h : ∀ w ∈ W, (s : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W) :
    W.map ((s : T.Qt ≃ₗ[ZMod 2] T.Qt) : T.Qt →ₗ[ZMod 2] T.Qt) = W :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨w, hw, rfl⟩; exact h w hw)
    (LinearEquiv.finrank_map_eq _ _)

theorem not_isTypeA_of_swap {σ : T.O}
    (hσ : W₁.map ((σ : T.Qt ≃ₗ[ZMod 2] T.Qt) : T.Qt →ₗ[ZMod 2] T.Qt) = W₂) :
    ¬ IsTypeA T.q (σ : T.Qt ≃ₗ[ZMod 2] T.Qt) 2 := by
  rintro ⟨-, -, -, hdim, -⟩
  set f : T.Qt →ₗ[ZMod 2] T.Qt :=
    ((σ : T.Qt ≃ₗ[ZMod 2] T.Qt) : T.Qt →ₗ[ZMod 2] T.Qt) - LinearMap.id with hf
  have hinj : Function.Injective (f.domRestrict W₁) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, hf, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hw
    have hw₂ : (w : T.Qt) ∈ W₂ := hσ ▸ ⟨w, w.2, hw⟩
    have hw0 : (w : T.Qt) ∈ W₁ ⊓ W₂ := ⟨w.2, hw₂⟩
    rw [L.inf] at hw0
    exact (Submodule.mem_bot _).mpr (Subtype.ext ((Submodule.mem_bot _).mp hw0))
  have hle : LinearMap.range (f.domRestrict W₁) ≤ commSpace (σ : T.Qt ≃ₗ[ZMod 2] T.Qt) := by
    rintro _ ⟨w, rfl⟩
    exact mem_commSpace.mpr ⟨w, rfl⟩
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hinj, L.finrank₁, hdim] at h1
  omega

theorem Xbar12_stab (g₀ : K) {s : T.O} (hs : s ∈ T.Xbar12 g₀) :
    (∀ w ∈ W₁, (s : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₁) ∧
      ∀ w ∈ W₂, (s : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₂ := by
  have hgen : ∀ τ ∈ T.Ebar12 g₀, (∀ w ∈ W₁, (τ : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₁) ∧
      ∀ w ∈ W₂, (τ : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₂ := by
    intro τ hτ
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hτ.1
    rcases L.map_eq m with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact ⟨fun w hw => h1 ▸ ⟨w, hw, rfl⟩, fun w hw => h2 ▸ ⟨w, hw, rfl⟩⟩
    · exact absurd (Setting.isTypeA_of_mem_Ebar12 hτ) (L.not_isTypeA_of_swap h1)
  induction hs using Subgroup.closure_induction'' with
  | mem τ hτ => exact hgen τ hτ
  | inv_mem τ hτ =>
    have hττ : τ * τ = 1 := Subtype.ext (Setting.isTypeA_of_mem_Ebar12 hτ).2.2.1
    rw [inv_eq_of_mul_eq_one_right hττ]
    exact hgen τ hτ
  | one => exact ⟨fun w hw => hw, fun w hw => hw⟩
  | mul x y _ _ hx hy =>
    exact ⟨fun w hw => hx.1 _ (hy.1 w hw), fun w hw => hx.2 _ (hy.2 w hw)⟩

theorem eq_one_of_fix {s : T.O} (h₁ : ∀ w ∈ W₁, (s : T.Qt ≃ₗ[ZMod 2] T.Qt) w = w)
    (h₂ : ∀ w ∈ W₂, (s : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₂) : s = 1 := by
  have hpol : ∀ {W : Submodule (ZMod 2) T.Qt}, (∀ w ∈ W, T.q w = 0) → ∀ u ∈ W, ∀ v ∈ W,
      polar T.q u v = 0 := fun hW u hu v hv => by
    rw [QuadraticMap.polar, hW _ (Submodule.add_mem _ hu hv), hW u hu, hW v hv, sub_zero,
      sub_zero]
  have hfix₂ : ∀ w ∈ W₂, (s : T.Qt ≃ₗ[ZMod 2] T.Qt) w = w := by
    intro w hw
    have hd : (s : T.Qt ≃ₗ[ZMod 2] T.Qt) w - w ∈ W₂ := W₂.sub_mem (h₂ w hw) hw
    refine sub_eq_zero.mp (T.q_nondegenerate.2 _ fun x => ?_)
    have hx : x ∈ W₁ ⊔ W₂ := by rw [L.sup]; exact Submodule.mem_top
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polarBilin_apply_apply, polar_add_left, hpol L.ts₂ x₂ hx₂ _ hd, add_zero,
      polar_sub_right, ← h₁ x₁ hx₁,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup s.2, h₁ x₁ hx₁, sub_self]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have hv : v ∈ W₁ ⊔ W₂ := by rw [L.sup]; exact Submodule.mem_top
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, h₁ v₁ hv₁, hfix₂ v₂ hv₂]
  rfl

end LatData

end CFSG.LargeExtraspecial.GLW4
