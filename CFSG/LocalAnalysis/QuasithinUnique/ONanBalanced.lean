module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanFree
public import CFSG.LocalAnalysis.QuasithinUnique.ONanSpread

public section

namespace CFSG.QuasithinUnique.ONan

open Module
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {X R : Subgroup (V ≃ₗ[ZMod 2] V)} {A C : Submodule (ZMod 2) V}

structure Balanced (X R : Subgroup (V ≃ₗ[ZMod 2] V)) (A C : Submodule (ZMod 2) V) : Prop where
  setting : Setting X R A C
  irreducible : ∀ W : Submodule (ZMod 2) V, (∀ x ∈ X, ∀ v ∈ W, x v ∈ W) → W = ⊥ ∨ W = ⊤
  two_le : 2 ≤ finrank (ZMod 2) C
  finrank_eq : finrank (ZMod 2) A = finrank (ZMod 2) C
  free : ∀ r ∈ R, ∀ a ∈ A, a ≠ 0 → r a = a → r = 1
  ti : ∀ x ∈ X, C ⊓ x • C ≠ ⊥ → x • C = C
  norm : ∀ x ∈ X, x • C = C → ∀ r ∈ R, x * r * x⁻¹ ∈ R

theorem mem_orbit_iff' {D : Submodule (ZMod 2) V} :
    D ∈ MulAction.orbit X C ↔ ∃ x ∈ X, x • C = D :=
  ⟨fun ⟨g, hg⟩ => ⟨g, g.2, hg⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩⟩

theorem smul_mem_orbit {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ X) {D : Submodule (ZMod 2) V}
    (hD : D ∈ MulAction.orbit X C) : x • D ∈ MulAction.orbit X C := by
  obtain ⟨y, hy, rfl⟩ := mem_orbit_iff'.mp hD
  exact mem_orbit_iff'.mpr ⟨x * y, X.mul_mem hx hy, mul_smul x y C⟩

theorem finrank_orbit {D : Submodule (ZMod 2) V}
    (hD : D ∈ MulAction.orbit X C) : finrank (ZMod 2) D = finrank (ZMod 2) C := by
  obtain ⟨y, hy, rfl⟩ := mem_orbit_iff'.mp hD
  exact finrank_smul y C

theorem Balanced.ti_vec (h : Balanced X R A C) {z : V ≃ₗ[ZMod 2] V} (hz : z ∈ X) {v : V}
    (hvC : v ∈ C) (hv0 : v ≠ 0) (hzv : z⁻¹ v ∈ C) : z • C = C := by
  apply h.ti z hz
  rw [Submodule.ne_bot_iff]
  exact ⟨v, ⟨hvC, (mem_smul_iff z C v).mpr hzv⟩, hv0⟩

theorem Balanced.inf_eq_bot_of_mem (h : Balanced X R A C) {D E : Submodule (ZMod 2) V}
    (hD : D ∈ MulAction.orbit X C) (hE : E ∈ MulAction.orbit X C) (hDE : D ≠ E) :
    D ⊓ E = ⊥ := by
  obtain ⟨x, hx, rfl⟩ := mem_orbit_iff'.mp hD
  obtain ⟨y, hy, rfl⟩ := mem_orbit_iff'.mp hE
  by_contra hne
  obtain ⟨v, ⟨hv1, hv2⟩, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hz : x⁻¹ * y ∈ X := X.mul_mem (X.inv_mem hx) hy
  have hxv : x⁻¹ v ∈ C := (mem_smul_iff x C v).mp hv1
  have hxv0 : x⁻¹ v ≠ 0 := fun h0 => hv0 ((map_eq_zero_iff x⁻¹ x⁻¹.injective).mp h0)
  have hyv : y⁻¹ v ∈ C := (mem_smul_iff y C v).mp hv2
  have h1 : (x⁻¹ * y) • C = C := by
    refine h.ti_vec hz hxv hxv0 ?_
    have : (x⁻¹ * y)⁻¹ (x⁻¹ v) = y⁻¹ v := by simp
    rw [this]
    exact hyv
  apply hDE
  calc x • C = x • ((x⁻¹ * y) • C) := by rw [h1]
    _ = y • C := by rw [← mul_smul]; simp

theorem Balanced.two_le_A (h : Balanced X R A C) : 2 ≤ finrank (ZMod 2) A := by
  rw [h.finrank_eq]
  exact h.two_le

variable [Finite V]

theorem Balanced.eq_or_eq_of_fixed (h : Balanced X R A C) {D : Submodule (ZMod 2) V}
    (hD : D ∈ MulAction.orbit X C) (hfix : ∀ ρ ∈ R, ρ • D = D) : D = C ∨ D = A := by
  by_cases hDC : D = C
  · exact Or.inl hDC
  · right
    have hinf : D ⊓ C = ⊥ := h.inf_eq_bot_of_mem hD (MulAction.mem_orbit_self C) hDC
    obtain ⟨ρ, hρ, hρ1⟩ := h.setting.exists_ne_one h.two_le_A
    exact eq_of_smul_eq h.setting h.finrank_eq h.free hρ hρ1 hinf
      (by rw [finrank_orbit hD, h.finrank_eq]) (hfix ρ hρ)

theorem Balanced.finrank_space (h : Balanced X R A C) :
    finrank (ZMod 2) V = 2 * finrank (ZMod 2) C := by
  have := h.setting.finrank_space
  rw [h.finrank_eq] at this
  omega

theorem Balanced.ncard_orbit_le (h : Balanced X R A C) :
    (MulAction.orbit X C).ncard ≤ 2 ^ finrank (ZMod 2) C + 1 := by
  have hS : IsPartialSpread (finrank (ZMod 2) C)
      (fun D : ↥(MulAction.orbit X C) => (D : Submodule (ZMod 2) V)) :=
    ⟨h.finrank_space, fun D => finrank_orbit D.2,
      fun D E hDE => h.inf_eq_bot_of_mem D.2 E.2 (fun heq => hDE (Subtype.ext heq))⟩
  have := hS.natCard_le (by have := h.two_le; omega)
  rwa [Nat.card_coe_set_eq] at this

end CFSG.QuasithinUnique.ONan
