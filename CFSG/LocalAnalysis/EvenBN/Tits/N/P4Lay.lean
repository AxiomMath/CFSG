module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Aut
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup

variable {L : Type*} [Group L] [Finite L]

theorem comm_mem_trivOn (hcomm : ∀ a b : L, a * b = b * a) {Z E : Subgroup L} (hZE : Z ≤ E)
    {a b : MulAut L} (ha1 : a ∈ trivOn Z E hZE) (ha2 : a ∈ trivOn E ⊤ le_top)
    (hb1 : b ∈ trivOn Z E hZE) (hb2 : b ∈ trivOn E ⊤ le_top) :
    a * b * a⁻¹ * b⁻¹ ∈ trivOn Z ⊤ (hZE.trans le_top) := by
  have key : ∀ l : L, a (b l) * (b (a l))⁻¹ ∈ Z := by
    intro l
    obtain ⟨α, hαE, hαdef⟩ : ∃ α ∈ E, a l = α * l :=
      ⟨a l * l⁻¹, mem_trivOn.1 ha2 l (mem_top l), by group⟩
    obtain ⟨β, hβE, hβdef⟩ : ∃ β ∈ E, b l = β * l :=
      ⟨b l * l⁻¹, mem_trivOn.1 hb2 l (mem_top l), by group⟩
    obtain ⟨ζ₁, hζ₁, h1⟩ : ∃ ζ₁ ∈ Z, a β = ζ₁ * β := ⟨a β * β⁻¹, mem_trivOn.1 ha1 β hβE, by group⟩
    obtain ⟨ζ₂, hζ₂, h2⟩ : ∃ ζ₂ ∈ Z, b α = ζ₂ * α := ⟨b α * α⁻¹, mem_trivOn.1 hb1 α hαE, by group⟩
    have hA : a (b l) = ζ₁ * (α * β * l) := by
      rw [hβdef, map_mul, h1, hαdef]
      calc ζ₁ * β * (α * l) = ζ₁ * ((β * α) * l) := by group
        _ = ζ₁ * ((α * β) * l) := by rw [hcomm β α]
    have hB : b (a l) = ζ₂ * (α * β * l) := by
      rw [hαdef, map_mul, h2, hβdef]
      group
    rw [hA, hB]
    have : ζ₁ * (α * β * l) * (ζ₂ * (α * β * l))⁻¹ = ζ₁ * ζ₂⁻¹ := by group
    rw [this]
    exact Z.mul_mem hζ₁ (Z.inv_mem hζ₂)
  rw [mem_trivOn]
  intro x _
  set l₀ := (b * a)⁻¹ x with hl₀
  have hx : x = (b * a) l₀ := by simp [hl₀]
  have hc : (a * b * a⁻¹ * b⁻¹) ((b * a) l₀) = (a * b) l₀ := by
    have : (a * b * a⁻¹ * b⁻¹) * (b * a) = a * b := by group
    rw [← MulAut.mul_apply, this]
  rw [hx, hc]
  exact key l₀

theorem elemAb_of_layers (hcomm : ∀ a b : L, a * b = b * a) (hsq : ∀ a : L, a * a = 1)
    {Z E : Subgroup L} (hZE : Z ≤ E) {W U : Subgroup (MulAut L)} {t : MulAut L}
    (hWZ : ∀ w ∈ W, ∀ ζ ∈ Z, w ζ = ζ)
    (hW1 : ∀ w ∈ W, w ∈ trivOn Z E hZE) (hW2 : ∀ w ∈ W, w ∈ trivOn E ⊤ le_top)
    (ht1 : t ∈ trivOn Z E hZE) (ht2 : t ∈ trivOn E ⊤ le_top)
    (hWU : ∀ w ∈ W, ∀ u ∈ U, w * u = u * w)
    (hreg : ∀ u ∈ U, ∃ w ∈ W, w * t * w⁻¹ * t⁻¹ = u)
    (hC : ∀ l : L, (∀ u ∈ U, u l = l) → l ∈ Z) :
    (∀ w ∈ W, ∀ l : L, w l * l⁻¹ ∈ Z) ∧ (∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) ∧
      ∀ w ∈ W, w * w = 1 := by
  have hU : ∀ u ∈ U, u ∈ trivOn Z ⊤ (hZE.trans le_top) := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := hreg u hu
    exact comm_mem_trivOn hcomm hZE (hW1 w hw) (hW2 w hw) ht1 ht2
  have hZW : ∀ w ∈ W, ∀ l : L, w l * l⁻¹ ∈ Z := by
    intro w' hw' l
    apply hC
    intro u hu
    obtain ⟨ζ, hζ, hζdef⟩ : ∃ ζ ∈ Z, u l = ζ * l :=
      ⟨u l * l⁻¹, mem_trivOn.1 (hU u hu) l (mem_top l), by group⟩
    have hcu : w' (u l) = u (w' l) := by
      have := congrArg (fun φ : MulAut L => φ l) (hWU w' hw' u hu)
      exact this
    have h1 : u (w' l) = ζ * w' l := by
      rw [← hcu, hζdef, map_mul, hWZ w' hw' ζ hζ]
    have e : u (w' l * l⁻¹) = ζ * w' l * (ζ * l)⁻¹ := by
      rw [map_mul, map_inv, h1, hζdef]
    rw [e]
    calc ζ * w' l * (ζ * l)⁻¹ = ζ * (w' l * l⁻¹) * ζ⁻¹ := by group
      _ = (w' l * l⁻¹) * ζ * ζ⁻¹ := by rw [hcomm ζ (w' l * l⁻¹)]
      _ = w' l * l⁻¹ := by group
  refine ⟨hZW, fun w hw w' hw' => ?_, fun w hw => ?_⟩
  · ext l
    obtain ⟨ζ, hζ, hζdef⟩ : ∃ ζ ∈ Z, w l = ζ * l := ⟨w l * l⁻¹, hZW w hw l, by group⟩
    obtain ⟨ζ', hζ', hζ'def⟩ : ∃ ζ' ∈ Z, w' l = ζ' * l := ⟨w' l * l⁻¹, hZW w' hw' l, by group⟩
    show w (w' l) = w' (w l)
    rw [hζ'def, hζdef, map_mul, map_mul, hWZ w hw ζ' hζ', hWZ w' hw' ζ hζ, hζdef, hζ'def]
    rw [← mul_assoc, hcomm ζ' ζ, mul_assoc]
  · ext l
    obtain ⟨ζ, hζ, hζdef⟩ : ∃ ζ ∈ Z, w l = ζ * l := ⟨w l * l⁻¹, hZW w hw l, by group⟩
    show w (w l) = l
    rw [hζdef, map_mul, hWZ w hw ζ hζ, hζdef, ← mul_assoc, hsq ζ, one_mul]

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
