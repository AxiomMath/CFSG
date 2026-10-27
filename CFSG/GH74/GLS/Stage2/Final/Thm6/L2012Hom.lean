module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup

variable {G : Type} [Group G]

theorem exists_inj_hom {B X K : Subgroup G} (hXK : X ≤ K)
    (hZ : ∀ k ∈ X, (∀ x ∈ K, k * x = x * k) → k = 1)
    (hB : ∀ b ∈ B, ∃ k ∈ X, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹)
    (hinj : ∀ b ∈ B, (∀ x ∈ K, b * x = x * b) → b = 1) :
    ∃ φ : ↥B →* ↥X, Function.Injective φ := by
  classical
  have uniq : ∀ k ∈ X, ∀ k' ∈ X, (∀ x ∈ K, k * x * k⁻¹ = k' * x * k'⁻¹) → k = k' := by
    intro k hk k' hk' h
    have h1 : k'⁻¹ * k ∈ X := X.mul_mem (X.inv_mem hk') hk
    have h2 : k'⁻¹ * k = 1 := by
      refine hZ _ h1 (fun x hx => ?_)
      have := h x hx
      calc k'⁻¹ * k * x = k'⁻¹ * (k * x * k⁻¹) * k := by group
        _ = k'⁻¹ * (k' * x * k'⁻¹) * k := by rw [this]
        _ = x * (k'⁻¹ * k) := by group
    exact (inv_mul_eq_one.1 h2).symm
  let f : ↥B → ↥X := fun b => ⟨Classical.choose (hB b b.2), (Classical.choose_spec (hB b b.2)).1⟩
  have hf : ∀ b : ↥B, ∀ x ∈ K, (b : G) * x * (b : G)⁻¹ = (f b : G) * x * (f b : G)⁻¹ :=
    fun b => (Classical.choose_spec (hB b b.2)).2
  refine ⟨MonoidHom.mk' f (fun b b' => ?_), ?_⟩
  · apply Subtype.ext
    apply uniq _ (f (b * b')).2 _ (X.mul_mem (f b).2 (f b').2)
    intro x hx
    have h1 := hf (b * b') x hx
    have hy : (f b' : G) * x * (f b' : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (hXK (f b').2) hx) (K.inv_mem (hXK (f b').2))
    have h2 := hf b _ hy
    have h3 := hf b' x hx
    show (f (b * b') : G) * x * (f (b * b') : G)⁻¹ = ((f b : G) * (f b' : G)) * x * ((f b : G) * (f b' : G))⁻¹
    rw [← h1]
    calc ((b * b' : ↥B) : G) * x * ((b * b' : ↥B) : G)⁻¹
        = (b : G) * ((b' : G) * x * (b' : G)⁻¹) * (b : G)⁻¹ := by simp only [Subgroup.coe_mul]; group
      _ = (b : G) * ((f b' : G) * x * (f b' : G)⁻¹) * (b : G)⁻¹ := by rw [h3]
      _ = (f b : G) * ((f b' : G) * x * (f b' : G)⁻¹) * (f b : G)⁻¹ := h2
      _ = ((f b : G) * (f b' : G)) * x * ((f b : G) * (f b' : G))⁻¹ := by group
  · rw [injective_iff_map_eq_one]
    intro b hb
    have hb1 : f b = 1 := hb
    apply Subtype.ext
    apply hinj b b.2
    intro x hx
    have h1 := hf b x hx
    have : (f b : G) = 1 := by rw [hb1]; rfl
    rw [this] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    calc (b : G) * x = ((b : G) * x * (b : G)⁻¹) * b := by group
      _ = x * b := by rw [h1]

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
