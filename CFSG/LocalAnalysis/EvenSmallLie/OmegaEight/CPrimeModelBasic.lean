module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open Subgroup

theorem exists_coset_rep {X : Type*} [Group X] {H K : Subgroup X} [Finite K] {m : ℕ}
    (w : Fin m → X) (hw : ∀ j, w j ∈ K) (hHK : H ≤ K) (hcard : Nat.card K = m * Nat.card H)
    (hinj : ∀ i j, w j * (w i)⁻¹ ∈ H → i = j) {x : X} (hx : x ∈ K) :
    ∃ j, x * (w j)⁻¹ ∈ H := by
  have : Finite H := Finite.of_injective (inclusion hHK) (inclusion_injective hHK)
  let f : H × Fin m → K := fun p => ⟨p.1 * w p.2, mul_mem (hHK p.1.2) (hw p.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨h, i⟩ ⟨h', j⟩ e
    have e' : (h : X) * w i = h' * w j := congrArg Subtype.val e
    have hij : i = j := hinj i j (by
      have e2 : w j * (w i)⁻¹ = (h' : X)⁻¹ * h := by
        calc w j * (w i)⁻¹ = (h' : X)⁻¹ * (h' * w j) * (w i)⁻¹ := by group
          _ = (h' : X)⁻¹ * (h * w i) * (w i)⁻¹ := by rw [e']
          _ = (h' : X)⁻¹ * h := by group
      rw [e2]
      exact mul_mem (inv_mem h'.2) h.2)
    subst hij
    have hh : h = h' := Subtype.ext (mul_right_cancel e')
    rw [hh]
  have hb : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).2 ⟨hf, by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, hcard,
      mul_comm]⟩
  obtain ⟨⟨h, j⟩, e⟩ := hb.2 ⟨x, hx⟩
  refine ⟨j, ?_⟩
  have e' : (h : X) * w j = x := congrArg Subtype.val e
  rw [← e', mul_inv_cancel_right]
  exact h.2

variable {G X : Type*} [Group G] [Group X]

theorem exists_rechoice {L : Subgroup G} {L' : Subgroup X} (θ : L ≃* L') {c : G}
    (hcL : c ∈ normalizer (L : Set G)) {g σ : X}
    (hg : ∀ l l' : L, (l' : G) = c * l * c⁻¹ → g * (θ l : X) * g⁻¹ = θ l')
    (hgσ : g⁻¹ * σ ∈ L') (hσ : σ * σ = 1) :
    ∃ m ∈ L, c * m * (c * m) ∈ centralizer (L : Set G) ∧
      ∀ l l' : L, (l' : G) = c * m * l * (c * m)⁻¹ → σ * (θ l : X) * σ⁻¹ = θ l' := by
  set m₀ : L := θ.symm ⟨g⁻¹ * σ, hgσ⟩ with hm₀
  have hθm : (θ m₀ : X) = g⁻¹ * σ := by rw [hm₀, MulEquiv.apply_symm_apply]
  have hcmL : c * m₀ ∈ normalizer (L : Set G) := mul_mem hcL (le_normalizer m₀.2)
  have hact : ∀ l l' : L, (l' : G) = c * m₀ * l * (c * m₀)⁻¹ →
      σ * (θ l : X) * σ⁻¹ = θ l' := by
    intro l l' hl'
    set k : L := m₀ * l * m₀⁻¹ with hk
    have h1 := hg k l' (by rw [hl', hk]; simp only [coe_mul, coe_inv]; group)
    have h2 : (θ k : X) = g⁻¹ * σ * θ l * (g⁻¹ * σ)⁻¹ := by
      rw [hk, map_mul, map_mul, map_inv]
      simp only [coe_mul, coe_inv, hθm]
    rw [← h1, h2]
    group
  refine ⟨m₀, m₀.2, mem_centralizer_iff.2 fun x hx => ?_, hact⟩
  set y : L := ⟨c * m₀ * x * (c * m₀)⁻¹, (mem_normalizer_iff.1 hcmL x).1 hx⟩ with hy
  set z : L := ⟨c * m₀ * y * (c * m₀)⁻¹, (mem_normalizer_iff.1 hcmL y).1 y.2⟩ with hz
  have h1 := hact ⟨x, hx⟩ y rfl
  have h2 := hact y z rfl
  have h3 : (θ z : X) = θ ⟨x, hx⟩ := by
    rw [← h2, ← h1]
    calc σ * (σ * (θ ⟨x, hx⟩ : X) * σ⁻¹) * σ⁻¹ = σ * σ * θ ⟨x, hx⟩ * (σ * σ)⁻¹ := by group
      _ = θ ⟨x, hx⟩ := by rw [hσ, one_mul, inv_one, mul_one]
  have h4 : (z : G) = x := congrArg Subtype.val (θ.injective (Subtype.ext h3))
  rw [hz, hy] at h4
  change c * m₀ * (c * m₀ * x * (c * m₀)⁻¹) * (c * m₀)⁻¹ = x at h4
  calc x * (c * m₀ * (c * m₀)) = c * m₀ * (c * m₀ * x * (c * m₀)⁻¹) * (c * m₀)⁻¹ *
        (c * m₀ * (c * m₀)) := by rw [h4]
    _ = c * m₀ * (c * m₀) * x := by group

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel
