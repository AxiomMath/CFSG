module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

theorem eq_bot_of_fourGroup {Γ : Type*} [Group Γ] [Finite Γ] (K : Subgroup Γ) (a b : Γ)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (haK : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hbK : ∀ k ∈ K, b * k * b⁻¹ ∈ K)
    (h1 : ∀ k ∈ K, a * k = k * a → k = 1) (h2 : ∀ k ∈ K, b * k = k * b → k = 1)
    (h3 : ∀ k ∈ K, (a * b) * k = k * (a * b) → k = 1) : K = ⊥ := by
  have key : ∀ c : Γ, c * c = 1 → (∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      (∀ k ∈ K, c * k = k * c → k = 1) → ∀ k ∈ K, c * k * c⁻¹ = k⁻¹ := by
    intro c hc2 hcK hc1
    have hc : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    let f : K → K := fun k => ⟨k⁻¹ * (c * k * c⁻¹), K.mul_mem (K.inv_mem k.2) (hcK k k.2)⟩
    have hf : Function.Injective f := by
      intro k l hkl
      have hkl' : (k : Γ)⁻¹ * (c * k * c⁻¹) = (l : Γ)⁻¹ * (c * l * c⁻¹) :=
        congrArg Subtype.val hkl
      have hcomm : c * ((l : Γ) * (k : Γ)⁻¹) = ((l : Γ) * (k : Γ)⁻¹) * c := by
        calc c * ((l : Γ) * (k : Γ)⁻¹)
            = (l : Γ) * ((l : Γ)⁻¹ * (c * l * c⁻¹)) * c * (k : Γ)⁻¹ := by group
          _ = (l : Γ) * ((k : Γ)⁻¹ * (c * k * c⁻¹)) * c * (k : Γ)⁻¹ := by rw [hkl']
          _ = ((l : Γ) * (k : Γ)⁻¹) * c := by group
      have hlk : (l : Γ) * (k : Γ)⁻¹ = 1 := hc1 _ (K.mul_mem l.2 (K.inv_mem k.2)) hcomm
      exact Subtype.ext (mul_inv_eq_one.1 hlk).symm
    intro x hx
    obtain ⟨k, hk⟩ := Finite.injective_iff_surjective.1 hf ⟨x, hx⟩
    have hkx : (k : Γ)⁻¹ * (c * k * c⁻¹) = x := congrArg Subtype.val hk
    have hc2' : c⁻¹ * c⁻¹ = 1 := by rw [hc, hc2]
    have hcc : c * (c * k * c⁻¹) * c⁻¹ = (k : Γ) := by
      calc c * (c * k * c⁻¹) * c⁻¹ = (c * c) * k * (c⁻¹ * c⁻¹) := by group
        _ = k := by rw [hc2, hc2', one_mul, mul_one]
    rw [← hkx]
    calc c * ((k : Γ)⁻¹ * (c * k * c⁻¹)) * c⁻¹
        = (c * k * c⁻¹)⁻¹ * (c * (c * k * c⁻¹) * c⁻¹) := by group
      _ = (c * k * c⁻¹)⁻¹ * k := by rw [hcc]
      _ = ((k : Γ)⁻¹ * (c * k * c⁻¹))⁻¹ := by group
  have hA := key a ha2 haK h1
  have hB := key b hb2 hbK h2
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  refine h3 k hk ?_
  have hk' : a * (b * k * b⁻¹) * a⁻¹ = k := by
    rw [hB k hk, hA k⁻¹ (K.inv_mem hk), inv_inv]
  calc a * b * k = (a * (b * k * b⁻¹) * a⁻¹) * (a * b) := by group
    _ = k * (a * b) := by rw [hk']

end CFSG.EvenSporadicStandard.M12Std.Yosh
