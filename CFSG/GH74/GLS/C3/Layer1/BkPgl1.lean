module

public import CFSG.GH74.GLS.C3.Layer1.BkIvk10Stmt
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_mem_coset_of_normal {X N Q : Subgroup G} (hQ2 : IsPGroup 2 ↥Q)
    (hN : Odd (Nat.card N)) (hNX : N ≤ X) (hQX : ∀ q ∈ Q, ∀ k ∈ X, q * k * q⁻¹ ∈ X)
    (hQN : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) {k : G} (hk : k ∈ X)
    (hQt : ∀ q ∈ Q, k⁻¹ * (q * k * q⁻¹) ∈ N) :
    ∃ c ∈ X, (∀ q ∈ Q, c * q = q * c) ∧ k⁻¹ * c ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set G := {s | s ∈ X ∧ k⁻¹ * s ∈ N}
  have hS : ∀ q ∈ Q, ∀ s ∈ S, q * s * q⁻¹ ∈ S := by
    intro q hq s hs
    obtain ⟨hsX, hsN⟩ := hs
    refine ⟨hQX q hq s hsX, ?_⟩
    have e : k⁻¹ * (q * s * q⁻¹) = (k⁻¹ * (q * k * q⁻¹)) * (q * (k⁻¹ * s) * q⁻¹) := by group
    rw [e]
    exact N.mul_mem (hQt q hq) (hQN q hq _ hsN)
  let inst : MulAction ↥Q ↥S :=
    { smul := fun q s => ⟨(q : G) * s * (q : G)⁻¹, hS q q.2 s s.2⟩
      one_smul := fun s => Subtype.ext (by
        show ((1 : ↥Q) : G) * s * ((1 : ↥Q) : G)⁻¹ = s
        simp)
      mul_smul := fun a b s => Subtype.ext (by
        show ((a * b : ↥Q) : G) * s * ((a * b : ↥Q) : G)⁻¹ =
          (a : G) * ((b : G) * s * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hcard : ¬ 2 ∣ Nat.card ↥S := by
    let e : ↥N ≃ ↥S :=
      { toFun := fun n => ⟨k * n, X.mul_mem hk (hNX n.2), by simp⟩
        invFun := fun s => ⟨k⁻¹ * s, s.2.2⟩
        left_inv := fun n => Subtype.ext (by simp)
        right_inv := fun s => Subtype.ext (by simp) }
    rw [← Nat.card_congr e]
    exact fun hd => (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 hd)
  have : Finite ↥S := Subtype.finite
  obtain ⟨⟨c, hcX, hcN⟩, hfix⟩ := hQ2.nonempty_fixed_point_of_prime_not_dvd_card ↥S hcard
  refine ⟨c, hcX, fun q hq => ?_, hcN⟩
  have h : q * c * q⁻¹ = c := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix ⟨q, hq⟩)
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

omit [Finite G] in
theorem exists_good_element {P Q V : Subgroup G} {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hPQbot : P ⊓ Q = ⊥) (hV : V ≤ P ⊔ Q)
    [Finite ↥Q] (hVcard : Nat.card ↥V = 4) (hQcard : Nat.card ↥Q = 4) :
    ∃ v ∈ V, v ≠ 1 ∧ (v ∈ P ∨ ∃ p ∈ P, v = p * x) := by
  have hcomm' : ∀ p' ∈ P, ∀ q ∈ Q, q * p' * q⁻¹ = p' := by
    intro p' hp' q hq
    calc q * p' * q⁻¹ = p' * q * q⁻¹ := by rw [← hPQ p' hp' q hq]
      _ = p' := by group
  have hQnorm : Q ≤ normalizer (P : Set G) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      rw [hcomm' p hp q hq]
      exact hp
    · intro hp
      have h3 := hcomm' _ hp q⁻¹ (Q.inv_mem hq)
      have e : q⁻¹ * (q * p * q⁻¹) * q⁻¹⁻¹ = p := by group
      rw [e] at h3
      rw [h3]
      exact hp
  by_cases hVP : ∃ v ∈ V, v ≠ 1 ∧ v ∈ P
  · obtain ⟨v, hv, hv1, hvP⟩ := hVP
    exact ⟨v, hv, hv1, Or.inl hvP⟩
  · have hVP' : ∀ v ∈ V, v ≠ 1 → v ∉ P := fun v hv hv1 hvP => hVP ⟨v, hv, hv1, hvP⟩
    have hdec : ∀ v : ↥V, ∃ q : ↥Q, ∃ p ∈ P, (v : G) = p * q := by
      intro v
      have hv : (v : G) ∈ ((P ⊔ Q : Subgroup G) : Set G) := hV v.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left P Q hQnorm] at hv
      obtain ⟨p, hp, q, hq, hpq⟩ := hv
      exact ⟨⟨q, hq⟩, p, hp, hpq.symm⟩
    choose f hf using hdec
    have hinj : Function.Injective f := by
      intro v₁ v₂ h12
      obtain ⟨p₁, hp₁, h1⟩ := hf v₁
      obtain ⟨p₂, hp₂, h2⟩ := hf v₂
      rw [h12] at h1
      have hmem : (v₁ : G) * (v₂ : G)⁻¹ ∈ P := by
        have e : (v₁ : G) * (v₂ : G)⁻¹ = p₁ * p₂⁻¹ := by
          rw [h1, h2]; group
        rw [e]
        exact P.mul_mem hp₁ (P.inv_mem hp₂)
      have hmemV : (v₁ : G) * (v₂ : G)⁻¹ ∈ V := V.mul_mem v₁.2 (V.inv_mem v₂.2)
      by_contra hne
      have hne' : (v₁ : G) * (v₂ : G)⁻¹ ≠ 1 := by
        intro h
        apply hne
        exact Subtype.ext (mul_inv_eq_one.1 h)
      exact hVP' _ hmemV hne' hmem
    have hbij : Function.Bijective f :=
      Function.Injective.bijective_of_nat_card_le hinj (by rw [hVcard, hQcard])
    obtain ⟨v, hv⟩ := hbij.2 ⟨x, hxQ⟩
    obtain ⟨p, hp, hvp⟩ := hf v
    rw [hv] at hvp
    refine ⟨v, v.2, ?_, Or.inr ⟨p, hp, hvp⟩⟩
    intro h1
    have h2 : p * x = 1 := by rw [← hvp]; exact h1
    have hxP : x ∈ P := by
      have : x = p⁻¹ := by
        have := congrArg (fun z => p⁻¹ * z) h2
        simpa using this
      rw [this]
      exact P.inv_mem hp
    have : x ∈ P ⊓ Q := ⟨hxP, hxQ⟩
    rw [hPQbot, Subgroup.mem_bot] at this
    exact hx1 this

end CFSG.GH74.GLS.C3.Layer1.Bk
