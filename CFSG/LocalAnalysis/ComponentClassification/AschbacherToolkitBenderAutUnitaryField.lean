module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitaryCoord

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace UnitaryField

open CFSG.BenderSuzuki.MatrixGroups

variable {K : Type*} [Field K]

theorem eq_or_eq_conj_of_quadratic (σ : K ≃+* K) {x u : K}
    (h : u ^ 2 - (x + σ x) * u + x * σ x = 0) : u = x ∨ u = σ x := by
  have h2 : (u - x) * (u - σ x) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl (sub_eq_zero.mp h3)
  · exact Or.inr (sub_eq_zero.mp h3)

theorem eq_id_or_eq_conj_of_fix (σ : K ≃+* K) (hσ : Function.Involutive σ) (θ : K →+* K)
    (hθ : ∀ t : K, σ t = t → θ t = t) : (∀ x, θ x = x) ∨ (∀ x, θ x = σ x) := by
  have hroot : ∀ x : K, θ x = x ∨ θ x = σ x := by
    intro x
    apply eq_or_eq_conj_of_quadratic σ
    have htr : σ (x + σ x) = x + σ x := by rw [map_add, hσ x, add_comm]
    have hn : σ (x * σ x) = x * σ x := by rw [map_mul, hσ x, mul_comm]
    have h0 : θ (x ^ 2 - (x + σ x) * x + x * σ x) = 0 := by
      have : x ^ 2 - (x + σ x) * x + x * σ x = 0 := by ring
      rw [this, map_zero]
    rw [map_add, map_sub, map_mul, map_pow, hθ _ htr, hθ _ hn] at h0
    exact h0
  let A : AddSubgroup K :=
    { carrier := {x | θ x = x}
      add_mem' := fun {a b} ha hb => by
        change θ (a + b) = a + b
        rw [map_add, show θ a = a from ha, show θ b = b from hb]
      zero_mem' := by
        change θ 0 = 0
        exact map_zero θ
      neg_mem' := fun {a} ha => by
        change θ (-a) = -a
        rw [map_neg, show θ a = a from ha] }
  let B : AddSubgroup K :=
    { carrier := {x | θ x = σ x}
      add_mem' := fun {a b} ha hb => by
        change θ (a + b) = σ (a + b)
        rw [map_add, map_add, show θ a = σ a from ha, show θ b = σ b from hb]
      zero_mem' := by
        change θ 0 = σ 0
        rw [map_zero, map_zero]
      neg_mem' := fun {a} ha => by
        change θ (-a) = σ (-a)
        rw [map_neg, map_neg, show θ a = σ a from ha] }
  have hcov : (⊤ : AddSubgroup K) ≤ A ∨ (⊤ : AddSubgroup K) ≤ B := by
    apply AddSubgroupClass.subset_union.mp
    intro x _
    rcases hroot x with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hcov with h | h
  · exact Or.inl fun x => h (AddSubgroup.mem_top x)
  · exact Or.inr fun x => h (AddSubgroup.mem_top x)

variable [Finite K]

theorem exists_decomp (σ : K ≃+* K) (q : ℕ) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // σ x = x} = q) {μ ν : K} (hμ : μ ≠ 0)
    (hν : ∀ r : K, σ r = r → ν ≠ μ * r) (x : K) :
    ∃ r₁ r₂ : K, σ r₁ = r₁ ∧ σ r₂ = r₂ ∧ x = μ * r₁ + ν * r₂ := by
  classical
  let F := {x : K // σ x = x}
  let f : F × F → K := fun p => μ * (p.1 : K) + ν * (p.2 : K)
  have hinj : Function.Injective f := by
    rintro ⟨r₁, r₂⟩ ⟨r₁', r₂'⟩ h
    change μ * (r₁ : K) + ν * r₂ = μ * r₁' + ν * r₂' at h
    by_cases h2 : (r₂ : K) = r₂'
    · have h1 : μ * (r₁ : K) = μ * r₁' := by rw [h2] at h; exact add_right_cancel h
      have h1' : (r₁ : K) = r₁' := mul_left_cancel₀ hμ h1
      rw [Prod.mk.injEq]
      exact ⟨Subtype.ext h1', Subtype.ext h2⟩
    · exfalso
      have hd : (r₂' : K) - r₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h2)
      apply hν (((r₁ : K) - r₁') / ((r₂' : K) - r₂))
      · rw [map_div₀, map_sub, map_sub, r₁.2, r₁'.2, r₂.2, r₂'.2]
      · field_simp
        linear_combination -h
  have hcardF : Nat.card (F × F) = Nat.card K := by
    rw [Nat.card_prod, hfixed, hcard, sq]
  have hsurj : Function.Surjective f := (hinj.bijective_of_nat_card_le hcardF.ge).2
  obtain ⟨⟨r₁, r₂⟩, hp⟩ := hsurj x
  exact ⟨r₁, r₂, r₁.2, r₂.2, hp.symm⟩

theorem additive_eq_zero [CharP K 2] (σ : K ≃+* K) (q : ℕ) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // σ x = x} = q) (S : Set K)
    (hS : ∀ r : K, σ r = r → r ≠ 0 → r ∈ S) {s₀ : K} (hs₀S : s₀ ∈ S) (hs₀ : σ s₀ ≠ s₀)
    (κ : K →+ K) (hκ : ∀ x, σ (κ x) = κ x) (hκS : ∀ s ∈ S, ∀ x, κ (x * s) = s * σ s * κ x) :
    ∀ x, κ x = 0 := by
  classical
  have hq : q < q ^ 2 := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hcard] at h1
    have hq1 : 1 < q := by
      by_contra h
      push Not at h
      interval_cases q <;> simp at h1
    calc q = q * 1 := (mul_one q).symm
      _ < q * q := Nat.mul_lt_mul_of_pos_left hq1 (by omega)
      _ = q ^ 2 := (sq q).symm
  obtain ⟨μ, hμ, hμκ⟩ : ∃ μ : K, μ ≠ 0 ∧ κ μ = 0 := by
    by_contra hcon
    push Not at hcon
    let g : K → {x : K // σ x = x} := fun x => ⟨κ x, hκ x⟩
    have hg : Function.Injective g := by
      intro a b hab
      have h1 : κ (a - b) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val hab
      by_contra hne
      exact hcon (a - b) (sub_ne_zero.mpr hne) h1
    have hle := Nat.card_le_card_of_injective g hg
    rw [hfixed, hcard] at hle
    omega
  have hκF : ∀ r : K, σ r = r → ∀ x, κ (x * r) = r ^ 2 * κ x := by
    intro r hr x
    by_cases hr0 : r = 0
    · rw [hr0, mul_zero, map_zero]
      ring
    · rw [hκS r (hS r hr hr0) x, hr, sq]
  by_contra hcon
  push Not at hcon
  obtain ⟨ν, hν⟩ := hcon
  have hνμ : ∀ r : K, σ r = r → ν ≠ μ * r := by
    intro r hr h
    apply hν
    rw [h, hκF r hr μ, hμκ, mul_zero]
  obtain ⟨r₁, r₂, hr₁, hr₂, hdec⟩ := exists_decomp σ q hcard hfixed hμ hνμ (μ * s₀)
  have h0 : κ (μ * s₀) = 0 := by rw [hκS s₀ hs₀S μ, hμκ, mul_zero]
  rw [hdec, map_add, hκF r₁ hr₁ μ, hκF r₂ hr₂ ν, hμκ, mul_zero, zero_add] at h0
  have hr₂0 : r₂ = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact (pow_eq_zero_iff (by norm_num)).mp h
    · exact absurd h hν
  rw [hr₂0, mul_zero, add_zero] at hdec
  have hs : s₀ = r₁ := mul_left_cancel₀ hμ hdec
  exact hs₀ (hs ▸ hr₁)

end UnitaryField

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
