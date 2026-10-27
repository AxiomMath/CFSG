module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

section SemiField

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem semi_exists_trace_one (θ : F →+* F) (hθ : θ ≠ RingHom.id F) (hθθ : ∀ r, θ (θ r) = r) :
    ∃ t : F, t + θ t = 1 := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : F, θ c₀ ≠ c₀ := by
    by_contra h
    push Not at h
    exact hθ (RingHom.ext h)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hτ : c₀ + θ c₀ ≠ 0 := by
    intro h
    apply hc₀
    linear_combination h - c₀ * h2
  have hθτ : θ (c₀ + θ c₀) = c₀ + θ c₀ := by
    rw [map_add, hθθ, add_comm]
  refine ⟨c₀ * (c₀ + θ c₀)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hθτ, ← add_mul, mul_inv_cancel₀ hτ]

@[expose] def semi_fix (θ : F →+* F) : AddSubgroup F where
  carrier := {x | θ x = x}
  zero_mem' := map_zero θ
  add_mem' := fun {x y} hx hy => by
    show θ (x + y) = x + y
    rw [map_add, show θ x = x from hx, show θ y = y from hy]
  neg_mem' := fun {x} hx => by
    show θ (-x) = -x
    rw [map_neg, show θ x = x from hx]

theorem semi_mem_fix {θ : F →+* F} {x : F} : x ∈ semi_fix θ ↔ θ x = x := Iff.rfl

theorem semi_sq_add_mem {θ : F →+* F} {x : F} (hx : θ x = x) :
    θ (x ^ 2 + x) = x ^ 2 + x := by
  rw [map_add, map_pow, hx]

@[expose] def semi_P (θ : F →+* F) : semi_fix θ →+ semi_fix θ :=
  AddMonoidHom.mk'
    (fun s => ⟨(s : F) ^ 2 + (s : F), semi_mem_fix.mpr (semi_sq_add_mem (semi_mem_fix.mp s.2))⟩)
    (fun s s' => by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      apply Subtype.ext
      show ((s + s' : semi_fix θ) : F) ^ 2 + ((s + s' : semi_fix θ) : F)
          = ((s : F) ^ 2 + (s : F)) + ((s' : F) ^ 2 + (s' : F))
      rw [AddSubgroup.coe_add]
      linear_combination ((s : F) * (s' : F)) * h2)

theorem semi_P_val {θ : F →+* F} (s : semi_fix θ) :
    ((semi_P θ s : semi_fix θ) : F) = (s : F) ^ 2 + (s : F) := rfl

theorem semi_mem_ker_P {θ : F →+* F} (x : semi_fix θ) :
    x ∈ (semi_P θ).ker ↔ (x : F) ^ 2 + (x : F) = 0 := by
  rw [AddMonoidHom.mem_ker, Subtype.ext_iff]
  exact Iff.rfl

theorem semi_sq_add_eq_zero_iff (u : F) : u ^ 2 + u = 0 ↔ u = 0 ∨ u = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have hm : u * (u + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hm with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h0 - h2)
  · rintro (h0 | h0)
    · linear_combination (u + 1) * h0
    · linear_combination (u + 2) * h0 + h2

theorem semi_card_ker_P (θ : F →+* F) : Nat.card (semi_P θ).ker = 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : (1 : F) ∈ semi_fix θ := semi_mem_fix.mpr (map_one θ)
  have hk1 : (⟨1, h1⟩ : semi_fix θ) ∈ (semi_P θ).ker :=
    (semi_mem_ker_P _).mpr (by show (1 : F) ^ 2 + 1 = 0; linear_combination h2)
  rw [Nat.card_eq_two_iff]
  refine ⟨0, ⟨⟨1, h1⟩, hk1⟩, ?_, ?_⟩
  · intro h
    exact zero_ne_one (congrArg (fun z : (semi_P θ).ker => ((z : semi_fix θ) : F)) h)
  · apply Set.eq_univ_of_forall
    rintro ⟨⟨u, hu⟩, hz⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (semi_sq_add_eq_zero_iff u).mp ((semi_mem_ker_P _).mp hz) with h0 | h0
    · exact Or.inl (Subtype.ext (Subtype.ext h0))
    · exact Or.inr (Subtype.ext (Subtype.ext h0))

theorem semi_index_range_P (θ : F →+* F) : (semi_P θ).range.index = 2 := by
  have hA := AddSubgroup.card_ker_mul_card_range (semi_P θ)
  have hB := AddSubgroup.card_mul_index (H := (semi_P θ).range)
  rw [semi_card_ker_P] at hA
  have hpos : 0 < Nat.card (semi_P θ).range := Nat.card_pos
  have hmul : Nat.card (semi_P θ).range * (semi_P θ).range.index
      = Nat.card (semi_P θ).range * 2 := by
    rw [hB]
    omega
  exact Nat.eq_of_mul_eq_mul_left hpos hmul

theorem semi_sq_add_ne {θ : F →+* F} {t : F} (hθt : θ t = t + 1) {s : F} (hs : θ s = s) :
    s ^ 2 + s ≠ t ^ 2 + t := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  intro h
  have hu : (t + s) ^ 2 + (t + s) = 0 := by
    linear_combination h + (t ^ 2 + t + t * s) * h2
  have hθu : θ (t + s) = t + s := by
    rcases (semi_sq_add_eq_zero_iff (t + s)).mp hu with h0 | h0
    · rw [h0, map_zero]
    · rw [h0, map_one]
  rw [map_add, hθt, hs] at hθu
  have h10 : (1 : F) = 0 := by linear_combination hθu
  exact one_ne_zero h10

theorem semi_artin_schreier (θ : F →+* F) (hθ : θ ≠ RingHom.id F) (hθθ : ∀ r, θ (θ r) = r)
    {δ : F} (hδ : θ δ = δ) : ∃ d : F, d ^ 2 + d = δ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨t, ht⟩ := semi_exists_trace_one θ hθ hθθ
  have hθt : θ t = t + 1 := by linear_combination ht - t * h2
  have hδ₀ : θ (t ^ 2 + t) = t ^ 2 + t := by
    rw [map_add, map_pow, hθt]
    linear_combination (t + 1) * h2
  obtain ⟨δ₀, hδ₀val⟩ : ∃ e : semi_fix θ, (e : F) = t ^ 2 + t :=
    ⟨⟨t ^ 2 + t, semi_mem_fix.mpr hδ₀⟩, rfl⟩
  have hnot : δ₀ ∉ (semi_P θ).range := by
    intro h
    obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp h
    have hv := congrArg Subtype.val hy
    rw [semi_P_val, hδ₀val] at hv
    exact semi_sq_add_ne hθt (semi_mem_fix.mp y.2) hv
  obtain ⟨a, ha⟩ := AddSubgroup.index_eq_two_iff.mp (semi_index_range_P θ)
  have hc : δ₀ + a ∈ (semi_P θ).range := by
    rcases ha δ₀ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hnot
  have key : ∀ b : semi_fix θ, b ∈ (semi_P θ).range ∨ b - δ₀ ∈ (semi_P θ).range := by
    intro b
    by_cases hb : b ∈ (semi_P θ).range
    · exact Or.inl hb
    · right
      have hba : b + a ∈ (semi_P θ).range := by
        rcases ha b with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · exact absurd h1 hb
      have e : b - δ₀ = (b + a) - (δ₀ + a) := by abel
      rw [e]
      exact sub_mem hba hc
  rcases key ⟨δ, semi_mem_fix.mpr hδ⟩ with hmem | hmem
  · obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp hmem
    refine ⟨(y : F), ?_⟩
    have hv := congrArg Subtype.val hy
    rw [semi_P_val] at hv
    exact hv
  · obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp hmem
    have hv : (y : F) ^ 2 + (y : F) = δ - (δ₀ : F) := by
      have hv' := congrArg Subtype.val hy
      rw [semi_P_val] at hv'
      exact hv'
    rw [hδ₀val] at hv
    refine ⟨t + (y : F), ?_⟩
    linear_combination hv + (t * (y : F)) * h2

theorem semi_exists_zero_binary (θ : F →+* F) (hθ : θ ≠ RingHom.id F) (hθθ : ∀ r, θ (θ r) = r)
    {α β γ : F} (hα : θ α = α) (hβ : θ β = β) (hγ : θ γ = γ) :
    ∃ c₁ c₂ : F, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ α * c₁ ^ 2 + β * c₁ * c₂ + γ * c₂ ^ 2 = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases hα0 : α = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by rw [hα0]; ring⟩
  by_cases hβ0 : β = 0
  ·
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (γ / α)
    refine ⟨r, 1, Or.inr one_ne_zero, ?_⟩
    have : γ = α * (r * r) := by
      rw [← hr]
      field_simp
    rw [hβ0, this]
    linear_combination (α * (r * r)) * h2
  ·
    have hδ : θ (α * γ / β ^ 2) = α * γ / β ^ 2 := by
      rw [map_div₀, map_mul, map_pow, hα, hβ, hγ]
    obtain ⟨d, hd⟩ := semi_artin_schreier θ hθ hθθ hδ
    refine ⟨β / α * d, 1, Or.inr one_ne_zero, ?_⟩
    have h1 : d ^ 2 + d = α * γ / β ^ 2 := hd
    have h3 : γ = (β ^ 2 / α) * (d ^ 2 + d) := by
      rw [h1]
      field_simp
    rw [h3]
    field_simp
    linear_combination (β ^ 2 * d ^ 2 + β ^ 2 * d) * h2

end SemiField

section SemiDecomp

variable {F : Type} [Field F] [CharP F 2] {M : Type*} [AddCommGroup M] [Module F M]

theorem semi_add_self (F : Type) [Field F] [CharP F 2] {M : Type*} [AddCommGroup M] [Module F M]
    (x : M) : x + x = 0 := by
  rw [← two_smul F x, CharTwo.two_eq_zero, zero_smul]

theorem semi_decomp (σ : M → M) (θ : F →+* F) (hadd : ∀ x y, σ (x + y) = σ x + σ y)
    (hsm : ∀ (r : F) x, σ (r • x) = θ r • σ x) (hσσ : ∀ x, σ (σ x) = x) {t : F}
    (ht : t + θ t = 1) (x : M) :
    ∃ a b : M, σ a = a ∧ σ b = b ∧ x = a + t • a + b := by
  refine ⟨x + σ x, t • x + σ (t • x), ?_, ?_, ?_⟩
  · rw [hadd, hσσ, add_comm]
  · rw [hadd, hσσ, add_comm]
  · have e : σ (t • x) = θ t • σ x := hsm t x
    rw [e]
    have h1 : t • (x + σ x) + (t • x + θ t • σ x) = σ x := by
      calc t • (x + σ x) + (t • x + θ t • σ x)
          = (t • x + t • x) + (t + θ t) • σ x := by
            rw [smul_add, add_smul]
            abel
        _ = σ x := by rw [semi_add_self F, ht, one_smul, zero_add]
    calc x = (x + σ x) + σ x := by rw [add_assoc, semi_add_self F, add_zero]
      _ = (x + σ x) + (t • (x + σ x) + (t • x + θ t • σ x)) := by rw [h1]
      _ = x + σ x + t • (x + σ x) + (t • x + θ t • σ x) := by abel

end SemiDecomp

end CFSG.LocalAnalysis.RankThreeUC
