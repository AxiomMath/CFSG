module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutAlt

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem exists_invariant_line {X : Type*} [Group X] [Finite X] (hX9 : Nat.card X = 9)
    (hcomm : ∀ x y : X, x * y = y * x) (𝒜 : Set (MulAut X))
    (hmul : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, α * β ∈ 𝒜) (hsq : ∀ α ∈ 𝒜, α * α = 1) :
    ∃ W : Subgroup X, Nat.card W = 3 ∧ ∀ α ∈ 𝒜, ∀ w ∈ W, α w ∈ W := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hαβ : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, α * β = β * α := by
    intro α hα β hβ
    have h1 := hsq α hα
    have h2 := hsq β hβ
    have h3 := hsq _ (hmul α hα β hβ)
    have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right h1
    have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right h2
    have hi : (α * β)⁻¹ = α * β := inv_eq_of_mul_eq_one_right h3
    calc α * β = (α * β)⁻¹ := hi.symm
      _ = β * α := by rw [mul_inv_rev, hαi, hβi]
  by_cases h1 : ∀ α ∈ 𝒜, (∀ x, α x = x) ∨ (∀ x, α x = x⁻¹)
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX9]; norm_num)
    refine ⟨Subgroup.zpowers g, by rw [Nat.card_zpowers, hg], fun α hα w hw => ?_⟩
    rcases h1 α hα with h | h
    · rw [h]; exact hw
    · rw [h]; exact Subgroup.inv_mem _ hw
  · push Not at h1
    obtain ⟨α₀, hα₀, hne1, hne2⟩ := h1
    obtain ⟨x₁, hx₁⟩ := hne1
    obtain ⟨x₂, hx₂⟩ := hne2
    let Wp : Subgroup X :=
      { carrier := {x | α₀ x = x}
        mul_mem' := fun {a b} (ha : α₀ a = a) (hb : α₀ b = b) => by
          show α₀ (a * b) = a * b
          rw [map_mul, ha, hb]
        one_mem' := by simp
        inv_mem' := fun {a} (ha : α₀ a = a) => by
          show α₀ a⁻¹ = a⁻¹
          rw [map_inv, ha] }
    have hmemWp : ∀ x, x ∈ Wp ↔ α₀ x = x := fun x => Iff.rfl
    have hWtop : Wp ≠ ⊤ := fun h => hx₁ ((hmemWp x₁).1 (h ▸ Subgroup.mem_top x₁))
    have hWbot : Wp ≠ ⊥ := by
      intro hb
      apply hx₂
      have hsq0 : ∀ x, α₀ (α₀ x) = x := fun x => by
        have := congrArg (fun γ : MulAut X => γ x) (hsq α₀ hα₀)
        simpa using this
      have : x₂ * α₀ x₂ ∈ Wp := by
        rw [hmemWp, map_mul, hsq0, hcomm]
      rw [hb, Subgroup.mem_bot] at this
      exact eq_inv_of_mul_eq_one_right this
    have hcard : Nat.card Wp = 3 := by
      have hdvd : Nat.card Wp ∣ 3 ^ 2 := by
        have := Subgroup.card_subgroup_dvd_card Wp
        rwa [hX9] at this
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      interval_cases k
      · exact absurd (Subgroup.card_eq_one.1 (by simpa using hk')) hWbot
      · simpa using hk'
      · exact absurd ((Subgroup.card_eq_iff_eq_top Wp).1 (by rw [hk', hX9]; norm_num)) hWtop
    refine ⟨Wp, hcard, fun β hβ w hw => ?_⟩
    rw [hmemWp] at hw ⊢
    have := congrArg (fun γ : MulAut X => γ w) (hαβ α₀ hα₀ β hβ)
    simp only [MulAut.mul_apply] at this
    rw [this, hw]

variable {Q : Type*} [Group Q]

theorem exists_line_of_sq_trivial [Finite Q] {E N : Subgroup Q} (hE9 : Nat.card E = 9)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hNE : N ≤ Subgroup.normalizer (E : Set Q))
    (hsq : ∀ n ∈ N, ∀ x ∈ E, n * n * x * (n * n)⁻¹ = x) :
    ∃ W : Subgroup Q, W ≤ E ∧ Nat.card W = 3 ∧ N ≤ Subgroup.normalizer (W : Set Q) := by
  let 𝒜 : Set (MulAut E) := {α | ∃ (n : Q) (hn : n ∈ N), α = conjOnNormalizer E n (hNE hn)}
  have hmulc : ∀ (n m : Q) (hn : n ∈ N) (hm : m ∈ N),
      conjOnNormalizer E n (hNE hn) * conjOnNormalizer E m (hNE hm) =
        conjOnNormalizer E (n * m) (hNE (N.mul_mem hn hm)) := by
    intro n m hn hm
    ext x
    simp [conjOnNormalizer_apply, mul_assoc]
  obtain ⟨W', hW'c, hW'⟩ := exists_invariant_line (X := E) hE9
    (fun x y => Subtype.ext (hcomm x x.2 y y.2)) 𝒜
    (by
      rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
      exact ⟨n * m, N.mul_mem hn hm, hmulc n m hn hm⟩)
    (by
      rintro _ ⟨n, hn, rfl⟩
      rw [hmulc n n hn hn]
      ext x
      simpa [conjOnNormalizer_apply] using hsq n hn x x.2)
  refine ⟨W'.map E.subtype, Subgroup.map_subtype_le W', ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hW'c]
  · intro n hn
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨conjOnNormalizer E n (hNE hn) w, hW' _ ⟨n, hn, rfl⟩ w hw, ?_⟩
    simp [conjOnNormalizer_apply]

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
