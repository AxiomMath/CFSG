module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cW2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cQ

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace Conf

variable (K : Conf S T₁)

theorem D₁₁_mem_E {δ : X} (hδ : δ ∈ K.D₁.D₁₁) : δ ∈ normalizer (S.E S.y : Set X) :=
  (K.D₁.D₁₁_le hδ).1.1

theorem conj_E0 {δ : X} (hδ : δ ∈ K.D₁.D₁₁) {e : X} (he : e ∈ S.E0 S.y S.k) :
    δ * e * δ⁻¹ ∈ S.E0 S.y S.k :=
  K.P.V.conj_mem_E0 (K.D₁₁_mem_E hδ) he

theorem conj_E0' {δ : X} (hδ : δ ∈ K.D₁.D₁₁) {e : X} (he : e ∈ S.E0 S.y S.k) :
    δ⁻¹ * e * δ ∈ S.E0 S.y S.k := by
  have := K.conj_E0 (inv_mem hδ) he
  rwa [inv_inv] at this

theorem conj_Q0X {δ : X} (hδ : δ ∈ K.D₁.D₁₁) {x : X} (hx : x ∈ K.Q0X) :
    δ * x * δ⁻¹ ∈ K.Q0X := by
  have h := K.D₁.Q0_invariant δ ⟨(K.D₁.D₁₁_le hδ).1.1, (K.D₁.D₁₁_le hδ).1.2⟩
  exact Sec7.conj_mem_of_map_eq h hx

theorem coset_cases {x : X} (hx : x ∈ K.Q0X) (hx0 : x ∉ S.E0 S.y S.k) :
    (K.ι MC.w₁)⁻¹ * x ∈ S.E0 S.y S.k ∨ (K.ι MC.w₂)⁻¹ * x ∈ S.E0 S.y S.k ∨
      (K.ι (MC.w₁ * MC.w₂))⁻¹ * x ∈ S.E0 S.y S.k := by
  obtain ⟨a, ha, rfl⟩ := K.exists_of_mem_Q0X hx
  rw [K.mem_E0_iff] at hx0
  rw [K.mem_coset_iff, K.mem_coset_iff, K.mem_coset_iff]
  rcases Q0h_cosets a ha with h | h | h | h
  · exact absurd h hx0
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem conj_coset {δ : X} (hδ : δ ∈ K.D₁.D₁₁) {c c' x : X}
    (hc : c'⁻¹ * (δ * c * δ⁻¹) ∈ S.E0 S.y S.k) (hx : c⁻¹ * x ∈ S.E0 S.y S.k) :
    c'⁻¹ * (δ * x * δ⁻¹) ∈ S.E0 S.y S.k := by
  have := mul_mem hc (K.conj_E0 hδ hx)
  rw [show c'⁻¹ * (δ * c * δ⁻¹) * (δ * (c⁻¹ * x) * δ⁻¹) = c'⁻¹ * (δ * x * δ⁻¹) by group]
    at this
  exact this

theorem W₂_mem_Q0X : K.ι MC.w₂ ∈ K.Q0X := K.ι_mem_Q0X (by decide +kernel)

theorem W₁₂_mem_Q0X : K.ι (MC.w₁ * MC.w₂) ∈ K.Q0X := K.ι_mem_Q0X (by decide +kernel)

theorem W₂_not_mem : K.ι MC.w₂ ∉ S.E0 S.y S.k := by
  rw [K.mem_E0_iff, cosets_ne.1]
  decide

theorem W₁₂_not_mem : K.ι (MC.w₁ * MC.w₂) ∉ S.E0 S.y S.k := by
  rw [K.mem_E0_iff, cosets_ne.2.2.2.2.2.2]
  decide

theorem not_mem_conj {δ : X} (hδ : δ ∈ K.D₁.D₁₁) {x : X} (hx : x ∉ S.E0 S.y S.k) :
    δ * x * δ⁻¹ ∉ S.E0 S.y S.k := fun h => hx (by
  have := K.conj_E0' hδ h
  rwa [show δ⁻¹ * (δ * x * δ⁻¹) * δ = x by group] at this)

theorem exists_move : ∃ δ ∈ K.D₁.D₁₁, (K.ι MC.w₂)⁻¹ * (δ * K.ι MC.w₂ * δ⁻¹) ∉ S.E0 S.y S.k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hno
  push Not at hno
  set W := K.ι MC.w₂ with hW
  let α := {x : X // W⁻¹ * x ∈ S.E0 S.y S.k}
  have hmem : ∀ (δ : K.D₁.D₁₁) (x : α), W⁻¹ * ((δ : X) * x.1 * (δ : X)⁻¹) ∈ S.E0 S.y S.k :=
    fun δ x => K.conj_coset δ.2 (hno δ δ.2) x.2
  let act : MulAction K.D₁.D₁₁ α :=
    { smul := fun δ x => ⟨(δ : X) * x.1 * (δ : X)⁻¹, hmem δ x⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : K.D₁.D₁₁) : X) * x.1 * ((1 : K.D₁.D₁₁) : X)⁻¹ = x.1
        simp)
      mul_smul := fun δ ε x => Subtype.ext (by
        show (δ : X) * ε * x.1 * ((δ : X) * ε)⁻¹ = δ * (ε * x.1 * (ε : X)⁻¹) * (δ : X)⁻¹
        group) }
  have hcard : Nat.card α = 8 := by
    have h8 : Nat.card (S.E0 S.y S.k) = 8 := K.P.V.F.card_E0
    rw [← h8]
    exact Nat.card_congr
      { toFun := fun x => ⟨W⁻¹ * x.1, x.2⟩
        invFun := fun e => ⟨W * e.1, by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun e => Subtype.ext (by simp) }
  obtain ⟨x, hx⟩ := K.D₁.isPGroup_D₁₁.nonempty_fixed_point_of_prime_not_dvd_card α
    (by rw [hcard]; decide)
  have hfix : ∀ δ ∈ K.D₁.D₁₁, δ * x.1 * δ⁻¹ = x.1 := fun δ hδ =>
    congrArg Subtype.val (hx ⟨δ, hδ⟩)
  have hxQ : x.1 ∈ K.Q0X := by
    have := mul_mem K.W₂_mem_Q0X (K.E0_le_Q0X x.2)
    rwa [mul_inv_cancel_left] at this
  have hxC : x.1 ∈ K.D₁.Q₁ ⊓ centralizer (K.D₁.D₁₁ : Set X) := by
    refine ⟨K.D₁.Q0_le hxQ, mem_centralizer_iff.mpr fun δ hδ => ?_⟩
    have := hfix δ hδ
    calc δ * x.1 = δ * x.1 * δ⁻¹ * δ := by group
      _ = x.1 * δ := by rw [this]
  obtain ⟨a, ha, hax⟩ := K.exists_of_mem_C hxC
  have h2 := x.2
  rw [← hax, hW, K.mem_coset_iff] at h2
  rw [(tkv_miss a ha).2.1] at h2
  exact absurd h2 (by decide)

theorem exists_to_W₁ : ∃ δ ∈ K.D₁.D₁₁,
    (K.ι MC.w₁)⁻¹ * (δ * K.ι MC.w₂ * δ⁻¹) ∈ S.E0 S.y S.k := by
  obtain ⟨δ, hδ, hmove⟩ := K.exists_move
  set W₂ := K.ι MC.w₂
  set W₁₂ := K.ι (MC.w₁ * MC.w₂)
  rcases K.coset_cases (K.conj_Q0X hδ K.W₂_mem_Q0X) (K.not_mem_conj hδ K.W₂_not_mem) with
    h | h | h
  · exact ⟨δ, hδ, h⟩
  · exact absurd h hmove
  rcases K.coset_cases (K.conj_Q0X hδ K.W₁₂_mem_Q0X) (K.not_mem_conj hδ K.W₁₂_not_mem) with
    h' | h' | h'
  ·
    refine ⟨δ * δ, mul_mem hδ hδ, ?_⟩
    have := K.conj_coset hδ h' h
    rwa [show δ * (δ * W₂ * δ⁻¹) * δ⁻¹ = δ * δ * W₂ * (δ * δ)⁻¹ by group] at this
  ·
    exfalso
    have hpow : ∀ m : ℕ, W₁₂⁻¹ * (δ ^ (2 * m + 1) * W₂ * (δ ^ (2 * m + 1))⁻¹) ∈
        S.E0 S.y S.k := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.mul_zero, zero_add, pow_one]
        exact h
      | succ m ih =>
        have h1 := K.conj_coset hδ h' ih
        have h2 := K.conj_coset hδ h h1
        rwa [show δ * (δ * (δ ^ (2 * m + 1) * W₂ * (δ ^ (2 * m + 1))⁻¹) * δ⁻¹) * δ⁻¹ =
          δ ^ (2 * (m + 1) + 1) * W₂ * (δ ^ (2 * (m + 1) + 1))⁻¹ by
            rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, pow_succ, pow_succ]
            group] at h2
    obtain ⟨n, hn⟩ := K.D₁.isPGroup_D₁₁ ⟨δ, hδ⟩
    have hn' : δ ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
    have := hpow m
    rw [← hm, hn', one_mul, inv_one, mul_one, K.mem_coset_iff, cosets_ne.2.2.1] at this
    exact absurd this (by decide)
  ·
    exfalso
    have := mul_mem (inv_mem h) h'
    rw [show (W₁₂⁻¹ * (δ * W₂ * δ⁻¹))⁻¹ * (W₁₂⁻¹ * (δ * W₁₂ * δ⁻¹)) =
      δ * (W₂⁻¹ * W₁₂) * δ⁻¹ by group] at this
    have h3 := K.conj_E0' hδ this
    rw [show δ⁻¹ * (δ * (W₂⁻¹ * W₁₂) * δ⁻¹) * δ = W₂⁻¹ * W₁₂ by group, K.mem_coset_iff,
      cosets_ne.2.2.2.2.2.1] at h3
    exact absurd h3 (by decide)

theorem not_conjTo_w₂ : ¬ ConjTo t (K.ι MC.w₂) := by
  obtain ⟨δ, hδ, hcos⟩ := K.exists_to_W₁
  intro hc
  obtain ⟨a, -, hax⟩ := K.exists_of_mem_Q0X (K.conj_Q0X hδ K.W₂_mem_Q0X)
  rw [← hax, K.mem_coset_iff] at hcos
  have ha2 : a * a = 1 := by
    apply K.ι_injective
    rw [map_mul, hax, map_one, show δ * K.ι MC.w₂ * δ⁻¹ * (δ * K.ι MC.w₂ * δ⁻¹) =
      δ * K.ι (MC.w₂ * MC.w₂) * δ⁻¹ by rw [map_mul]; group,
      show MC.w₂ * MC.w₂ = 1 by decide +kernel, map_one]
    group
  apply K.not_hasT_7
  refine ⟨K.ι a, K.ι_mem_Ex (w1E0_F2 a hcos ha2), ?_⟩
  rw [hax]
  exact (conjTo_conj_iff δ _).mpr hc

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit
