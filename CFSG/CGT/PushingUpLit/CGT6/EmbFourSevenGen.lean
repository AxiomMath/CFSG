module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

variable {Γ A : Type*} [Group Γ] [Group A]

theorem exists_pow_five_lift (θ : Γ →* A) (hker : IsPGroup 2 θ.ker) {a : A} (ha : a ^ 5 = 1)
    {g : Γ} (hg : θ g = a) : ∃ c : ℕ, (g ^ 2 ^ c) ^ 5 = 1 ∧ θ (g ^ 2 ^ c) = a ^ 2 ^ c := by
  have h5 : g ^ 5 ∈ θ.ker := by rw [MonoidHom.mem_ker, map_pow, hg, ha]
  obtain ⟨c, hc⟩ := hker ⟨g ^ 5, h5⟩
  refine ⟨c, ?_, by rw [map_pow, hg]⟩
  have := congrArg Subtype.val hc
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [← pow_mul, mul_comm, pow_mul]
  exact this

theorem closure_pow_five_eq_top [Group.IsPerfect Γ] [IsSimpleGroup A] (θ : Γ →* A)
    (hθs : Function.Surjective θ) (hcent : θ.ker ≤ Subgroup.center Γ) (hker : IsPGroup 2 θ.ker)
    (S₀ : Set A) (hne : S₀.Nonempty) (h1 : ∀ a ∈ S₀, a ≠ 1 ∧ a ^ 5 = 1)
    (hconj : ∀ a ∈ S₀, ∀ b : A, b * a * b⁻¹ ∈ S₀) (hpow : ∀ a ∈ S₀, a ^ 2 ∈ S₀) :
    Subgroup.closure {x : Γ | x ^ 5 = 1 ∧ θ x ∈ S₀} = ⊤ := by
  set S : Set Γ := {x | x ^ 5 = 1 ∧ θ x ∈ S₀} with hS
  set T := Subgroup.closure S with hT
  have hSconj : ∀ s ∈ S, ∀ g : Γ, g * s * g⁻¹ ∈ S := by
    intro s hs g
    refine ⟨by rw [conj_pow, hs.1]; group, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact hconj _ hs.2 _
  have hTn : T.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hSconj x hx g)
    | one => simp
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]; exact mul_mem hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hx
  have hpowc : ∀ a ∈ S₀, ∀ c : ℕ, a ^ 2 ^ c ∈ S₀ := by
    intro a ha c
    induction c with
    | zero => simpa using ha
    | succ c ih => rw [pow_succ, pow_mul]; exact hpow _ ih
  obtain ⟨a, ha⟩ := hne
  obtain ⟨g, hg⟩ := hθs a
  obtain ⟨c, hc5, hcθ⟩ := exists_pow_five_lift θ hker (h1 a ha).2 hg
  have hxS : g ^ 2 ^ c ∈ S := ⟨hc5, by rw [hcθ]; exact hpowc a ha c⟩
  have hmapn : (T.map θ).Normal := hTn.map θ hθs
  have hmap_top : T.map θ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.map θ) with h | h
    · exfalso
      have hmem : θ (g ^ 2 ^ c) ∈ T.map θ := ⟨_, Subgroup.subset_closure hxS, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact (h1 _ (hpowc a ha c)).1 (by rw [← hcθ]; exact hmem)
    · exact h
  have hsup : ∀ g : Γ, ∃ t ∈ T, ∃ k ∈ θ.ker, t * k = g := by
    intro g
    have : θ g ∈ T.map θ := by rw [hmap_top]; exact Subgroup.mem_top _
    obtain ⟨t, ht, htg⟩ := this
    refine ⟨t, ht, t⁻¹ * g, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, htg, inv_mul_cancel]
  have hcomm : (⊤ : Subgroup Γ) ≤ T := by
    have hperf : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [← hperf, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨t₁, ht₁, k₁, hk₁, rfl⟩ := hsup g₁
    obtain ⟨t₂, ht₂, k₂, hk₂, rfl⟩ := hsup g₂
    have hc₁ := Subgroup.mem_center_iff.mp (hcent hk₁)
    have hc₂ := Subgroup.mem_center_iff.mp (hcent hk₂)
    have : ⁅t₁ * k₁, t₂ * k₂⁆ = ⁅t₁, t₂⁆ := by
      simp only [commutatorElement_def]
      calc t₁ * k₁ * (t₂ * k₂) * (t₁ * k₁)⁻¹ * (t₂ * k₂)⁻¹
          = t₁ * (k₁ * t₂) * k₂ * k₁⁻¹ * t₁⁻¹ * k₂⁻¹ * t₂⁻¹ := by group
        _ = t₁ * (t₂ * k₁) * k₂ * k₁⁻¹ * t₁⁻¹ * k₂⁻¹ * t₂⁻¹ := by rw [hc₁ t₂]
        _ = t₁ * t₂ * (k₁ * k₂ * k₁⁻¹) * t₁⁻¹ * k₂⁻¹ * t₂⁻¹ := by group
        _ = t₁ * t₂ * k₂ * t₁⁻¹ * k₂⁻¹ * t₂⁻¹ := by
          have h3 : k₁ * k₂ * k₁⁻¹ = k₂ := by rw [hc₂ k₁]; group
          rw [h3]
        _ = t₁ * t₂ * (k₂ * t₁⁻¹) * k₂⁻¹ * t₂⁻¹ := by group
        _ = t₁ * t₂ * (t₁⁻¹ * k₂) * k₂⁻¹ * t₂⁻¹ := by rw [hc₂ t₁⁻¹]
        _ = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by group
    rw [this, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ht₁ ht₂) (inv_mem ht₁)) (inv_mem ht₂)
  exact top_le_iff.mp hcomm

end CFSG.CGT.PushingUpLit.CGT6
