module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.PermThree
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec14

section Klein

variable {X : Type*} [Group X]

abbrev Pt (V : Subgroup X) : Type _ := {v : X // v ∈ V ∧ v ≠ 1}

theorem card_Pt [Finite X] {V : Subgroup X} (h : Nat.card V = 4) : Nat.card (Pt V) = 3 := by
  classical
  have e1 : Pt V ≃ {v : ↥V // v ≠ 1} :=
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, fun h => v.2.2 (congrArg Subtype.val h)⟩
      invFun := fun v => ⟨v.1.1, v.1.2, fun h => v.2 (Subtype.ext h)⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  have e2 := Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥V))
  rw [Nat.card_congr e1]
  have : Nat.card (Option {b : ↥V // b ≠ 1}) = Nat.card {b : ↥V // b ≠ 1} + 1 := by
    simp
  omega

@[expose] def actPt (V : Subgroup X) (g : ↥(Subgroup.normalizer (V : Set X))) : Equiv.Perm (Pt V) where
  toFun v := ⟨(g : X) * v.1 * (g : X)⁻¹, (Subgroup.mem_normalizer_iff.1 g.2 v.1).1 v.2.1, by
    intro h
    apply v.2.2
    have := congrArg (fun y => (g : X)⁻¹ * y * (g : X)) h
    simpa [mul_assoc] using this⟩
  invFun v := ⟨(g : X)⁻¹ * v.1 * (g : X), by
    have h1 := (Subgroup.mem_normalizer_iff.1 g.2 ((g : X)⁻¹ * v.1 * (g : X))).2
    have : (g : X) * ((g : X)⁻¹ * v.1 * (g : X)) * (g : X)⁻¹ = v.1 := by group
    rw [this] at h1
    exact h1 v.2.1, by
    intro h
    apply v.2.2
    have := congrArg (fun y => (g : X) * y * (g : X)⁻¹) h
    simpa [mul_assoc] using this⟩
  left_inv v := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv v := by
    apply Subtype.ext
    simp [mul_assoc]

@[expose] def actPtHom (V : Subgroup X) : ↥(Subgroup.normalizer (V : Set X)) →* Equiv.Perm (Pt V) where
  toFun := actPt V
  map_one' := by
    ext v
    simp [actPt]
  map_mul' g h := by
    ext v
    simp [actPt, mul_assoc]

end Klein

section Finite

theorem perm3_conj_inv : ∀ σ γ : Equiv.Perm (Fin 3), σ ≠ 1 → σ * σ = 1 → γ ^ 3 = 1 →
    σ * γ * σ⁻¹ = γ⁻¹ := by decide

theorem perm3_cycle : ∀ p q : Fin 3, ∃ c : Equiv.Perm (Fin 3), c ^ 3 = 1 ∧ c p = q := by decide

theorem perm3_fpf : ∀ γ : Equiv.Perm (Fin 3), γ ^ 3 = 1 → γ ≠ 1 → ∀ i, γ i ≠ i := by decide

theorem perm3_three_cycle : ∀ p : Fin 3, ∀ a b : Equiv.Perm (Fin 3), a p ≠ p → b p ≠ p → a p ≠ b p →
    (a ^ 3 = 1 ∧ a ≠ 1) ∨ (b ^ 3 = 1 ∧ b ≠ 1) ∨ ((a * b) ^ 3 = 1 ∧ a * b ≠ 1) := by decide

abbrev Sig9 : Finset B3 := Finset.univ.filter (fun b : B3 => b ^ 3 = 1)

@[expose] def GenP (γ δ ε : B3) : Prop :=
  γ ≠ 1 → δ ≠ 1 → δ ≠ γ → δ ≠ γ ^ 2 → ∃ i j : Fin 3, ε = γ ^ i.val * δ ^ j.val

instance (γ δ ε : B3) : Decidable (GenP γ δ ε) := by unfold GenP; infer_instance

theorem b3_gen : ∀ γ ∈ Sig9, ∀ δ ∈ Sig9, ∀ ε ∈ Sig9, GenP γ δ ε := by decide +kernel

theorem mem_Sig9 {b : B3} : b ∈ Sig9 ↔ b ^ 3 = 1 := by simp [Sig9]

theorem perm3_two_other : ∀ p : Fin 3, ∃ j₁ j₂ : Fin 3, j₁ ≠ p ∧ j₂ ≠ p ∧ j₁ ≠ j₂ := by decide

theorem exists_three_elt (Γ : Subgroup B3) (f : B3 →* Equiv.Perm (Fin 3)) (p : Fin 3)
    (htr : ∀ j : Fin 3, ∃ γ ∈ Γ, f γ p = j) : ∃ γ ∈ Γ, γ ^ 3 = 1 ∧ f γ ≠ 1 := by
  obtain ⟨j₁, j₂, h1, h2, h12⟩ := perm3_two_other p
  obtain ⟨γ₁, hγ₁, e₁⟩ := htr j₁
  obtain ⟨γ₂, hγ₂, e₂⟩ := htr j₂
  have key : ∃ δ ∈ Γ, (f δ) ^ 3 = 1 ∧ f δ ≠ 1 := by
    rcases perm3_three_cycle p (f γ₁) (f γ₂) (by rw [e₁]; exact h1) (by rw [e₂]; exact h2)
        (by rw [e₁, e₂]; exact h12) with h | h | h
    · exact ⟨γ₁, hγ₁, h⟩
    · exact ⟨γ₂, hγ₂, h⟩
    · exact ⟨γ₁ * γ₂, Γ.mul_mem hγ₁ hγ₂, by simpa using h⟩
  obtain ⟨δ, hδ, h3, hne⟩ := key
  refine ⟨δ ^ 4, Γ.pow_mem hδ 4, ?_, ?_⟩
  · rw [← pow_mul]
    have : δ ^ 12 = (δ ^ 6) ^ 2 := by rw [← pow_mul]
    rw [show 4 * 3 = 12 by norm_num, this, B3_exp, one_pow]
  · rw [map_pow]
    have : (f δ) ^ 4 = f δ := by
      rw [show 4 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [this]; exact hne

theorem fl_main (Γ : Subgroup B3) (σ : B3) (hσ1 : σ.1 ≠ 1) (hσ2 : σ.2 ≠ 1)
    (hσ1' : σ.1 * σ.1 = 1) (hσ2' : σ.2 * σ.2 = 1)
    (p q : Fin 3) (htr1 : ∀ j : Fin 3, ∃ γ ∈ Γ, γ.1 p = j) (htr2 : ∀ j : Fin 3, ∃ γ ∈ Γ, γ.2 q = j) :
    (∀ γ : B3, γ ^ 3 = 1 → σ * γ * σ⁻¹ = γ⁻¹) ∧
      ∃ γ ∈ Γ, γ ^ 3 = 1 ∧ γ.1 ≠ 1 ∧ γ.2 ≠ 1 := by
  refine ⟨?_, ?_⟩
  · intro γ hγ3
    apply Prod.ext
    · have h1 : γ.1 ^ 3 = 1 := by simpa using congrArg Prod.fst hγ3
      simpa using perm3_conj_inv σ.1 γ.1 hσ1 hσ1' h1
    · have h1 : γ.2 ^ 3 = 1 := by simpa using congrArg Prod.snd hγ3
      simpa using perm3_conj_inv σ.2 γ.2 hσ2 hσ2' h1
  · obtain ⟨γ₁, hγ₁, h₁3, h₁⟩ := exists_three_elt Γ (MonoidHom.fst _ _) p htr1
    obtain ⟨γ₂, hγ₂, h₂3, h₂⟩ := exists_three_elt Γ (MonoidHom.snd _ _) q htr2
    by_cases hc : γ₁.2 = 1
    · by_cases hd : γ₂.1 = 1
      · refine ⟨γ₁ * γ₂, Γ.mul_mem hγ₁ hγ₂, ?_, ?_, ?_⟩
        · apply Prod.ext
          · have a1 : γ₁.1 ^ 3 = 1 := by simpa using congrArg Prod.fst h₁3
            simp [hd, a1]
          · have a2 : γ₂.2 ^ 3 = 1 := by simpa using congrArg Prod.snd h₂3
            simp [hc, a2]
        · simpa [hd] using h₁
        · simpa [hc] using h₂
      · exact ⟨γ₂, hγ₂, h₂3, hd, h₂⟩
    · exact ⟨γ₁, hγ₁, h₁3, h₁, hc⟩

theorem fl_dichotomy (Γ₀ : Subgroup B3) (hΓ₀ : ∀ γ ∈ Γ₀, γ ^ 3 = 1) (γ : B3) (hγ : γ ∈ Γ₀)
    (hγ1 : γ.1 ≠ 1) :
    (∀ δ ∈ Γ₀, δ = 1 ∨ δ = γ ∨ δ = γ ^ 2) ∨ (∀ ε : B3, ε ^ 3 = 1 → ε ∈ Γ₀) := by
  by_cases h : ∀ δ ∈ Γ₀, δ = 1 ∨ δ = γ ∨ δ = γ ^ 2
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨δ, hδ, hδ1, hδγ, hδγ2⟩ := h
    intro ε hε
    have hγ3 : γ ∈ Sig9 := mem_Sig9.2 (hΓ₀ γ hγ)
    have hδ3 : δ ∈ Sig9 := mem_Sig9.2 (hΓ₀ δ hδ)
    have hε3 : ε ∈ Sig9 := mem_Sig9.2 hε
    have hγne : γ ≠ 1 := fun e => hγ1 (by simp [e])
    obtain ⟨i, j, hij⟩ := b3_gen γ hγ3 δ hδ3 ε hε3 hγne hδ1 hδγ hδγ2
    rw [hij]
    exact Γ₀.mul_mem (Γ₀.pow_mem hγ _) (Γ₀.pow_mem hδ _)

end Finite

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn
