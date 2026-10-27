module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped commutatorElement

section Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem perm_eq_one_of_commute_alternating (h5 : Fintype.card Ω = 5) {σ : Equiv.Perm Ω}
    (h : ∀ τ ∈ alternatingGroup Ω, σ * τ = τ * σ) : σ = 1 := by
  ext a
  by_contra hne
  have hne' : a ≠ σ a := fun h' => hne (by simpa using h'.symm)
  obtain ⟨y, hya, hyσ⟩ : ∃ y : Ω, y ≠ a ∧ y ≠ σ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset Ω) ⊆ {a, σ a} := by
      intro y _
      by_cases hya : y = a
      · simp [hya]
      · simp [hcon y hya]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, h5] at h1
    have h2 := Finset.card_le_two (a := a) (b := σ a)
    omega
  obtain ⟨τ, hτ, h1, h2⟩ := alt_two_transitive h5 hne' hya.symm
  have h3 := congrArg (fun π : Equiv.Perm Ω => π a) (h τ hτ)
  simp only [Equiv.Perm.mul_apply, h1, h2] at h3
  exact hyσ h3.symm

omit [Fintype Ω] in
theorem mem_closure_swap {x y : Ω} (g : Equiv.Perm Ω) :
    g ∈ Subgroup.closure {Equiv.swap x y} ↔ g = 1 ∨ g = Equiv.swap x y := by
  rw [← Subgroup.zpowers_eq_closure, Subgroup.mem_zpowers_iff]
  have hsq : Equiv.swap x y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact Equiv.swap_mul_self x y
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, hsq, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

omit [Fintype Ω] in
theorem swap_ne_one {x y : Ω} (hxy : x ≠ y) : Equiv.swap x y ≠ 1 := by
  intro h
  have := congrArg (fun π : Equiv.Perm Ω => π x) h
  simp only [Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at this
  exact hxy this.symm

omit [Fintype Ω] in
theorem natCard_closure_swap {x y : Ω} (hxy : x ≠ y) :
    Nat.card (Subgroup.closure {Equiv.swap x y}) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact Equiv.swap_mul_self x y) (swap_ne_one hxy)

theorem commutatorElement_mem_alternatingGroup (σ τ : Equiv.Perm Ω) :
    ⁅σ, τ⁆ ∈ alternatingGroup Ω := by
  rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)

theorem alternatingGroup_ne_top (h : 1 < Fintype.card Ω) : alternatingGroup Ω ≠ ⊤ := by
  classical
  intro htop
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h
  have h1 : Equiv.swap a b ∈ alternatingGroup Ω := by rw [htop]; trivial
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hab] at h1
  exact absurd h1 (by decide)

end Perm

end CFSG.QuasithinUnique.Setup.Lift
