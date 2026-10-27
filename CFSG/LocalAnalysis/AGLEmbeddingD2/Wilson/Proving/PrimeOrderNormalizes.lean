module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem commute_of_orderOf_prime_normalizes {Γ : Type*} [Group Γ] (P : Subgroup Γ) [Finite P]
    (w : Γ) (q : ℕ) [Fact q.Prime] (hw : orderOf w = q) (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P)
    (hcop : ∀ B : Subgroup Γ, B ≤ P → B ≠ P → ¬ (q : ℤ) ∣ (Nat.card P : ℤ) - (Nat.card B : ℤ)) :
    ∀ x ∈ P, w * x = x * w := by
  classical
  have : Fintype P := Fintype.ofFinite P
  let f : Function.End P := fun x => ⟨w * x * w⁻¹, hwP x x.2⟩
  have hfk : ∀ k : ℕ, ∀ x : P, ((f^[k]) x : Γ) = w ^ k * x * (w ^ k)⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro x
      rw [pow_zero, one_mul, inv_one, mul_one]
      rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply']
      show w * ((f^[k]) x : Γ) * w⁻¹ = _
      rw [ih x]
      group
  have hwq : w ^ q = 1 := hw ▸ pow_orderOf_eq_one w
  have hfq : ∀ x : P, (f^[q]) x = x := by
    intro x
    apply Subtype.ext
    rw [hfk, hwq]
    simp
  have hf : f ^ (q ^ 1) = 1 := by
    rw [pow_one]
    funext x
    exact hfq x
  have hcong := Equiv.Perm.card_fixedPoints_modEq (p := q) (n := 1) hf
  obtain ⟨B, hB⟩ : ∃ B : Subgroup Γ, B = P ⊓ Subgroup.centralizer ({w} : Set Γ) := ⟨_, rfl⟩
  have hBP : B ≤ P := by rw [hB]; exact inf_le_left
  have hmemC : ∀ g ∈ B, w * g = g * w := by
    intro g hg
    rw [hB] at hg
    have hgC : g ∈ Subgroup.centralizer ({w} : Set Γ) := hg.2
    rw [Subgroup.mem_centralizer_iff] at hgC
    exact hgC w (Set.mem_singleton w)
  have hfix : ∀ g : Γ, ∀ hgP : g ∈ P, g ∈ B → (⟨g, hgP⟩ : P) ∈ f.fixedPoints := by
    intro g hgP hgB
    rw [Function.mem_fixedPoints_iff]
    apply Subtype.ext
    show w * g * w⁻¹ = g
    rw [hmemC g hgB]
    simp
  have hcardB : Nat.card B = Nat.card f.fixedPoints := by
    apply Nat.card_congr
    exact
      { toFun := fun g => ⟨⟨g.1, hBP g.2⟩, hfix g.1 (hBP g.2) g.2⟩
        invFun := fun x => ⟨x.1.1, by
          have h : w * x.1.1 * w⁻¹ = x.1.1 :=
            congrArg Subtype.val (Function.mem_fixedPoints_iff.mp x.2)
          have hc : w * x.1.1 = x.1.1 * w := mul_inv_eq_iff_eq_mul.mp h
          rw [hB]
          refine ⟨x.1.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
          intro k hk
          rw [Set.mem_singleton_iff.mp hk]
          exact hc⟩
        left_inv := fun g => Subtype.ext rfl
        right_inv := fun x => Subtype.ext (Subtype.ext rfl) }
  have hBeq : B = P := by
    by_contra hne
    apply hcop B hBP hne
    simp only [← Nat.card_eq_fintype_card] at hcong
    rw [← hcardB] at hcong
    exact dvd_sub_comm.mp (Nat.modEq_iff_dvd.mp hcong)
  intro x hx
  have hxB : x ∈ B := by rw [hBeq]; exact hx
  rw [hB] at hxB
  have hxC : x ∈ Subgroup.centralizer ({w} : Set Γ) := hxB.2
  rw [Subgroup.mem_centralizer_iff] at hxC
  exact hxC w (Set.mem_singleton w)

end CFSG.AGLEmbeddingD2.Wilson.Proving
