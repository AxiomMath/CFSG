module


public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section PairClosure

variable {Γ : Type*} [Group Γ]

theorem twPlane_pair_mul {a b : Γ} (hab : Commute a b) (i j k l : ℕ) :
    (a ^ i * b ^ j) * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
  rw [(hab.symm.pow_pow j k).mul_mul_mul_comm, ← pow_add, ← pow_add]

theorem twPlane_closure_pair_eq_range {a b : Γ} (hab : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) :
    (Subgroup.closure ({a, b} : Set Γ) : Set Γ) =
      Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)) := by
  have hmul : ∀ x y : Γ, (∃ i j : ℕ, x = a ^ i * b ^ j) → (∃ i j : ℕ, y = a ^ i * b ^ j) →
      ∃ i j : ℕ, x * y = a ^ i * b ^ j := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact ⟨i + k, j + l, twPlane_pair_mul hab i j k l⟩
  let T : Subgroup Γ :=
    { carrier := {x | ∃ i j : ℕ, x = a ^ i * b ^ j}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := fun {x y} hx hy => hmul x y hx hy
      inv_mem' := fun {x} hx => by
        obtain ⟨i, j, rfl⟩ := hx
        have h3 : (a ^ i * b ^ j) * ((a ^ i * b ^ j) * (a ^ i * b ^ j)) = 1 := by
          have e : (a ^ i * b ^ j) * ((a ^ i * b ^ j) * (a ^ i * b ^ j)) = (a ^ i * b ^ j) ^ 3 :=
            (pow_three _).symm
          rw [e, ((hab.pow_pow i j).mul_pow 3), ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3,
            pow_mul, pow_mul, ha, hb]
          simp
        have hinv : (a ^ i * b ^ j)⁻¹ = (a ^ i * b ^ j) * (a ^ i * b ^ j) :=
          inv_eq_of_mul_eq_one_right h3
        rw [hinv]
        exact hmul _ _ ⟨i, j, rfl⟩ ⟨i, j, rfl⟩ }
  have hle : Subgroup.closure ({a, b} : Set Γ) ≤ T := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rcases hx with rfl
      exact ⟨0, 1, by simp⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, j, rfl⟩ := hle hx
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    have e1 : a ^ i = a ^ (i % 3) := by
      conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, ha, one_pow, one_mul]
    have e2 : b ^ j = b ^ (j % 3) := by
      conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hb, one_pow, one_mul]
    show a ^ (i % 3) * b ^ (j % 3) = a ^ i * b ^ j
    rw [← e1, ← e2]
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem twPlane_pow_three_of_mem_closure_pair {a b : Γ} (hab : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) {x : Γ} (hx : x ∈ Subgroup.closure ({a, b} : Set Γ)) : x ^ 3 = 1 := by
  have hx' : x ∈ Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)) := by
    rw [← twPlane_closure_pair_eq_range hab ha hb]
    exact hx
  obtain ⟨⟨i, j⟩, rfl⟩ := hx'
  show (a ^ (i : ℕ) * b ^ (j : ℕ)) ^ 3 = 1
  rw [(hab.pow_pow _ _).mul_pow, ← pow_mul, ← pow_mul, mul_comm (i : ℕ) 3, mul_comm (j : ℕ) 3,
    pow_mul, pow_mul, ha, hb]
  simp

theorem twPlane_card_closure_pair {a b : Γ} (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    Nat.card (Subgroup.closure ({a, b} : Set Γ)) = 9 := by
  have hinj : Function.Injective
      (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hf
    have hf' : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) := hf
    have key : a ^ ((i : ℕ) + 2 * (k : ℕ)) * b ^ ((j : ℕ) + 2 * (l : ℕ)) = 1 := by
      have h1 := twPlane_pair_mul hab (i : ℕ) (j : ℕ) (2 * (k : ℕ)) (2 * (l : ℕ))
      have h2 := twPlane_pair_mul hab (k : ℕ) (l : ℕ) (2 * (k : ℕ)) (2 * (l : ℕ))
      rw [← h1, hf', h2]
      rw [show (k : ℕ) + 2 * (k : ℕ) = 3 * (k : ℕ) by ring,
        show (l : ℕ) + 2 * (l : ℕ) = 3 * (l : ℕ) by ring, pow_mul, pow_mul, ha, hb]
      simp
    obtain ⟨h3i, h3j⟩ := hind _ _ key
    have hi : (i : ℕ) = k := by
      have := i.2
      have := k.2
      omega
    have hj : (j : ℕ) = l := by
      have := j.2
      have := l.2
      omega
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  have h9 : Nat.card (Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ))) = 9 := by
    rw [Nat.card_range_of_injective hinj]
    simp
  calc Nat.card (Subgroup.closure ({a, b} : Set Γ))
      = Set.ncard (Subgroup.closure ({a, b} : Set Γ) : Set Γ) := Nat.card_coe_set_eq _
    _ = Set.ncard (Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ))) := by
        rw [twPlane_closure_pair_eq_range hab ha hb]
    _ = Nat.card (Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ))) :=
        (Nat.card_coe_set_eq _).symm
    _ = 9 := h9

end PairClosure

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
