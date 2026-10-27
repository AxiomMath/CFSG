module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Algebra.CharP.Frobenius

public section

namespace CFSG.LieType.SeitzGeneration

instance ug87_neZero (r : ℕ) [Fact r.Prime] : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩

section Arith

variable {K : Type*} [Field K] {r : ℕ} [Fact r.Prime]

local notation "χ" => quadraticChar (ZMod r)

theorem ug87_two_ne_zero (hr8 : r % 8 = 1) : (2 : ZMod r) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 r).mp h2)
  have := (Fact.out : r.Prime).two_le
  omega

theorem ug87_chi_two (hr8 : r % 8 = 1) : χ (2 : ZMod r) = 1 := by
  have hr2 : r ≠ 2 := by omega
  exact (quadraticChar_one_iff_isSquare (ug87_two_ne_zero hr8)).mpr
    ((ZMod.exists_sq_eq_two_iff hr2).mpr (Or.inl hr8))

theorem ug87_chi_neg_one (hr8 : r % 8 = 1) : χ (-1 : ZMod r) = 1 := by
  exact (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega))

theorem ug87_chi_neg (hr8 : r % 8 = 1) (x : ZMod r) : χ (-x) = χ x := by
  rw [← neg_one_mul, map_mul, ug87_chi_neg_one hr8, one_mul]

theorem ug87_chi_cases (x : ZMod r) : χ x = 0 ∨ χ x = 1 ∨ χ x = -1 := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx]; exact quadraticChar_zero)
  · exact Or.inr (quadraticChar_dichotomy hx)

theorem ug87_chi_eq_zero_iff (x : ZMod r) : χ x = 0 ↔ x = 0 :=
  quadraticChar_eq_zero_iff

theorem ug87_sum_even [CharP K 2] (hr8 : r % 8 = 1) (F : ZMod r → K) (hF : ∀ x, F (-x) = F x) :
    ∑ x : ZMod r, F x = F 0 := by
  classical
  rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ (0 : ZMod r))]
  have h0 : ∑ x ∈ Finset.univ.erase (0 : ZMod r), F x = 0 := by
    refine Finset.sum_involution (fun a _ => -a) ?_ ?_ ?_ ?_
    · intro a _
      rw [hF a]
      exact CharTwo.add_self_eq_zero _
    · intro a ha _ hneg
      have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
      apply ha0
      have h2a : (2 : ZMod r) * a = 0 := by linear_combination -hneg
      exact (mul_eq_zero.mp h2a).resolve_left (ug87_two_ne_zero hr8)
    · intro a ha
      refine Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase ha), Finset.mem_univ _⟩
    · intro a _
      exact neg_neg a
  rw [h0, add_zero]

@[expose] def ug87_eta (ψ : AddChar (ZMod r) K) (δ : ℤ) : K :=
  ∑ x : ZMod r, if χ x = δ then ψ x else 0

theorem ug87_eta_add [CharP K 2] {ψ : AddChar (ZMod r) K} (hψ : ψ ≠ 1) :
    ug87_eta ψ 1 + ug87_eta ψ (-1) = 1 := by
  classical
  unfold ug87_eta
  rw [← Finset.sum_add_distrib]
  have key : ∀ x : ZMod r, ((if χ x = 1 then ψ x else 0) + (if χ x = -1 then ψ x else 0)) =
      ψ x + (if x = 0 then 1 else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [quadraticChar_zero, AddChar.map_zero_eq_one, CharTwo.add_self_eq_zero]
    · rcases quadraticChar_dichotomy hx with h | h
      · simp [h, hx]
      · simp [h, hx]
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib,
    AddChar.sum_eq_zero_of_ne_one hψ, Finset.sum_ite_eq' Finset.univ (0 : ZMod r)]
  simp

theorem ug87_eta_sq [CharP K 2] (hr8 : r % 8 = 1) (ψ : AddChar (ZMod r) K) (δ : ℤ) :
    ug87_eta ψ δ ^ 2 = ug87_eta ψ δ := by
  classical
  have hExp : ExpChar K 2 := ExpChar.prime Nat.prime_two
  unfold ug87_eta
  rw [sum_pow_char 2]
  refine Fintype.sum_bijective (fun x : ZMod r => 2 * x)
    (mulLeft_bijective₀ (2 : ZMod r) (ug87_two_ne_zero hr8)) _ _ ?_
  intro x
  show (if χ x = δ then ψ x else 0) ^ 2 = if χ (2 * x) = δ then ψ (2 * x) else 0
  rw [map_mul, ug87_chi_two hr8, one_mul]
  split_ifs
  · rw [sq, ← AddChar.map_add_eq_mul, two_mul]
  · simp

theorem ug87_exists_sigma [CharP K 2] (hr8 : r % 8 = 1) {ψ : AddChar (ZMod r) K} (hψ : ψ ≠ 1) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ug87_eta ψ σ = 1 ∧ ug87_eta ψ (-σ) = 0 := by
  have hadd := ug87_eta_add hψ
  have hsq := ug87_eta_sq hr8 ψ 1
  have hmul : ug87_eta ψ 1 * (ug87_eta ψ 1 - 1) = 0 := by
    rw [mul_sub, mul_one, ← sq, hsq, sub_self]
  rcases mul_eq_zero.mp hmul with h | h
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · rw [h, zero_add] at hadd
      exact hadd
    · rw [neg_neg]
      exact h
  · have h1 : ug87_eta ψ 1 = 1 := sub_eq_zero.mp h
    refine ⟨1, Or.inl rfl, h1, ?_⟩
    rw [h1] at hadd
    have : ug87_eta ψ (-1) = 0 := by linear_combination hadd
    exact this

theorem ug87_G (ψ : AddChar (ZMod r) K) (δ : ℤ) {u : ZMod r} (hu : u ≠ 0) :
    ∑ x : ZMod r, (if χ x = δ then ψ (u * x) else 0) = ug87_eta ψ (δ * χ u) := by
  classical
  have hχu : χ u ≠ 0 := fun h => hu ((ug87_chi_eq_zero_iff u).mp h)
  unfold ug87_eta
  refine Fintype.sum_bijective (fun x : ZMod r => u * x) (mulLeft_bijective₀ u hu) _ _ ?_
  intro x
  show (if χ x = δ then ψ (u * x) else 0) = if χ (u * x) = δ * χ u then ψ (u * x) else 0
  have hmul : χ (u * x) = χ u * χ x := map_mul _ _ _
  by_cases hx : χ x = δ
  · rw [if_pos hx, if_pos (by rw [hmul, hx, mul_comm])]
  · rw [if_neg hx, if_neg]
    intro h
    exact hx (mul_left_cancel₀ hχu ((hmul.symm.trans h).trans (mul_comm _ _)))

theorem ug87_ft_chi [CharP K 2] (hr8 : r % 8 = 1) {ψ : AddChar (ZMod r) K} {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (h1 : ug87_eta ψ σ = 1) (h0 : ug87_eta ψ (-σ) = 0)
    (φ : ℤ → K) (u : ZMod r) :
    ∑ x : ZMod r, φ (χ x) * ψ (u * x) = φ 0 + if u = 0 then 0 else φ (σ * χ u) := by
  classical
  by_cases hu : u = 0
  · subst hu
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one, if_true, add_zero]
    rw [ug87_sum_even hr8 (fun x => φ (χ x)) (fun x => by simp only [ug87_chi_neg hr8])]
    simp [quadraticChar_zero]
  · have hpt : ∀ x : ZMod r, φ (χ x) * ψ (u * x) =
        (if x = 0 then φ 0 else 0) + φ 1 * (if χ x = 1 then ψ (u * x) else 0) +
          φ (-1) * (if χ x = -1 then ψ (u * x) else 0) := by
      intro x
      by_cases hx : x = 0
      · subst hx
        simp [quadraticChar_zero]
      · rcases quadraticChar_dichotomy hx with h | h
        · simp [h, hx]
        · simp [h, hx]
    rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ (0 : ZMod r),
      ug87_G ψ 1 hu, ug87_G ψ (-1) hu]
    simp only [Finset.mem_univ, if_true, hu, if_false]
    rcases quadraticChar_dichotomy hu with hp | hp <;> rcases hσ with rfl | rfl <;>
      simp_all

theorem ug87_ft_e [CharP K 2] (hr8 : r % 8 = 1) {ψ : AddChar (ZMod r) K} {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (h1 : ug87_eta ψ σ = 1) (h0 : ug87_eta ψ (-σ) = 0)
    (φ : ℤ → K) (u : ZMod r) :
    ∑ x : ZMod r, φ (σ * χ x) * ψ (u * x) = φ 0 + if u = 0 then 0 else φ (χ u) := by
  have h := ug87_ft_chi hr8 hσ h1 h0 (fun n => φ (σ * n)) u
  have hσσ : σ * (σ * χ u) = χ u := by rcases hσ with rfl | rfl <;> ring
  simp only [mul_zero, hσσ] at h
  exact h

end Arith

end CFSG.LieType.SeitzGeneration

end
