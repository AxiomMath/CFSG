module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU2Cell
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.OddStandard.GH71.S55.C5U

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ClassicalInvolution.Phan

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K)

include h in
theorem card_statedSU_four_int :
    (Nat.card (StatedSU 4 (r ^ f) K) : ℤ) = ((r ^ f : ℕ) : ℤ) ^ 6 * ((((r ^ f : ℕ) : ℤ) ^ 2 - 1) *
      ((((r ^ f : ℕ) : ℤ) ^ 3 + 1) * (((r ^ f : ℕ) : ℤ) ^ 4 - 1))) := by
  rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 4) (by norm_num),
    show Finset.Icc 2 4 = {2, 3, 4} by rfl]
  simp only [Finset.mem_insert, Finset.mem_singleton, Nat.reduceEqDiff, or_self,
    not_false_eq_true, Finset.prod_insert, Finset.prod_singleton]
  norm_num

@[expose] noncomputable def su22 :
    StatedSU 2 (r ^ f) K × StatedSU 2 (r ^ f) K →* StatedSU 4 (r ^ f) K :=
  MonoidHom.noncommCoprod (blkSU h 0 (by omega : 0 + 2 ≤ 4)) (blkSU h 2 (by omega : 2 + 2 ≤ 4))
    fun A B => Subtype.ext (blockGL_commute (k := 2) (l := 2) (A : GL (Fin 2) K) B).eq

theorem su22_injective : Function.Injective (su22 h) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B⟩ hAB
  have e : blockGL 4 0 (by omega) (A : GL (Fin 2) K) * blockGL 4 2 (by omega) (B : GL (Fin 2) K) =
      1 := congrArg Subtype.val hAB
  rw [mul_eq_one_iff_eq_inv, ← map_inv] at e
  have hA : (A : GL (Fin 2) K) = 1 := Units.ext (eq_one_of_blockMat_eq (by omega) le_rfl
    (congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) e))
  rw [hA, map_one, eq_comm, map_inv, inv_eq_one] at e
  have e' : blockMat 4 2 ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blockMat 4 2 (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [blockMat_one]
    exact congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) e
  have hB : (B : GL (Fin 2) K) = 1 := Units.ext (blockMat_injective (by omega : 2 + 2 ≤ 4) e')
  exact Prod.ext (Subtype.ext hA) (Subtype.ext hB)

theorem range_su22_le_normalizer :
    (su22 h).range ≤ normalizer ((blkSU h 0 (by omega : 0 + 2 ≤ 4)).range :
      Set (StatedSU 4 (r ^ f) K)) := by
  have key : ∀ (A B C : StatedSU 2 (r ^ f) K),
      su22 h (A, B) * blkSU h 0 (by omega) C * (su22 h (A, B))⁻¹ =
        blkSU h 0 (by omega) (A * C * A⁻¹) := fun A B C =>
    Subtype.ext (conj_blockGL_mul (k := 2) (l := 2) (A : GL (Fin 2) K) C B)
  rintro _ ⟨⟨A, B⟩, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨_, (key A B C).symm⟩
  · rintro ⟨C, hC⟩
    have e : x = su22 h (A⁻¹, B⁻¹) * blkSU h 0 (by omega) C * (su22 h (A⁻¹, B⁻¹))⁻¹ := by
      rw [hC, show ((A⁻¹, B⁻¹) : StatedSU 2 (r ^ f) K × StatedSU 2 (r ^ f) K) = (A, B)⁻¹ from
        rfl, map_inv, inv_inv]
      group
    rw [e, key]
    exact ⟨_, rfl⟩

theorem index_su22 :
    (su22 h).range.index = (r ^ f) ^ 4 * (((r ^ f) ^ 3 + 1) * ((r ^ f) ^ 2 + 1)) := by
  have e1 := Subgroup.card_mul_index (su22 h).range
  have hK := h.card_eq_sq
  have := h.finite
  have : Fact r.Prime := ⟨h.prime⟩
  have : CharP K r := h.charP
  rw [← Nat.card_congr (MonoidHom.ofInjective (su22_injective h)).toEquiv, Nat.card_prod,
    CFSG.RankThree.SubgroupLists.card_statedSU_two hK] at e1
  have e2 := card_statedSU_four_int h
  have hq2 : 2 ≤ r ^ f := h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) r)
  generalize (su22 h).range.index = N at e1 ⊢
  generalize Nat.card (StatedSU 4 (r ^ f) K) = C at e1 e2
  generalize r ^ f = q at e1 e2 hq2 ⊢
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hq1] at e1 ⊢
  rw [e2] at e1
  have hq : (2 : ℤ) ≤ q := by exact_mod_cast hq2
  have hne : ((q : ℤ) * ((q : ℤ) ^ 2 - 1)) * ((q : ℤ) * ((q : ℤ) ^ 2 - 1)) ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
    positivity
  apply mul_left_cancel₀ hne
  rw [e1]
  ring

theorem index_blkGU_three :
    (blkGU h 3).range.index = (r ^ f) ^ 3 * ((r ^ f - 1) * ((r ^ f) ^ 2 + 1)) := by
  have e1 := Subgroup.card_mul_index (blkGU h 3).range
  change _ = Nat.card (StatedSU 4 (r ^ f) K) at e1
  rw [← Nat.card_congr (MonoidHom.ofInjective (blkGU_injective h 3)).toEquiv, card_uU_three h]
    at e1
  have e2 := card_statedSU_four_int h
  have hq2 : 2 ≤ r ^ f := h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) r)
  generalize (blkGU h 3).range.index = N at e1 ⊢
  generalize Nat.card (StatedSU 4 (r ^ f) K) = C at e1 e2
  generalize r ^ f = q at e1 e2 hq2 ⊢
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hq1, (by omega : 1 ≤ q)] at e1 ⊢
  rw [e2] at e1
  have hq : (2 : ℤ) ≤ q := by exact_mod_cast hq2
  have hne : (q : ℤ) ^ 3 * (((q : ℤ) + 1) * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1)) ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
    positivity
  apply mul_left_cancel₀ hne
  rw [e1]
  ring

theorem dvd_cases_four {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : ¬ p ∣ q)
    (h : p ∣ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)))) :
    p ∣ q - 1 ∨ p ∣ q + 1 ∨ p ∣ q ^ 2 - q + 1 ∨ p ∣ q ^ 2 + 1 := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero _
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have e : q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) =
      q ^ 6 * ((q - 1) * (q + 1) *
        ((q + 1) * (q ^ 2 - q + 1) * ((q - 1) * (q + 1) * (q ^ 2 + 1)))) := by
    zify [hq, hq2, hqq, hq4]
    ring
  rw [e] at h
  rcases hp.dvd_mul.1 h with h | h
  · exact absurd (hp.dvd_of_dvd_pow h) hpq
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

theorem lt_four_two (x : ℤ) (hx : 3 ≤ x) :
    4 * (x * (x ^ 2 - 1)) < x ^ 6 * ((x ^ 2 - 1) * ((x ^ 3 + 1) * (x ^ 4 - 1))) := by
  have hx2 : 9 ≤ x ^ 2 := by nlinarith
  have h2 : 0 < x ^ 2 - 1 := by linarith
  have h1 : 0 < x * (x ^ 2 - 1) := by positivity
  have h3 : (28 : ℤ) ≤ x ^ 3 + 1 := by nlinarith
  have h4 : (80 : ℤ) ≤ x ^ 4 - 1 := by nlinarith
  have h5 : (243 : ℤ) ≤ x ^ 5 := by nlinarith
  have h34 : (28 * 80 : ℤ) ≤ (x ^ 3 + 1) * (x ^ 4 - 1) :=
    mul_le_mul h3 h4 (by norm_num) (by linarith)
  have h6 : (4 : ℤ) < x ^ 5 * ((x ^ 3 + 1) * (x ^ 4 - 1)) := by nlinarith
  have := mul_lt_mul_of_pos_left h6 h1
  nlinarith

theorem lt_four_three (x : ℤ) (hx : 3 ≤ x) :
    4 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1))) <
      x ^ 6 * ((x ^ 2 - 1) * ((x ^ 3 + 1) * (x ^ 4 - 1))) := by
  have hx2 : 9 ≤ x ^ 2 := by nlinarith
  have h2 : 0 < x ^ 2 - 1 := by linarith
  have h1 : 0 < x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) := by positivity
  have h4 : (80 : ℤ) ≤ x ^ 4 - 1 := by nlinarith
  have h5 : (27 : ℤ) ≤ x ^ 3 := by nlinarith
  have h6 : (4 : ℤ) < x ^ 3 * (x ^ 4 - 1) := by nlinarith
  have := mul_lt_mul_of_pos_left h6 h1
  nlinarith

end CFSG.OddStandard.GH71.S55.C5U
