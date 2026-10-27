module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

section Lift

variable {n : ℕ} {K : Type*} [Field K]

theorem eq_zero_or_eq_one_of_card_two [Finite K] (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite K
  have h3 : ({0, 1, c} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, 1, c, zero_ne_one, hcon.1.symm, hcon.2.symm, rfl⟩
  have := Finset.card_le_univ ({0, 1, c} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at this
  omega

@[expose] def blkIdxN (a m : ℕ) (h : a + m ≤ n) (i : Fin m) : Fin n :=
  ⟨a + i, by have := i.isLt; omega⟩

theorem blkIdxN_ne {a m : ℕ} {h : a + m ≤ n} {i j : Fin m} (hij : i ≠ j) :
    blkIdxN a m h i ≠ blkIdxN a m h j := by
  intro e
  apply hij
  have := congrArg Fin.val e
  simp only [blkIdxN] at this
  exact Fin.ext (by omega)

@[expose] def liftT (a m : ℕ) (h : a + m ≤ n) {i j : Fin m} (hij : i ≠ j) :
    SpecialLinearGroup (Fin n) K :=
  SpecialLinearGroup.transvection (blkIdxN_ne (h := h) hij) (1 : K)

theorem coe_liftT (a m : ℕ) (h : a + m ≤ n) {i j : Fin m} (hij : i ≠ j) :
    ((liftT (K := K) a m h hij : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + Matrix.single (blkIdxN a m h i) (blkIdxN a m h j) (1 : K) := rfl

theorem blkAt_liftT (a m : ℕ) (h : a + m ≤ n) {i j : Fin m} (hij : i ≠ j) :
    blkAt a m h ((liftT (K := K) a m h hij : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j (1 : K) := by
  ext i' j'
  rw [blkAt_apply, coe_liftT]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, blkIdxN,
    Nat.add_left_cancel_iff, Fin.ext_iff]

theorem liftT_mem_flagStabilizer {I : Set ℕ} (a m : ℕ) (h : a + m ≤ n)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) {i j : Fin m} (hij : i ≠ j) :
    (liftT a m h hij : SpecialLinearGroup (Fin n) K) ∈ flagStabilizer n K I := by
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  rw [coe_liftT]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have hkl : k ≠ l := fun e => by subst e; omega
  have hne : ¬ (blkIdxN a m h i = k ∧ blkIdxN a m h j = l) := by
    rintro ⟨e1, e2⟩
    have h1 : (i : ℕ) < m := i.isLt
    have h2 := congrArg Fin.val e1
    have h3 := congrArg Fin.val e2
    simp only [blkIdxN] at h2 h3
    exact hno c hc ⟨by omega, by omega⟩
  simp [hkl, hne]

end Lift

section BigBlock

variable {n : ℕ} {K : Type*} [Field K]

@[expose] noncomputable def bigBlockHom [Finite K] (I : Set ℕ) (a m : ℕ) (h : a + m ≤ n)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I) :
    ↥(perfectCore (flagStabilizer n K I)) →* SpecialLinearGroup (Fin m) K :=
  blkSL (flagStabilizer n K I) a m h (blockLeft_of_cut m ha) (blockRight_of_cut hb)
    (perfectCore_le _) (Subgroup.isPerfect_iff.mpr (perfectCore_perfect _))

theorem bigBlockHom_coe [Finite K] (I : Set ℕ) (a m : ℕ) (h : a + m ≤ n) (ha : a = 0 ∨ a ∈ I)
    (hb : a + m = n ∨ a + m ∈ I) (x : ↥(perfectCore (flagStabilizer n K I))) :
    ((bigBlockHom I a m h ha hb x : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      blkAt a m h ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem bigBlockHom_surjective [Finite K] (hK : Nat.card K = 2) {I : Set ℕ} {a m : ℕ}
    (h : a + m ≤ n) (hm3 : 3 ≤ m) (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) :
    Function.Surjective (bigBlockHom (K := K) I a m h ha hb) := by
  classical
  set H : Subgroup (SpecialLinearGroup (Fin n) K) := flagStabilizer n K I with hH
  set P₀ : Subgroup (SpecialLinearGroup (Fin n) K) :=
    Subgroup.closure {x | ∃ (i j : Fin m) (hij : i ≠ j), x = liftT a m h hij} with hP₀
  have hP₀H : P₀ ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, hij, rfl⟩
    exact liftT_mem_flagStabilizer a m h hno hij
  have hgen : ∀ (i j : Fin m) (hij : i ≠ j), liftT a m h hij ∈ P₀ := fun i j hij =>
    Subgroup.subset_closure ⟨i, j, hij, rfl⟩
  have hP₀perf : ⁅P₀, P₀⁆ = P₀ := by
    have h1 : ⁅P₀, P₀⁆ ≤ P₀ := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    have h2 : P₀ ≤ ⁅P₀, P₀⁆ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, j, hij, rfl⟩
      obtain ⟨k, hki, hkj⟩ : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
        by_contra hcon
        push Not at hcon
        have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun k _ => by
          by_cases hki : k = i
          · simp [hki]
          · simp [hcon k hki]
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_le_two (a := i) (b := j)
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        omega
      have hcomm : ⁅(liftT a m h (Ne.symm hki) : SpecialLinearGroup (Fin n) K),
          (liftT a m h hkj : SpecialLinearGroup (Fin n) K)⁆ = liftT a m h hij := by
        have := SpecialLinearGroup.commutatorElement_transvection
          (blkIdxN_ne (h := h) (Ne.symm hki)) (blkIdxN_ne (h := h) hkj)
          (blkIdxN_ne (h := h) hij) (1 : K) 1
        rw [mul_one] at this
        exact this
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator (hgen _ _ _) (hgen _ _ _)
    exact le_antisymm h1 h2
  have hP₀N : P₀ ≤ perfectCore H := le_perfectCore_of_perfect hP₀H hP₀perf
  have hE : ∀ x ∈ CFSG.LinearGroups.elementarySet m K,
      x ∈ (bigBlockHom (K := K) I a m h ha hb).range := by
    rintro _ ⟨i, j, hij, c, rfl⟩
    rcases eq_zero_or_eq_one_of_card_two hK c with rfl | rfl
    · have : (SpecialLinearGroup.transvection hij (0 : K) : SpecialLinearGroup (Fin m) K) = 1 :=
        Subtype.ext (by rw [CFSG.LinearGroups.coe_transvection]; simp)
      rw [this]
      exact one_mem _
    · refine ⟨⟨liftT a m h hij, hP₀N (hgen i j hij)⟩, Subtype.ext ?_⟩
      rw [bigBlockHom_coe]
      exact blkAt_liftT a m h hij
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation (n := m) (K := K)]
  exact (Subgroup.closure_le _).2 hE

end BigBlock

end CFSG.QuasithinUnique.Vol2Native.A312L
