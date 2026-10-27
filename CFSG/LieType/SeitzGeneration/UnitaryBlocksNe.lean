module

public import CFSG.LieType.SeitzGeneration.HeisTorusU84
public import CFSG.LinearAlgebra.LinearGroups.Elementary

public section

namespace CFSG.LieType.Universal.SpecialLinear

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem weylMatrix_apply (a b : ι) (i j : ι) :
    weylMatrix (R := R) a b i j =
      if i = Equiv.swap a b j then weylSign (R := R) a j else 0 := by
  rw [weylMatrix, signedPerm_apply]

theorem weylElement_one_eq_weylMatrix {n : ℕ} {K : Type*} [Field K] {a b : Fin n}
    (hab : a ≠ b) :
    CFSG.LinearGroups.weylElement a b (1 : K) = weylMatrix (R := K) a b := by
  unfold CFSG.LinearGroups.weylElement
  rw [← coe_transvection_mul_transvection_mul_transvection (R := K) hab]
  simp [CFSG.LinearGroups.coe_transvection, Matrix.SpecialLinearGroup.coe_mul]

theorem weylMatrix_det {a b : ι} (hab : a ≠ b) :
    (weylMatrix (R := R) a b).det = 1 := by
  rw [← coe_transvection_mul_transvection_mul_transvection (R := R) hab]
  exact (Matrix.SpecialLinearGroup.transvection hab (1 : R) *
    Matrix.SpecialLinearGroup.transvection hab.symm (-1) *
    Matrix.SpecialLinearGroup.transvection hab 1).2

theorem weylMatrix_transpose_mul_self (a b : ι) :
    ((weylMatrix (R := R) a b)ᵀ) * weylMatrix (R := R) a b = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ k, weylMatrix (R := R) a b k i * weylMatrix (R := R) a b k j) =
    if i = j then 1 else 0
  rw [Finset.sum_eq_single (Equiv.swap a b i)
    (fun k _ hk => by rw [weylMatrix_apply]; simp [hk]) (by simp)]
  rw [weylMatrix_apply, weylMatrix_apply]
  by_cases hij : i = j
  · subst hij; simp [weylSign_mul_self]
  · simp [hij, (Equiv.swap a b).injective.eq_iff]

end CFSG.LieType.Universal.SpecialLinear

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.SpecialLinear

variable {ℓ f : ℕ} {K : Type} [Field K]

private theorem weylMatrix_map_bar (h : UnitaryFieldData ℓ f K) {n : ℕ} {b c : Fin n}
    (hbc : b ≠ c) : (weylMatrix (R := K) b c).map h.bar = weylMatrix (R := K) b c := by
  rw [← weylElement_one_eq_weylMatrix hbc]
  unfold CFSG.LinearGroups.weylElement
  simp [Matrix.map_mul, Matrix.map_add, Matrix.map_one, Matrix.map_single,
    h.bar.map_one, h.bar.map_neg]

private theorem weylMatrix_isCoordBlockOn {n : ℕ} {b c : Fin n} (hbc : b ≠ c) :
    IsCoordBlockOn b c (weylMatrix (R := K) b c) := by
  rw [← weylElement_one_eq_weylMatrix hbc, CFSG.LinearGroups.weylElement_eq hbc one_ne_zero]
  intro i j hij
  rcases hij with ⟨hi1, hi2⟩ | ⟨hj1, hj2⟩
  · simp [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply,
      hi1, hi1.symm, hi2, hi2.symm]
  · simp [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply,
      hj1, hj1.symm, hj2, hj2.symm]

private theorem weylMatrix_adj_mul (h : UnitaryFieldData ℓ f K) {n : ℕ} {b c : Fin n}
    (hbc : b ≠ c) :
    ((weylMatrix (R := K) b c).map h.bar)ᵀ * weylMatrix (R := K) b c = 1 := by
  rw [weylMatrix_map_bar h hbc, weylMatrix_transpose_mul_self]

private theorem weylMatrix_mul_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (b c i l : Fin n) :
    (weylMatrix (R := K) b c * g) i l =
      weylSign (R := K) b (Equiv.swap b c i) * g (Equiv.swap b c i) l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap b c i)]
  · rw [weylMatrix_apply]; simp
  · intro k _ hk
    have hne : i ≠ Equiv.swap b c k := by
      intro h
      have h1 : Equiv.swap b c i = k := by rw [h, Equiv.swap_apply_self]
      exact hk h1.symm
    rw [weylMatrix_apply]; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem weylMatrix_conj_apply (h : UnitaryFieldData ℓ f K) {n : ℕ} {b c : Fin n}
    (hbc : b ≠ c) (g : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (weylMatrix (R := K) b c * g *
        ((weylMatrix (R := K) b c).map h.bar)ᵀ) i j =
      weylSign (R := K) b (Equiv.swap b c i) *
        g (Equiv.swap b c i) (Equiv.swap b c j) *
        weylSign (R := K) b (Equiv.swap b c j) := by
  rw [weylMatrix_map_bar h hbc, Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap b c j)]
  · rw [weylMatrix_mul_apply, Matrix.transpose_apply, weylMatrix_apply]; simp
  · intro l _ hl
    have hne : j ≠ Equiv.swap b c l := by
      intro h
      have h1 : Equiv.swap b c j = l := by rw [h, Equiv.swap_apply_self]
      exact hl h1.symm
    rw [weylMatrix_mul_apply, Matrix.transpose_apply, weylMatrix_apply]; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem isCoordBlockOn_weylMatrix_conj (h : UnitaryFieldData ℓ f K) {n : ℕ}
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {g : Matrix (Fin n) (Fin n) K} (hg : IsCoordBlockOn a b g) :
    IsCoordBlockOn a c
      (weylMatrix (R := K) b c * g * ((weylMatrix (R := K) b c).map h.bar)ᵀ) := by
  intro i j hij
  rw [weylMatrix_conj_apply h hbc]
  have hπa : Equiv.swap b c a = a := Equiv.swap_apply_of_ne_of_ne hab hac
  have hπc : Equiv.swap b c c = b := by rw [Equiv.swap_apply_right]
  have hoff : (Equiv.swap b c i ≠ a ∧ Equiv.swap b c i ≠ b) ∨
      (Equiv.swap b c j ≠ a ∧ Equiv.swap b c j ≠ b) := by
    rcases hij with ⟨hi1, hi2⟩ | ⟨hj1, hj2⟩
    · exact Or.inl ⟨fun h => hi1 ((Equiv.swap b c).injective (by rw [h, hπa])),
        fun h => hi2 ((Equiv.swap b c).injective (by rw [h, hπc]))⟩
    · exact Or.inr ⟨fun h => hj1 ((Equiv.swap b c).injective (by rw [h, hπa])),
        fun h => hj2 ((Equiv.swap b c).injective (by rw [h, hπc]))⟩
  rw [hg (Equiv.swap b c i) (Equiv.swap b c j) hoff]
  by_cases hij' : i = j
  · subst hij'
    simp [weylSign_mul_self]
  · simp [hij', (Equiv.swap b c).injective.eq_iff]

private theorem isCoordBlockOn_comm {n : ℕ} {a b : Fin n} {g : Matrix (Fin n) (Fin n) K}
    (hg : IsCoordBlockOn a b g) : IsCoordBlockOn b a g := by
  intro i j hij
  exact hg i j (by
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩)

theorem unitarySU_le_of_blocks_ne (h : UnitaryFieldData ℓ f K) (hq : 4 ≤ ℓ ^ f) {n : ℕ}
    (hn : 3 ≤ n) (a₀ b₀ : Fin n) (M : Subgroup (GL (Fin n) K))
    (hM : ∀ a b : Fin n, a ≠ b → ¬ (a = a₀ ∧ b = b₀) → ¬ (a = b₀ ∧ b = a₀) →
      ∀ g ∈ unitarySU ℓ f K n, IsCoordBlockOn a b (g : Matrix (Fin n) (Fin n) K) → g ∈ M) :
    unitarySU ℓ f K n ≤ M := by
  classical
  refine unitarySU_le_of_blocks h hq (by omega) M ?_
  intro a b hab g hg hblk
  by_cases hplane : (a = a₀ ∧ b = b₀) ∨ (a = b₀ ∧ b = a₀)
  · have hab₀ : a₀ ≠ b₀ := by
      rcases hplane with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    have hblk₀ : IsCoordBlockOn a₀ b₀ (g : Matrix (Fin n) (Fin n) K) := by
      rcases hplane with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [hblk, isCoordBlockOn_comm hblk]
    have hlt : ({a₀, b₀} : Finset (Fin n)).card <
        (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt Finset.card_le_two (by omega)
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({a₀, b₀} : Finset (Fin n))) (t := Finset.univ) hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    have hca : c ≠ a₀ := hc.1
    have hcb : c ≠ b₀ := hc.2
    have hbc : b₀ ≠ c := hcb.symm
    let wm : Matrix (Fin n) (Fin n) K := weylMatrix (R := K) b₀ c
    have hdet : wm.det = 1 := weylMatrix_det hbc
    have hunit : ((wm.map h.bar)ᵀ) * wm = 1 := weylMatrix_adj_mul h hbc
    let w : GL (Fin n) K :=
      Units.mk wm ((wm.map h.bar)ᵀ) (mul_eq_one_comm.mp hunit) hunit
    have hwval : (w : Matrix (Fin n) (Fin n) K) = wm := rfl
    have hwinv : ((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (wm.map h.bar)ᵀ := rfl
    have hwSU : w ∈ unitarySU ℓ f K n := by
      rw [mem_unitarySU_iff h, hwval]
      exact ⟨hdet, hunit⟩
    have hwblk : IsCoordBlockOn b₀ c wm := weylMatrix_isCoordBlockOn hbc
    have hwM : w ∈ M := by
      refine hM b₀ c hbc (by simp [hcb]) (by simp [hca]) w hwSU ?_
      rwa [hwval]
    let g' : GL (Fin n) K := w * g * w⁻¹
    have hg'SU : g' ∈ unitarySU ℓ f K n := mul_mem (mul_mem hwSU hg) (inv_mem hwSU)
    have hg'val : (g' : Matrix (Fin n) (Fin n) K) =
        weylMatrix (R := K) b₀ c * (g : Matrix (Fin n) (Fin n) K) *
          ((weylMatrix (R := K) b₀ c).map h.bar)ᵀ := by
      dsimp only [g']
      simp only [Units.val_mul, hwval, hwinv]
      rfl
    have hg'blk : IsCoordBlockOn a₀ c (g' : Matrix (Fin n) (Fin n) K) := by
      rw [hg'val]
      exact isCoordBlockOn_weylMatrix_conj h hab₀ hca.symm hbc hblk₀
    have hg'M : g' ∈ M := by
      refine hM a₀ c hca.symm (by simp [hcb]) (by simp [hca]) g' hg'SU hg'blk
    have hfinal : g = w⁻¹ * g' * w := by dsimp only [g']; group
    rw [hfinal]
    exact mul_mem (mul_mem (inv_mem hwM) hg'M) hwM
  · exact hM a b hab (fun h => hplane (Or.inl h)) (fun h => hplane (Or.inr h)) g hg hblk

end CFSG.LieType.SeitzGeneration
