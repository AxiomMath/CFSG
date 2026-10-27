module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSL
public import CFSG.LieType.SpecialLinear.CurtisDatum.NegExcept
public import CFSG.LieType.SpecialLinear.CurtisDatum.RankOne
public import CFSG.LieType.Steinberg.Bridge

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

variable (m : ℕ) (F : Type) [Field F]

private theorem hdiag_coe' (k : Fin m) (u : Fˣ) :
    (hdiag m F k u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal fun r => if r = k.castSucc then (u : F) else
        if r = k.succ then ((u⁻¹ : Fˣ) : F) else 1 :=
  SpecialLinearGroup.diag2nUnit_coe _ u

private theorem diag2n_succ_eq_hdiag (k : Fin m) {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n (i := (k.castSucc : Fin (m + 1))) (j := (k.succ : Fin (m + 1)))
        (Fin.castSucc_lt_succ (i := k)).ne a ha =
      hdiag m F k (Units.mk0 a ha) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.diag2n_coe, hdiag_coe']
  apply congrArg Matrix.diagonal
  funext r
  split_ifs <;> simp [Units.val_mk0]

theorem diag2n_swap {i j : Fin (m + 1)} (hij : i ≠ j) {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha =
      SpecialLinearGroup.diag2n hij.symm a⁻¹ (inv_ne_zero ha) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.diag2n_coe]
  apply congrArg Matrix.diagonal
  funext r
  by_cases h1 : r = i
  · subst r
    rw [if_pos rfl, if_neg hij, if_pos rfl, inv_inv]
  · by_cases h2 : r = j
    · subst r
      rw [if_neg h1, if_pos rfl, if_pos rfl]
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

theorem diag2n_mul_mid {i l j : Fin (m + 1)} (hil : i ≠ l) (hlj : l ≠ j) (hij : i ≠ j)
    {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hil a ha * SpecialLinearGroup.diag2n hlj a ha =
      SpecialLinearGroup.diag2n hij a ha := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.diag2n_coe,
    SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext r
  by_cases h1 : r = i
  · subst r
    simp only [if_neg hil, if_neg hij, mul_one]
  · by_cases h2 : r = l
    · subst r
      simp only [if_neg h1, if_neg hlj]
      exact inv_mul_cancel₀ ha
    · by_cases h3 : r = j
      · subst r
        simp only [if_neg h1, if_neg h2, one_mul]
      · simp only [if_neg h1, if_neg h2, if_neg h3, mul_one]

private theorem diag2n_congr {i j i' j' : Fin (m + 1)} (hi : i = i') (hj : j = j')
    (hij : i ≠ j) (hij' : i' ≠ j') {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha = SpecialLinearGroup.diag2n hij' a ha := by
  apply Subtype.ext
  rw [SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.diag2n_coe]
  apply congrArg Matrix.diagonal
  funext r
  rw [hi, hj]

private theorem diag2n_eq_hdiag_of_adjacent {i j : Fin (m + 1)} (hi : i.val < m) (hij : i < j)
    (hji : j = (⟨i.val + 1, by omega⟩ : Fin (m + 1))) {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij.ne a ha =
      hdiag m F ⟨i.val, hi⟩ (Units.mk0 a ha) := by
  let k : Fin m := ⟨i.val, hi⟩
  have hik : (k.castSucc : Fin (m + 1)) = i := Fin.ext rfl
  have hjk : (k.succ : Fin (m + 1)) = j := by
    apply Fin.ext
    simp only [k, Fin.val_succ]
    rw [hji]
  rw [diag2n_congr m F (i := i) (j := j) (i' := (k.castSucc : Fin (m + 1)))
    (j' := (k.succ : Fin (m + 1))) hik.symm hjk.symm hij.ne
    ((Fin.castSucc_lt_succ (i := k)).ne) ha]
  exact diag2n_succ_eq_hdiag m F k ha

theorem diag2n_mem_iSup_torus_aux (d : ℕ) :
    ∀ (i j : Fin (m + 1)) (hij : i < j), j.val - i.val = d → ∀ {a : F} (ha : a ≠ 0),
      SpecialLinearGroup.diag2n hij.ne a ha ∈ ⨆ k, torus m F k := by
  induction d with
  | zero =>
    intro i j hij hd a ha
    omega
  | succ d ih =>
    intro i j hij hd a ha
    by_cases hd0 : d = 0
    ·
      have hji : j = (⟨i.val + 1, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext
        show j.val = i.val + 1
        omega
      have hi : i.val < m := by
        have h2 := j.isLt
        omega
      rw [diag2n_eq_hdiag_of_adjacent m F hi hij hji ha]
      exact hdiag_mem_H m F ⟨i.val, hi⟩ (Units.mk0 a ha)
    ·
      have hi : i.val < m := by
        have h2 := j.isLt
        omega
      let i' : Fin (m + 1) := ⟨i.val + 1, by omega⟩
      have hii' : i < i' := by
        rw [Fin.lt_def]
        show i.val < i.val + 1
        omega
      have hi'j : i' < j := by
        rw [Fin.lt_def]
        show i.val + 1 < j.val
        omega
      have hd' : j.val - i'.val = d := by
        show j.val - (i.val + 1) = d
        omega
      have hmem_mid : SpecialLinearGroup.diag2n hi'j.ne a ha ∈ ⨆ k, torus m F k :=
        ih i' j hi'j hd' ha
      let k : Fin m := ⟨i.val, hi⟩
      have hik : (k.castSucc : Fin (m + 1)) = i := Fin.ext rfl
      have hik' : (k.succ : Fin (m + 1)) = i' := by
        apply Fin.ext
        rfl
      have hmem_first : SpecialLinearGroup.diag2n hii'.ne a ha ∈ ⨆ k, torus m F k := by
        have hk : SpecialLinearGroup.diag2n (i := (k.castSucc : Fin (m + 1)))
            (j := (k.succ : Fin (m + 1))) ((Fin.castSucc_lt_succ (i := k)).ne) a ha ∈
            ⨆ k, torus m F k := by
          rw [diag2n_succ_eq_hdiag m F k ha]
          exact hdiag_mem_H m F k (Units.mk0 a ha)
        rwa [diag2n_congr m F (i := (k.castSucc : Fin (m + 1))) (j := (k.succ : Fin (m + 1)))
          (i' := i) (j' := i') hik hik' _ hii'.ne ha] at hk
      have hmul : SpecialLinearGroup.diag2n hii'.ne a ha *
            SpecialLinearGroup.diag2n hi'j.ne a ha ∈ ⨆ k, torus m F k :=
        Subgroup.mul_mem _ hmem_first hmem_mid
      rwa [diag2n_mul_mid m F hii'.ne hi'j.ne hij.ne ha] at hmul

theorem diag2n_mem_iSup_torus {i j : Fin (m + 1)} (hij : i < j) {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij.ne a ha ∈ ⨆ k, torus m F k :=
  diag2n_mem_iSup_torus_aux m F (j.val - i.val) i j hij rfl ha

theorem iSup_torus_eq_diagonalTorus :
    (⨆ k, torus m F k) = SpecialLinearGroup.diagonalTorus F (m + 1) := by
  refine le_antisymm CFSG.StandardType.GGRootSL.iSup_torus_le_diagonalTorus ?_
  intro g hg
  rw [SpecialLinearGroup.mem_diagonalTorus_iff] at hg
  set D : Fin (m + 1) → F := fun i => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i with hDdef
  have hD : (Matrix.diagonal D).det = 1 := by
    rw [show Matrix.diagonal D = (g : Matrix _ _ F) from hg.diagonal_diag]
    exact g.2
  have hgD : g = (⟨Matrix.diagonal D, hD⟩ : SpecialLinearGroup (Fin (m + 1)) F) :=
    Subtype.ext hg.diagonal_diag.symm
  rw [hgD, SpecialLinearGroup.diag_eq_diag2n_prod (0 : Fin (m + 1)) D hD]
  refine Subgroup.noncommProd_mem _ (SpecialLinearGroup.diag_commute 0 D hD) fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [dite_eq_left hi]
  have hpos : (0 : Fin (m + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
  have hswap := diag2n_swap m F (hij := hi) (a := D i) (SpecialLinearGroup.diagonal_neZero D hD i)
  rw [hswap]
  exact diag2n_mem_iSup_torus m F hpos (inv_ne_zero (SpecialLinearGroup.diagonal_neZero D hD i))

theorem mem_iSup_torus_iff {g : SpecialLinearGroup (Fin (m + 1)) F} :
    g ∈ (⨆ k, torus m F k) ↔
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
  rw [iSup_torus_eq_diagonalTorus, SpecialLinearGroup.mem_diagonalTorus_iff]

theorem iSup_torus_comm {a b : SpecialLinearGroup (Fin (m + 1)) F}
    (ha : a ∈ ⨆ k, torus m F k) (hb : b ∈ ⨆ k, torus m F k) : a * b = b * a := by
  have hda := (mem_iSup_torus_iff m F).mp ha
  have hdb := (mem_iSup_torus_iff m F).mp hb
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← hda.diagonal_diag, ← hdb.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem iSup_torus_le_normalizer_rootGroup {γ : Fin m → ℤ}
    (hγ : γ ∈ roots (isFiniteType_A m) ∅) :
    (⨆ k, torus m F k) ≤ Subgroup.normalizer
      ((rootGroup m F γ : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)) : Set _) := by
  refine iSup_le fun k => ?_
  intro h hh
  have hγ' : γ ∈ (rootDatum m F).roots := by
    rw [show (rootDatum m F).roots = roots (isFiniteType_A m) ∅ from rfl]
    exact hγ
  exact mem_normalizer_rootGroup (D := rootDatum m F) (H := torus m F)
    (isCTGroupDatum m F) hh hγ'

private theorem iSup_torus_le_normalizer_iSup₂ (P : Set (Fin m → ℤ))
    (hP : P ⊆ (rootDatum m F).roots) :
    (⨆ k, torus m F k) ≤ Subgroup.normalizer
      ((⨆ γ ∈ P, rootGroup m F γ :
        Subgroup (SpecialLinearGroup (Fin (m + 1)) F)) : Set _) := by
  refine le_normalizer_iSup₂ fun h hh γ hγ y hy => ?_
  exact Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ
    ((Subgroup.mem_normalizer_iff.mp (iSup_torus_le_normalizer_rootGroup m F (hP hγ) hh) y).mp hy))

theorem iSup_torus_le_normalizer_posUnipotent :
    (⨆ k, torus m F k) ≤ Subgroup.normalizer
      (posUnipotent (rootDatum m F) : Set (SpecialLinearGroup (Fin (m + 1)) F)) := by
  exact iSup_torus_le_normalizer_iSup₂ m F {γ | γ ∈ (rootDatum m F).roots ∧ 0 < ht γ}
    (fun _ hγ => hγ.1)

theorem iSup_torus_le_normalizer_negUnipotent :
    (⨆ k, torus m F k) ≤ Subgroup.normalizer
      (negUnipotent (rootDatum m F) : Set (SpecialLinearGroup (Fin (m + 1)) F)) := by
  exact iSup_torus_le_normalizer_iSup₂ m F {γ | γ ∈ (rootDatum m F).roots ∧ ht γ < 0}
    (fun _ hγ => hγ.1)

theorem iSup_torus_le_normalizer_negUnipotentExcept (i : Fin m) :
    (⨆ k, torus m F k) ≤ Subgroup.normalizer
      (negUnipotentExcept (rootDatum m F) i : Set (SpecialLinearGroup (Fin (m + 1)) F)) := by
  exact iSup_torus_le_normalizer_iSup₂ m F
    {γ | γ ∈ (RootSystem.ofCartan (rootDatum m F).isFiniteType (rootDatum m F).divisible).negExcept i}
    (fun _ hγ => hγ.1.1)

theorem iSup_torus_pow_card_sub_one [Finite F]
    {h : SpecialLinearGroup (Fin (m + 1)) F} (hh : h ∈ ⨆ k, torus m F k) :
    h ^ (Nat.card F - 1) = 1 := by
  have hF : Fintype F := Fintype.ofFinite F
  have hdiag := (mem_iSup_torus_iff m F).mp hh
  set D : Fin (m + 1) → F := fun i => (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i with hDdef
  have hD : (Matrix.diagonal D).det = 1 := by
    rw [show Matrix.diagonal D = (h : Matrix _ _ F) from hdiag.diagonal_diag]
    exact h.2
  have hmat : ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ^ (Nat.card F - 1)) = 1 := by
    rw [show (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal D from
      hdiag.diagonal_diag.symm]
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [Pi.pow_apply]
    have hne := SpecialLinearGroup.diagonal_neZero D hD i
    have hpow := @FiniteField.pow_card_sub_one_eq_one F _ hF (D i) hne
    simpa only [@Nat.card_eq_fintype_card F hF] using hpow
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  rw [map_pow, map_one, Matrix.SpecialLinearGroup.coeMonoidHom_apply]
  exact hmat

end CFSG.LieType.SpecialLinear
