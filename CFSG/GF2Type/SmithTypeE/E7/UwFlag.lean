module

public import CFSG.GF2Type.SmithTypeE.E7.UwMat
import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.GF2Type.SmithTypeE.E7

open scoped Matrix

theorem isUT_mul {A B : M6} (hA : IsUT A) (hB : IsUT B) : IsUT (A * B) := by
  intro i j hji
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA i i le_rfl, if_pos rfl, one_mul, hB i j hji]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [hA i k hlt.le, if_neg hlt.ne', zero_mul]
    · rw [hB k j (hji.trans hgt.le), if_neg (lt_of_le_of_lt hji hgt).ne', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem isUT_one : IsUT (1 : M6) := fun _ _ _ => Matrix.one_apply

theorem isUT_inv {g : GL6} (hg : IsUT (g : M6)) : IsUT ((g⁻¹ : GL6) : M6) := by
  have hpow : ∀ n : ℕ, IsUT ((g ^ n : GL6) : M6) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Units.val_one]; exact isUT_one
    | succ n ih => rw [pow_succ, Units.val_mul]; exact isUT_mul ih hg
  have hpos : 0 < orderOf g := orderOf_pos g
  have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', show orderOf g - 1 + 1 = orderOf g by omega, pow_orderOf_eq_one]
  rw [hinv]
  exact hpow _

@[expose] def UTsub : Subgroup GL6 where
  carrier := {g | IsUT (g : M6)}
  mul_mem' := fun {a b} ha hb => by
    show IsUT ((a * b : GL6) : M6)
    rw [Units.val_mul]
    exact isUT_mul ha hb
  one_mem' := by
    show IsUT ((1 : GL6) : M6)
    rw [Units.val_one]
    exact isUT_one
  inv_mem' := fun {g} hg => by
    show IsUT ((g⁻¹ : GL6) : M6)
    exact isUT_inv hg

theorem mem_UTsub {g : GL6} : g ∈ UTsub ↔ IsUT (g : M6) := Iff.rfl

theorem isUT_ext_of_upper {A B : M6} (hA : IsUT A) (hB : IsUT B)
    (h : ∀ i j : Fin 6, i < j → A i j = B i j) : A = B := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact h i j hij
  · rw [hA i i le_rfl, hB i i le_rfl]
  · rw [hA i j hij.le, hB i j hij.le]

abbrev UTpos : Type := {p : Fin 6 × Fin 6 // p.1 < p.2}

theorem card_UTpos : Nat.card UTpos = 15 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def UTofEntries (c : UTpos → ZMod 2) : M6 :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j then c ⟨(i, j), h⟩ else 0

theorem UTofEntries_diag (c : UTpos → ZMod 2) (i : Fin 6) : UTofEntries c i i = 1 := by
  simp [UTofEntries]

theorem UTofEntries_lower (c : UTpos → ZMod 2) {i j : Fin 6} (h : j < i) :
    UTofEntries c i j = 0 := by
  have hne : i ≠ j := h.ne'
  have hnlt : ¬ i < j := not_lt.mpr h.le
  simp [UTofEntries, hne, hnlt]

theorem UTofEntries_up (c : UTpos → ZMod 2) (p : UTpos) :
    UTofEntries c p.1.1 p.1.2 = c p := by
  have hne : p.1.1 ≠ p.1.2 := p.2.ne
  rw [UTofEntries, Matrix.of_apply, if_neg hne, dif_pos p.2]

theorem isUT_UTofEntries (c : UTpos → ZMod 2) : IsUT (UTofEntries c) := by
  intro i j hji
  by_cases hij : i = j
  · subst hij
    rw [UTofEntries_diag, if_pos rfl]
  · rw [UTofEntries_lower c (lt_of_le_of_ne hji (Ne.symm hij)), if_neg hij]

theorem det_UTofEntries (c : UTpos → ZMod 2) : (UTofEntries c).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · exact Finset.prod_eq_one fun i _ => UTofEntries_diag c i
  · intro i j hji
    exact UTofEntries_lower c hji

theorem isUnit_det_UTofEntries (c : UTpos → ZMod 2) : IsUnit (UTofEntries c).det := by
  rw [det_UTofEntries]
  exact isUnit_one

@[expose] noncomputable def UTunit (c : UTpos → ZMod 2) : GL6 :=
  Matrix.GeneralLinearGroup.mk'' (UTofEntries c) (isUnit_det_UTofEntries c)

theorem UTunit_val (c : UTpos → ZMod 2) : ((UTunit c : GL6) : M6) = UTofEntries c := rfl

@[expose] noncomputable def UTelem (c : UTpos → ZMod 2) : UTsub :=
  ⟨UTunit c, mem_UTsub.mpr (by rw [UTunit_val]; exact isUT_UTofEntries c)⟩

theorem card_UTsub : Nat.card UTsub = 2 ^ 15 := by
  have hT : Nat.card (UTpos → ZMod 2) = 2 ^ 15 := by
    rw [Nat.card_fun, Nat.card_zmod, card_UTpos]
  refine le_antisymm ?_ ?_
  · rw [← hT]
    refine Nat.card_le_card_of_injective
      (fun g : UTsub => fun p : UTpos => ((g : GL6) : M6) p.1.1 p.1.2) ?_
    intro g h hgh
    refine Subtype.ext (Units.ext ?_)
    refine isUT_ext_of_upper (mem_UTsub.mp g.2) (mem_UTsub.mp h.2) ?_
    intro i j hij
    exact congrFun hgh ⟨(i, j), hij⟩
  · rw [← hT]
    refine Nat.card_le_card_of_injective UTelem ?_
    intro c d hcd
    have hM : UTofEntries c = UTofEntries d :=
      congrArg (fun x : UTsub => ((x : GL6) : M6)) hcd
    funext p
    have h1 := congrFun (congrFun hM p.1.1) p.1.2
    rw [UTofEntries_up, UTofEntries_up] at h1
    exact h1

theorem card_GL6 : Nat.card GL6 = 2 ^ 15 * 615195 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 6, ZMod.card]
  norm_num [Fin.prod_univ_six]

theorem index_UTsub : UTsub.index = 615195 := by
  have h := Subgroup.card_mul_index (H := UTsub)
  rw [card_UTsub, card_GL6] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem exists_conj_isUT (H : Subgroup GL6) (hH : IsPGroup 2 H) :
    ∃ g : GL6, ∀ h ∈ H, IsUT ((g * h * g⁻¹ : GL6) : M6) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 GL6) :=
    Finite.of_injective (fun P : Sylow 2 GL6 => (P : Set GL6)) SetLike.coe_injective
  have hUT2 : IsPGroup 2 UTsub := IsPGroup.of_card card_UTsub
  have hidx : ¬ 2 ∣ UTsub.index := by
    rw [index_UTsub]
    decide
  obtain ⟨S, hS⟩ : ∃ S : Sylow 2 GL6, (S : Subgroup GL6) = UTsub :=
    ⟨hUT2.toSylow hidx, rfl⟩
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hH
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GL6 S Q
  refine ⟨g⁻¹, fun h hh => ?_⟩
  have hhQ : h ∈ (Q : Subgroup GL6) := hQ hh
  rw [← hg, Sylow.coe_subgroup_smul] at hhQ
  obtain ⟨s, hsS, hs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hhQ
  rw [hS] at hsS
  have hs' : g * s * g⁻¹ = h := hs
  have hconj : g⁻¹ * h * g⁻¹⁻¹ = s := by
    rw [inv_inv, ← hs']
    group
  rw [hconj]
  exact mem_UTsub.mp hsS

end CFSG.GF2Type.SmithTypeE.E7
