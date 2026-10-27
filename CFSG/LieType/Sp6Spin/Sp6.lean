module

public import CFSG.LieType.Universal.SymplecticExtras.TorusWeyl
import CFSG.LieType.Universal.SymplecticRoots.Weyl
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

public section

namespace CFSG.LieType.Sp6Spin

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Universal.Symplectic
  TauCeti.GLSymplecticFin

variable {K : Type} [Field K]

@[expose] def IsShortIndex {n : ℕ} : RootSubgroupIndex n → Prop
  | .positiveLong _ => False
  | .negativeLong _ => False
  | _ => True

theorem sw_conj_elt_difference [CharP K 2] {i j : Fin 3} (hij : i ≠ j)
    {a b : Fin 3} (hab : a ≠ b) (c : K) :
    sw hij * elt (.difference a b hab) c * (sw hij)⁻¹ =
      elt (.difference (Equiv.swap i j a) (Equiv.swap i j b)
        ((Equiv.swap i j).injective.ne hab)) c := by
  simp only [sw, elt]
  rw [← map_inv, ← map_mul, ← map_mul]
  simpa only [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply,
    CharTwo.neg_eq, ite_self, one_mul, mul_one, toAdd_ofAdd] using
    congrArg (equivStatedSp 3 K) (shortWeyl_conj_difference hij hab c)

theorem lw_conj_elt_difference_to_positiveSum [CharP K 2] {a b : Fin 3} (hab : a < b) (c : K) :
    lw b * elt (.difference a b hab.ne) c * (lw b)⁻¹ = elt (.positiveSum a b hab) c := by
  have h := longWeyl_conj_difference_right (R := K) (a := a) (k := b) hab.ne c
  rw [show -c = c from CharTwo.neg_eq c] at h
  simp only [lw, elt, ← map_inv, ← map_mul, ← map_mul,
    RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_positiveSum,
    differenceShortRootHom_apply, positiveSumShortRootHom_apply, toAdd_ofAdd]
  simpa only using congrArg (equivStatedSp 3 K) h

theorem lw_conj_elt_difference_to_negativeSum [CharP K 2] {a b : Fin 3} (hab : a < b) (c : K) :
    lw a * elt (.difference a b hab.ne) c * (lw a)⁻¹ = elt (.negativeSum a b hab) c := by
  have h := longWeyl_conj_difference_left (R := K) (k := a) (b := b) hab.ne c
  rw [show -c = c from CharTwo.neg_eq c] at h
  simp only [lw, elt, ← map_inv, ← map_mul, ← map_mul,
    RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_negativeSum,
    differenceShortRootHom_apply, negativeSumShortRootHom_apply, toAdd_ofAdd]
  simpa only using congrArg (equivStatedSp 3 K) h

theorem sw_conj_elt_negativeLong [CharP K 2] {i j : Fin 3} (hij : i ≠ j) (a : Fin 3) (c : K) :
    sw hij * elt (.negativeLong a) c * (sw hij)⁻¹ =
      elt (.negativeLong (Equiv.swap i j a)) c := by
  simp only [sw, elt]
  rw [← map_inv, ← map_mul, ← map_mul]
  simpa only [RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
    toAdd_ofAdd] using
    congrArg (equivStatedSp 3 K) (shortWeyl_conj_negativeLong hij a c)

theorem commute_lw_elt_positiveLong_two {k : Fin 3} (hk : k ≠ 2) (c : K) :
    Commute (lw k) (elt (.positiveLong 2) c) := by
  rw [commute_iff_eq]
  calc lw k * elt (.positiveLong 2) c
      = (lw k * elt (.positiveLong 2) c * (lw k)⁻¹) * lw k := by group
    _ = elt (.positiveLong 2) c * lw k := by
        rw [lw_conj_elt_positiveLong_of_ne (Ne.symm hk) c]

theorem commute_sw_elt_positiveLong_two (c : K) :
    Commute (sw (show (0 : Fin 3) ≠ 1 by decide)) (elt (.positiveLong 2) c) := by
  rw [commute_iff_eq]
  calc sw (show (0 : Fin 3) ≠ 1 by decide) * elt (.positiveLong 2) c
      = (sw (show (0 : Fin 3) ≠ 1 by decide) * elt (.positiveLong 2) c *
          (sw (show (0 : Fin 3) ≠ 1 by decide))⁻¹) *
          sw (show (0 : Fin 3) ≠ 1 by decide) := by group
    _ = elt (.positiveLong 2) c * sw (show (0 : Fin 3) ≠ 1 by decide) := by
        rw [sw_conj_elt_positiveLong (show (0 : Fin 3) ≠ 1 by decide) 2 c,
          show (Equiv.swap (0 : Fin 3) 1) 2 = 2 from by decide]

theorem not_commute_elt_difference_positiveLong :
    ¬ Commute (elt (n := 3) (F := K) (.difference 0 2 (by decide)) (1 : K))
      (elt (n := 3) (F := K) (.positiveLong 2) 1) := by
  intro h
  have hm : mat 3 K (elt (n := 3) (F := K) (.difference 0 2 (by decide)) (1 : K) *
      elt (n := 3) (F := K) (.positiveLong 2) (1 : K)) =
      mat 3 K (elt (n := 3) (F := K) (.positiveLong 2) (1 : K) *
        elt (n := 3) (F := K) (.difference 0 2 (by decide)) (1 : K)) := by
    rw [h.eq]
  simp only [map_mul, mat_elt] at hm
  have hentry := congrArg (fun M => M (.inl 0) (.inr 2)) hm
  simp [E, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three] at hentry

end CFSG.LieType.Sp6Spin

namespace CFSG.LieType.Sp6Spin

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Universal.Symplectic
  TauCeti.GLSymplecticFin

variable {K : Type} [Field K]

private noncomputable def baseElt (c : K) : StatedSp 3 K :=
  elt (n := 3) (F := K) (.difference 0 1 (by decide)) c

private theorem baseElt_eq (c : K) :
    baseElt c = elt (n := 3) (F := K) (.difference 0 1 (by decide)) c := by
  rw [baseElt]

private theorem conj_base_10 [CharP K 2] (c : K) :
    sw (show (0 : Fin 3) ≠ 1 by decide) * baseElt c *
        (sw (show (0 : Fin 3) ≠ 1 by decide))⁻¹ =
      elt (n := 3) (F := K) (.difference 1 0 (by decide)) c := by
  rw [baseElt, sw_conj_elt_difference (show (0 : Fin 3) ≠ 1 by decide)]
  congr 1

private theorem conj_base_02 [CharP K 2] (c : K) :
    sw (show (1 : Fin 3) ≠ 2 by decide) * baseElt c *
        (sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹ =
      elt (n := 3) (F := K) (.difference 0 2 (by decide)) c := by
  rw [baseElt, sw_conj_elt_difference (show (1 : Fin 3) ≠ 2 by decide)]
  congr 1

private theorem conj_base_21 [CharP K 2] (c : K) :
    sw (show (0 : Fin 3) ≠ 2 by decide) * baseElt c *
        (sw (show (0 : Fin 3) ≠ 2 by decide))⁻¹ =
      elt (n := 3) (F := K) (.difference 2 1 (by decide)) c := by
  rw [baseElt, sw_conj_elt_difference (show (0 : Fin 3) ≠ 2 by decide)]
  congr 1

private theorem conj_base_12 [CharP K 2] (c : K) :
    (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide)) *
        baseElt c *
        (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹ =
      elt (n := 3) (F := K) (.difference 1 2 (by decide)) c := by
  calc (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide)) *
        baseElt c *
        (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹
      = sw (show (0 : Fin 3) ≠ 1 by decide) *
          (sw (show (1 : Fin 3) ≠ 2 by decide) * baseElt c *
            (sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹) *
          (sw (show (0 : Fin 3) ≠ 1 by decide))⁻¹ := by group
    _ = sw (show (0 : Fin 3) ≠ 1 by decide) *
          elt (n := 3) (F := K) (.difference 0 2 (by decide)) c *
          (sw (show (0 : Fin 3) ≠ 1 by decide))⁻¹ := by rw [conj_base_02]
    _ = elt (n := 3) (F := K) (.difference 1 2 (by decide)) c := by
        rw [sw_conj_elt_difference (show (0 : Fin 3) ≠ 1 by decide)]
        congr 1

private theorem conj_base_20 [CharP K 2] (c : K) :
    (sw (show (1 : Fin 3) ≠ 2 by decide) * sw (show (0 : Fin 3) ≠ 1 by decide)) *
        baseElt c *
        (sw (show (1 : Fin 3) ≠ 2 by decide) * sw (show (0 : Fin 3) ≠ 1 by decide))⁻¹ =
      elt (n := 3) (F := K) (.difference 2 0 (by decide)) c := by
  calc (sw (show (1 : Fin 3) ≠ 2 by decide) * sw (show (0 : Fin 3) ≠ 1 by decide)) *
        baseElt c *
        (sw (show (1 : Fin 3) ≠ 2 by decide) * sw (show (0 : Fin 3) ≠ 1 by decide))⁻¹
      = sw (show (1 : Fin 3) ≠ 2 by decide) *
          (sw (show (0 : Fin 3) ≠ 1 by decide) * baseElt c *
            (sw (show (0 : Fin 3) ≠ 1 by decide))⁻¹) *
          (sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹ := by group
    _ = sw (show (1 : Fin 3) ≠ 2 by decide) *
          elt (n := 3) (F := K) (.difference 1 0 (by decide)) c *
          (sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹ := by rw [conj_base_10]
    _ = elt (n := 3) (F := K) (.difference 2 0 (by decide)) c := by
        rw [sw_conj_elt_difference (show (1 : Fin 3) ≠ 2 by decide)]
        congr 1

private theorem conj_base_p01 [CharP K 2] (c : K) :
    lw 1 * baseElt c * (lw 1)⁻¹ =
      elt (n := 3) (F := K) (.positiveSum 0 1 (by decide)) c := by
  rw [baseElt]
  convert lw_conj_elt_difference_to_positiveSum (a := 0) (b := 1) (by decide) c using 2

private theorem conj_base_n01 [CharP K 2] (c : K) :
    lw 0 * baseElt c * (lw 0)⁻¹ =
      elt (n := 3) (F := K) (.negativeSum 0 1 (by decide)) c := by
  rw [baseElt]
  convert lw_conj_elt_difference_to_negativeSum (a := 0) (b := 1) (by decide) c using 2

private theorem conj_base_p02 [CharP K 2] (c : K) :
    (lw 2 * sw (show (1 : Fin 3) ≠ 2 by decide)) * baseElt c *
        (lw 2 * sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹ =
      elt (n := 3) (F := K) (.positiveSum 0 2 (by decide)) c := by
  calc (lw 2 * sw (show (1 : Fin 3) ≠ 2 by decide)) * baseElt c *
        (lw 2 * sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹
      = lw 2 * (sw (show (1 : Fin 3) ≠ 2 by decide) * baseElt c *
          (sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹) * (lw 2)⁻¹ := by group
    _ = lw 2 * elt (n := 3) (F := K) (.difference 0 2 (by decide)) c * (lw 2)⁻¹ := by
        rw [conj_base_02]
    _ = elt (n := 3) (F := K) (.positiveSum 0 2 (by decide)) c := by
        convert lw_conj_elt_difference_to_positiveSum (a := 0) (b := 2) (by decide) c
          using 2

private theorem conj_base_n02 [CharP K 2] (c : K) :
    (lw 0 * sw (show (1 : Fin 3) ≠ 2 by decide)) * baseElt c *
        (lw 0 * sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹ =
      elt (n := 3) (F := K) (.negativeSum 0 2 (by decide)) c := by
  calc (lw 0 * sw (show (1 : Fin 3) ≠ 2 by decide)) * baseElt c *
        (lw 0 * sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹
      = lw 0 * (sw (show (1 : Fin 3) ≠ 2 by decide) * baseElt c *
          (sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹) * (lw 0)⁻¹ := by group
    _ = lw 0 * elt (n := 3) (F := K) (.difference 0 2 (by decide)) c * (lw 0)⁻¹ := by
        rw [conj_base_02]
    _ = elt (n := 3) (F := K) (.negativeSum 0 2 (by decide)) c := by
        convert lw_conj_elt_difference_to_negativeSum (a := 0) (b := 2) (by decide) c
          using 2

private theorem conj_base_p12 [CharP K 2] (c : K) :
    (lw 2 * (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide))) *
        baseElt c *
        (lw 2 * (sw (show (0 : Fin 3) ≠ 1 by decide) *
          sw (show (1 : Fin 3) ≠ 2 by decide)))⁻¹ =
      elt (n := 3) (F := K) (.positiveSum 1 2 (by decide)) c := by
  calc (lw 2 * (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide))) *
        baseElt c *
        (lw 2 * (sw (show (0 : Fin 3) ≠ 1 by decide) *
          sw (show (1 : Fin 3) ≠ 2 by decide)))⁻¹
      = lw 2 * ((sw (show (0 : Fin 3) ≠ 1 by decide) *
            sw (show (1 : Fin 3) ≠ 2 by decide)) * baseElt c *
          (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹) *
          (lw 2)⁻¹ := by group
    _ = lw 2 * elt (n := 3) (F := K) (.difference 1 2 (by decide)) c * (lw 2)⁻¹ := by
        rw [conj_base_12]
    _ = elt (n := 3) (F := K) (.positiveSum 1 2 (by decide)) c := by
        convert lw_conj_elt_difference_to_positiveSum (a := 1) (b := 2) (by decide) c
          using 2

private theorem conj_base_n12 [CharP K 2] (c : K) :
    (lw 1 * (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide))) *
        baseElt c *
        (lw 1 * (sw (show (0 : Fin 3) ≠ 1 by decide) *
          sw (show (1 : Fin 3) ≠ 2 by decide)))⁻¹ =
      elt (n := 3) (F := K) (.negativeSum 1 2 (by decide)) c := by
  calc (lw 1 * (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide))) *
        baseElt c *
        (lw 1 * (sw (show (0 : Fin 3) ≠ 1 by decide) *
          sw (show (1 : Fin 3) ≠ 2 by decide)))⁻¹
      = lw 1 * ((sw (show (0 : Fin 3) ≠ 1 by decide) *
            sw (show (1 : Fin 3) ≠ 2 by decide)) * baseElt c *
          (sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹) *
          (lw 1)⁻¹ := by group
    _ = lw 1 * elt (n := 3) (F := K) (.difference 1 2 (by decide)) c * (lw 1)⁻¹ := by
        rw [conj_base_12]
    _ = elt (n := 3) (F := K) (.negativeSum 1 2 (by decide)) c := by
        convert lw_conj_elt_difference_to_negativeSum (a := 1) (b := 2) (by decide) c
          using 2

theorem exists_conj_eq_elt [CharP K 2] (r : RootSubgroupIndex 3) (hr : IsShortIndex r) :
    ∃ g : StatedSp 3 K, ∀ c : K,
      g * elt (n := 3) (F := K) (.difference 0 1 (by decide)) c * g⁻¹ = elt r c := by
  cases r with
  | positiveLong a => simp [IsShortIndex] at hr
  | negativeLong a => simp [IsShortIndex] at hr
  | difference i j hij =>
      fin_cases i <;> fin_cases j <;> try (exact absurd rfl hij)
      · refine ⟨1, fun c => ?_⟩
        rw [← baseElt_eq c, show (1 : StatedSp 3 K) * baseElt c * 1⁻¹ = baseElt c from by group,
          baseElt_eq c]
        congr 1
      · refine ⟨sw (show (1 : Fin 3) ≠ 2 by decide), fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_02 c]
        congr 1
      · refine ⟨sw (show (0 : Fin 3) ≠ 1 by decide), fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_10 c]
        congr 1
      · refine ⟨sw (show (0 : Fin 3) ≠ 1 by decide) * sw (show (1 : Fin 3) ≠ 2 by decide),
          fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_12 c]
        congr 1
      · refine ⟨sw (show (1 : Fin 3) ≠ 2 by decide) * sw (show (0 : Fin 3) ≠ 1 by decide),
          fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_20 c]
        congr 1
      · refine ⟨sw (show (0 : Fin 3) ≠ 2 by decide), fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_21 c]
        congr 1
  | positiveSum i j hij =>
      fin_cases i <;> fin_cases j <;> simp at hij
      · refine ⟨lw 1, fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_p01 c]
        congr 1
      · refine ⟨lw 2 * sw (show (1 : Fin 3) ≠ 2 by decide), fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_p02 c]
        congr 1
      · refine ⟨lw 2 * (sw (show (0 : Fin 3) ≠ 1 by decide) *
            sw (show (1 : Fin 3) ≠ 2 by decide)), fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_p12 c]
        congr 1
  | negativeSum i j hij =>
      fin_cases i <;> fin_cases j <;> simp at hij
      · refine ⟨lw 0, fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_n01 c]
        congr 1
      · refine ⟨lw 0 * sw (show (1 : Fin 3) ≠ 2 by decide), fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_n02 c]
        congr 1
      · refine ⟨lw 1 * (sw (show (0 : Fin 3) ≠ 1 by decide) *
            sw (show (1 : Fin 3) ≠ 2 by decide)), fun c => ?_⟩
        rw [← baseElt_eq c, conj_base_n12 c]
        congr 1

end CFSG.LieType.Sp6Spin

namespace CFSG.LieType.Sp6Spin

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Universal.Symplectic
  TauCeti.GLSymplecticFin

variable {K : Type} [Field K]

@[expose] noncomputable def nShort : StatedSp 3 K :=
  elt (n := 3) (F := K) (.positiveSum 0 2 (by decide)) 1 *
    elt (n := 3) (F := K) (.negativeSum 0 2 (by decide)) 1 *
    elt (n := 3) (F := K) (.positiveSum 0 2 (by decide)) 1

@[expose] def Pmat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  Matrix.of fun a b =>
    if a = .inl 0 then if b = .inr 2 then 1 else 0
    else if a = .inl 2 then if b = .inr 0 then 1 else 0
    else if a = .inr 0 then if b = .inl 2 then 1 else 0
    else if a = .inr 2 then if b = .inl 0 then 1 else 0
    else if a = .inl 1 then if b = .inl 1 then 1 else 0
    else if a = .inr 1 then if b = .inr 1 then 1 else 0
    else 0

theorem mat_nShort [CharP K 2] : mat 3 K (nShort (K := K)) = Pmat (K := K) := by
  simp only [nShort, map_mul, mat_elt, Pmat]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [E, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
      CharTwo.add_self_eq_zero]

theorem Pmat_conj_positiveLong_two [CharP K 2] (c : K) :
    Pmat (K := K) * ((1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) +
        c • E (n := 3) (F := K) (.positiveLong 2)) * Pmat =
      (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) +
        c • E (n := 3) (F := K) (.negativeLong 0) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Pmat, E, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
      CharTwo.add_self_eq_zero]

private theorem nShort_inv [CharP K 2] : (nShort (K := K))⁻¹ = nShort (K := K) := by
  have hpos : elt (n := 3) (F := K) (.positiveSum 0 2 (by decide)) (1 : K) *
      elt (n := 3) (F := K) (.positiveSum 0 2 (by decide)) 1 = 1 := by
    rw [← elt_add, CharTwo.add_self_eq_zero, elt_zero]
  have hneg : elt (n := 3) (F := K) (.negativeSum 0 2 (by decide)) (1 : K) *
      elt (n := 3) (F := K) (.negativeSum 0 2 (by decide)) 1 = 1 := by
    rw [← elt_add, CharTwo.add_self_eq_zero, elt_zero]
  rw [nShort]
  simp only [_root_.mul_inv_rev]
  rw [show (elt (n := 3) (F := K) (.positiveSum 0 2 (by decide)) (1 : K))⁻¹ =
        elt (n := 3) (F := K) (.positiveSum 0 2 (by decide)) 1 from
      inv_eq_of_mul_eq_one_right hpos,
    show (elt (n := 3) (F := K) (.negativeSum 0 2 (by decide)) (1 : K))⁻¹ =
        elt (n := 3) (F := K) (.negativeSum 0 2 (by decide)) 1 from
      inv_eq_of_mul_eq_one_right hneg]
  group

theorem nShort_conj_positiveLong_two [CharP K 2] (c : K) :
    nShort * elt (n := 3) (F := K) (.positiveLong 2) c * (nShort (K := K))⁻¹ =
      elt (n := 3) (F := K) (.negativeLong 0) c := by
  rw [nShort_inv]
  refine mat_injective ?_
  rw [map_mul, map_mul, mat_nShort, mat_elt, mat_elt]
  exact Pmat_conj_positiveLong_two c

end CFSG.LieType.Sp6Spin

namespace CFSG.LieType.Sp6Spin

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Universal.Symplectic
  TauCeti.GLSymplecticFin

variable {K : Type} [Field K]

private theorem eq_top_of_elt_mem (H : Subgroup (StatedSp 3 K))
    (h : ∀ (r : RootSubgroupIndex 3) (c : K), elt r c ∈ H) : H = ⊤ := by
  have hT : H.comap (equivStatedSp 3 K).toMonoidHom = ⊤ :=
    eq_top_of_root_subgroups _ fun r c => h r c.toAdd
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (equivStatedSp 3 K).surjective x
  have hy : y ∈ H.comap (equivStatedSp 3 K).toMonoidHom := by
    rw [hT]
    exact Subgroup.mem_top y
  exact hy

theorem closure_short_long_eq_top [CharP K 2] :
    Subgroup.closure ({g | ∃ r : RootSubgroupIndex 3, IsShortIndex r ∧ ∃ c : K, elt r c = g} ∪
      Set.range (elt (n := 3) (F := K) (.positiveLong 2))) = ⊤ := by
  classical
  set H := Subgroup.closure ({g | ∃ r : RootSubgroupIndex 3,
    IsShortIndex r ∧ ∃ c : K, elt r c = g} ∪
      Set.range (elt (n := 3) (F := K) (.positiveLong 2))) with hH
  have hshort : ∀ (r : RootSubgroupIndex 3), IsShortIndex r → ∀ c : K, elt r c ∈ H := by
    intro r hr c
    exact Subgroup.subset_closure (Set.mem_union_left _ ⟨r, hr, c, rfl⟩)
  have hlong2 : ∀ c : K, elt (n := 3) (F := K) (.positiveLong 2) c ∈ H := by
    intro c
    exact Subgroup.subset_closure (Set.mem_union_right _ ⟨c, rfl⟩)
  have hsw : ∀ {i j : Fin 3} (hij : i ≠ j), sw (F := K) hij ∈ H := by
    intro i j hij
    rw [sw_eq (F := K) hij]
    exact H.mul_mem (H.mul_mem
      (hshort _ (by simp [IsShortIndex]) 1)
      (hshort _ (by simp [IsShortIndex]) (-1)))
      (hshort _ (by simp [IsShortIndex]) 1)
  have hpos : ∀ (a : Fin 3) (c : K), elt (n := 3) (F := K) (.positiveLong a) c ∈ H := by
    intro a c
    fin_cases a
    · have hx : sw (show (0 : Fin 3) ≠ 2 by decide) *
          elt (n := 3) (F := K) (.positiveLong 2) c *
          (sw (show (0 : Fin 3) ≠ 2 by decide))⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (hsw (show (0 : Fin 3) ≠ 2 by decide)) (hlong2 c))
          (H.inv_mem (hsw (show (0 : Fin 3) ≠ 2 by decide)))
      simpa [sw_conj_elt_positiveLong (show (0 : Fin 3) ≠ 2 by decide) 2 c,
        show (Equiv.swap (0 : Fin 3) 2) 2 = 0 from by decide] using hx
    · have hx : sw (show (1 : Fin 3) ≠ 2 by decide) *
          elt (n := 3) (F := K) (.positiveLong 2) c *
          (sw (show (1 : Fin 3) ≠ 2 by decide))⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (hsw (show (1 : Fin 3) ≠ 2 by decide)) (hlong2 c))
          (H.inv_mem (hsw (show (1 : Fin 3) ≠ 2 by decide)))
      simpa [sw_conj_elt_positiveLong (show (1 : Fin 3) ≠ 2 by decide) 2 c,
        show (Equiv.swap (1 : Fin 3) 2) 2 = 1 from by decide] using hx
    · exact hlong2 c
  have hnShort_mem : nShort (K := K) ∈ H := by
    rw [nShort]
    exact H.mul_mem (H.mul_mem
      (hshort _ (by simp [IsShortIndex]) 1)
      (hshort _ (by simp [IsShortIndex]) 1))
      (hshort _ (by simp [IsShortIndex]) 1)
  have hneg0 : ∀ c : K, elt (n := 3) (F := K) (.negativeLong 0) c ∈ H := by
    intro c
    have hx : nShort (K := K) * elt (n := 3) (F := K) (.positiveLong 2) c *
        (nShort (K := K))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hnShort_mem (hlong2 c)) (H.inv_mem hnShort_mem)
    simpa [nShort_conj_positiveLong_two c] using hx
  have hneg : ∀ (a : Fin 3) (c : K), elt (n := 3) (F := K) (.negativeLong a) c ∈ H := by
    intro a c
    fin_cases a
    · exact hneg0 c
    · have hx : sw (show (0 : Fin 3) ≠ 1 by decide) *
          elt (n := 3) (F := K) (.negativeLong 0) c *
          (sw (show (0 : Fin 3) ≠ 1 by decide))⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (hsw (show (0 : Fin 3) ≠ 1 by decide)) (hneg0 c))
          (H.inv_mem (hsw (show (0 : Fin 3) ≠ 1 by decide)))
      simpa [sw_conj_elt_negativeLong (show (0 : Fin 3) ≠ 1 by decide) 0 c,
        show (Equiv.swap (0 : Fin 3) 1) 0 = 1 from by decide] using hx
    · have hx : sw (show (0 : Fin 3) ≠ 2 by decide) *
          elt (n := 3) (F := K) (.negativeLong 0) c *
          (sw (show (0 : Fin 3) ≠ 2 by decide))⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (hsw (show (0 : Fin 3) ≠ 2 by decide)) (hneg0 c))
          (H.inv_mem (hsw (show (0 : Fin 3) ≠ 2 by decide)))
      simpa [sw_conj_elt_negativeLong (show (0 : Fin 3) ≠ 2 by decide) 0 c,
        show (Equiv.swap (0 : Fin 3) 2) 0 = 2 from by decide] using hx
  have hall : ∀ (r : RootSubgroupIndex 3) (c : K), elt r c ∈ H := by
    intro r c
    cases r with
    | positiveLong a => exact hpos a c
    | negativeLong a => exact hneg a c
    | difference i j hij => exact hshort _ (by simp [IsShortIndex]) c
    | positiveSum i j hij => exact hshort _ (by simp [IsShortIndex]) c
    | negativeSum i j hij => exact hshort _ (by simp [IsShortIndex]) c
  exact eq_top_of_elt_mem H hall

end CFSG.LieType.Sp6Spin
