module

public import CFSG.ClassicalGroups.Symplectic.PSp45.Model

public section

namespace CFSG.ClassicalGroups.Symplectic.PSp45

open CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt elt_add elt_zero mat mat_injective mat_elt E)
open TauCeti.GLSymplecticFin (RootSubgroupIndex eq_top_of_adjacent_of_long differenceShortRootUnit
  positiveLongRootTransvectionUnit negativeLongRootTransvectionUnit differenceShortRootHom_apply
  positiveLongRootTransvectionHom_apply negativeLongRootTransvectionHom_apply)
open scoped Matrix

private theorem mat_psp45Gen (i : Fin 8) : mat 2 (ZMod 5) (psp45Gen i) = genMat i :=
  mat_ofSymplecticMat _ _

private theorem psp45Gen_one : psp45Gen 1 = elt (.negativeLong (1 : Fin 2)) (1 : ZMod 5) := by
  apply mat_injective (n := 2) (F := ZMod 5)
  rw [mat_psp45Gen, mat_elt]
  decide +kernel

private theorem psp45Gen_three :
    psp45Gen 3 = elt (.difference (1 : Fin 2) 0 (by decide)) (3 : ZMod 5) := by
  apply mat_injective (n := 2) (F := ZMod 5)
  rw [mat_psp45Gen, mat_elt]
  decide +kernel

private theorem psp45Gen_seven_pow_four : psp45Gen 7 ^ 4 = 1 := by
  apply mat_injective (n := 2) (F := ZMod 5)
  rw [map_pow, map_one, mat_psp45Gen]
  decide +kernel

private theorem psp45Gen_seven_inv : (psp45Gen 7)⁻¹ = psp45Gen 7 ^ 3 := by
  have h : psp45Gen 7 * psp45Gen 7 ^ 3 = 1 := by
    rw [← pow_succ']
    norm_num
    exact psp45Gen_seven_pow_four
  exact inv_eq_of_mul_eq_one_right h

private theorem psp45Gen_six_pow_four : psp45Gen 6 ^ 4 = 1 := by
  apply mat_injective (n := 2) (F := ZMod 5)
  rw [map_pow, map_one, mat_psp45Gen]
  decide +kernel

private theorem psp45Gen_six_inv : (psp45Gen 6)⁻¹ = psp45Gen 6 ^ 3 := by
  have h : psp45Gen 6 * psp45Gen 6 ^ 3 = 1 := by
    rw [← pow_succ']
    norm_num
    exact psp45Gen_six_pow_four
  exact inv_eq_of_mul_eq_one_right h

private theorem conj_negLong_one :
    psp45Gen 7 * elt (.negativeLong (1 : Fin 2)) (1 : ZMod 5) * (psp45Gen 7)⁻¹ =
      elt (.positiveLong (1 : Fin 2)) (-1 : ZMod 5) := by
  rw [psp45Gen_seven_inv]
  apply mat_injective (n := 2) (F := ZMod 5)
  rw [map_mul, map_mul, map_pow, mat_psp45Gen, mat_elt, mat_elt]
  decide +kernel

private theorem conj_difference :
    psp45Gen 6 * elt (.difference (1 : Fin 2) 0 (by decide)) (3 : ZMod 5) * (psp45Gen 6)⁻¹ =
      elt (.difference (0 : Fin 2) 1 (by decide)) (2 : ZMod 5) := by
  rw [psp45Gen_six_inv]
  apply mat_injective (n := 2) (F := ZMod 5)
  rw [map_mul, map_mul, map_pow, mat_psp45Gen, mat_elt, mat_elt]
  decide +kernel

private theorem elt_mem_of_ne_zero {n : ℕ} (H : Subgroup (StatedSp n (ZMod 5)))
    (r : RootSubgroupIndex n) {a : ZMod 5} (ha : a ≠ 0) (h : elt r a ∈ H) (c : ZMod 5) :
    elt r c ∈ H := by
  have hnat : ∀ k : ℕ, elt r ((k : ZMod 5) * a) ∈ H := by
    intro k
    induction k with
    | zero => simpa [elt_zero] using H.one_mem
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, elt_add]
      exact H.mul_mem ih h
  have hc : c = ((ZMod.val (c * a⁻¹) : ℕ) : ZMod 5) * a := by
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  rw [hc]
  exact hnat _

private theorem equivStatedSp_difference_p45 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (c : ZMod 5) :
    equivStatedSp n (ZMod 5) (differenceShortRootUnit hij c) = elt (.difference i j hij) c := by
  rw [elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]

private theorem equivStatedSp_positiveLong_p45 {n : ℕ} (i : Fin n) (c : ZMod 5) :
    equivStatedSp n (ZMod 5) (positiveLongRootTransvectionUnit i c) = elt (.positiveLong i) c := by
  rw [elt, RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
    toAdd_ofAdd]

private theorem equivStatedSp_negativeLong_p45 {n : ℕ} (i : Fin n) (c : ZMod 5) :
    equivStatedSp n (ZMod 5) (negativeLongRootTransvectionUnit i c) = elt (.negativeLong i) c := by
  rw [elt, RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
    toAdd_ofAdd]

theorem closure_psp45Gen : Subgroup.closure (Set.range psp45Gen) = ⊤ := by
  set H := Subgroup.closure (Set.range psp45Gen) with hH
  have hg (i : Fin 8) : psp45Gen i ∈ H := Subgroup.subset_closure ⟨i, rfl⟩
  have hneg : elt (.negativeLong (1 : Fin 2)) (1 : ZMod 5) ∈ H := by
    rw [← psp45Gen_one]
    exact hg 1
  have hdiff : elt (.difference (1 : Fin 2) 0 (by decide)) (3 : ZMod 5) ∈ H := by
    rw [← psp45Gen_three]
    exact hg 3
  have hpos' : elt (.positiveLong (1 : Fin 2)) (-1 : ZMod 5) ∈ H := by
    rw [← conj_negLong_one]
    exact H.mul_mem (H.mul_mem (hg 7) hneg) (H.inv_mem (hg 7))
  have hdiff' : elt (.difference (0 : Fin 2) 1 (by decide)) (2 : ZMod 5) ∈ H := by
    rw [← conj_difference]
    exact H.mul_mem (H.mul_mem (hg 6) hdiff) (H.inv_mem (hg 6))
  have hpos : ∀ c : ZMod 5, elt (.positiveLong (1 : Fin 2)) c ∈ H :=
    elt_mem_of_ne_zero H _ (by decide) hpos'
  have hnegall : ∀ c : ZMod 5, elt (.negativeLong (1 : Fin 2)) c ∈ H :=
    elt_mem_of_ne_zero H _ (by decide) hneg
  have hdiff10 : ∀ c : ZMod 5, elt (.difference (1 : Fin 2) 0 (by decide)) c ∈ H :=
    elt_mem_of_ne_zero H _ (by decide) hdiff
  have hdiff01 : ∀ c : ZMod 5, elt (.difference (0 : Fin 2) 1 (by decide)) c ∈ H :=
    elt_mem_of_ne_zero H _ (by decide) hdiff'
  have hT : H.comap (equivStatedSp 2 (ZMod 5)).toMonoidHom = ⊤ := by
    refine eq_top_of_adjacent_of_long _ 1 ?_ ?_ ?_
    · intro i j hij c _
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_difference_p45]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hdiff01 c
      · exact hdiff10 c
      · exact absurd rfl hij
    · intro c
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_positiveLong_p45]
      exact hpos c
    · intro c
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_negativeLong_p45]
      exact hnegall c
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (equivStatedSp 2 (ZMod 5)).surjective x
  have hy : y ∈ H.comap (equivStatedSp 2 (ZMod 5)).toMonoidHom := by
    rw [hT]
    exact Subgroup.mem_top y
  exact hy

theorem closure_psp45GenP : Subgroup.closure (Set.range psp45GenP) = ⊤ := by
  set N := (StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5)) with hN
  have hcomp : psp45GenP = (QuotientGroup.mk' N) ∘ psp45Gen := by
    funext i
    rw [psp45GenP, Function.comp_apply, QuotientGroup.mk'_apply]
  rw [hcomp, Set.range_comp, ← MonoidHom.map_closure, closure_psp45Gen,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

end CFSG.ClassicalGroups.Symplectic.PSp45
