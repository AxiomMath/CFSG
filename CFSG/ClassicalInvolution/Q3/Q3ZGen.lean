module

public import CFSG.ClassicalInvolution.Q3.Q3ZMat

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt elt_add elt_zero)
open TauCeti.GLSymplecticFin (RootSubgroupIndex eq_top_of_adjacent_of_long
  differenceShortRootUnit differenceShortRootHom_apply positiveLongRootTransvectionUnit
  positiveLongRootTransvectionHom_apply negativeLongRootTransvectionUnit
  negativeLongRootTransvectionHom_apply)

private theorem elt_mem_of_one {n : ℕ} (H : Subgroup (StatedSp n (ZMod 3)))
    (r : RootSubgroupIndex n) (h : elt r (1 : ZMod 3) ∈ H) (c : ZMod 3) : elt r c ∈ H := by
  have hnat : ∀ k : ℕ, elt r (k : ZMod 3) ∈ H := by
    intro k
    induction k with
    | zero => simp [elt_zero]
    | succ k ih => rw [Nat.cast_succ, elt_add]; exact H.mul_mem ih h
  rw [← ZMod.natCast_zmod_val c]
  exact hnat _

private theorem equivStatedSp_difference {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : ZMod 3) :
    equivStatedSp n (ZMod 3) (differenceShortRootUnit hij c) = elt (.difference i j hij) c := by
  rw [elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]

private theorem equivStatedSp_positiveLong {n : ℕ} (i : Fin n) (c : ZMod 3) :
    equivStatedSp n (ZMod 3) (positiveLongRootTransvectionUnit i c) = elt (.positiveLong i) c := by
  rw [elt, RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
    toAdd_ofAdd]

private theorem equivStatedSp_negativeLong {n : ℕ} (i : Fin n) (c : ZMod 3) :
    equivStatedSp n (ZMod 3) (negativeLongRootTransvectionUnit i c) = elt (.negativeLong i) c := by
  rw [elt, RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
    toAdd_ofAdd]

theorem v6_closure_eq_top : Subgroup.closure (Set.range v6Mat) = ⊤ := by
  set H := Subgroup.closure (Set.range v6Mat) with hH
  have hgen : ∀ k : Fin 12, elt (v6Root k) (1 : ZMod 3) ∈ H := fun k =>
    Subgroup.subset_closure ⟨k, rfl⟩
  have hT : H.comap (equivStatedSp 3 (ZMod 3)).toMonoidHom = ⊤ := by
    refine eq_top_of_adjacent_of_long _ 2 ?_ ?_ ?_
    · intro i j hij c hadj
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_difference]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact elt_mem_of_one H _ (hgen 4) c
      · exact absurd hadj (by decide)
      · exact elt_mem_of_one H _ (hgen 5) c
      · exact absurd rfl hij
      · exact elt_mem_of_one H _ (hgen 9) c
      · exact absurd hadj (by decide)
      · exact elt_mem_of_one H _ (hgen 10) c
      · exact absurd rfl hij
    · intro c
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_positiveLong]
      exact elt_mem_of_one H _ (hgen 2) c
    · intro c
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, equivStatedSp_negativeLong]
      exact elt_mem_of_one H _ (hgen 3) c
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (equivStatedSp 3 (ZMod 3)).surjective x
  have hy : y ∈ H.comap (equivStatedSp 3 (ZMod 3)).toMonoidHom := by
    rw [hT]
    exact Subgroup.mem_top y
  exact hy

end CFSG.ClassicalInvolution.Q3.Q3Z
