module

public import CFSG.GH74.GLS.Stage2.Final.ModelSpData
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.GH74.GLS.IVK.Proofs2.Sp48O2

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelH2

open CFSG.GH74.L5U5 CFSG.LieType.Steinberg
open scoped MatrixGroups

section SL2

theorem isQuasisimple_of_isPerfect_of_isSimpleGroup {Q : Type*} [Group Q] (hp : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : CFSG.IsQuasisimple Q := by
  refine ⟨hp, hs, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨h⟩⟩
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative _ ‹_›

theorem isQuasisimple_sl2 {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple SL(2, K) :=
  isQuasisimple_of_isPerfect_of_isSimpleGroup (CFSG.ClassicalInvolution.sl2_isPerfect h4)
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)

theorem isQuasisimple_of_equiv_sl2 {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K)
    {G : Type*} [Group G] (e : SL(2, K) ≃* G) : CFSG.IsQuasisimple G :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_sl2 h4)

theorem isPGroup_two_center_of_equiv_sl2 {K : Type*} [Field K] {G : Type*} [Group G]
    (e : SL(2, K) ≃* G) : IsPGroup 2 (Subgroup.center G) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨z, hz⟩ := e.surjective (x : G)
  have hzc : z ∈ Subgroup.center SL(2, K) := by
    have h := (CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e.symm (x : G)).1 x.2
    rwa [← hz, e.symm_apply_apply] at h
  have hz2 : z ^ 2 = 1 := by
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff z).1 hzc with rfl | rfl
    · exact one_pow 2
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_two]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, ← hz, ← map_pow, hz2, map_one]

end SL2

section NegOne

variable {F : Type} [Field F]

theorem neg_one_ne_one_gl2 (h2 : (2 : F) ≠ 0) : (-1 : GL (Fin 2) F) ≠ 1 :=
  CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2Plane.neg_ne_one_GL h2

theorem two_dvd_natCard_H2 (M : ModelData F) (h2 : (2 : F) ≠ 0) : 2 ∣ Nat.card ↥M.H2 := by
  have hord : orderOf (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      exact neg_one_sq
    · intro h
      exact neg_one_ne_one_gl2 h2 (congrArg Subtype.val h)
  have hdvd := orderOf_dvd_natCard (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2)
  rwa [hord] at hdvd

end NegOne

section Lin

variable (F : Type) [Field F]

theorem h2_quasisimple_lin [Finite F] (h5 : 5 ≤ Nat.card F) :
    CFSG.IsQuasisimple ↥(ModelData.lin F).H2 :=
  isQuasisimple_of_equiv_sl2 (by omega) (lin_sl2_equiv_H2 F)

theorem h2_center_two_lin : IsPGroup 2 ↥(Subgroup.center ↥(ModelData.lin F).H2) :=
  isPGroup_two_center_of_equiv_sl2 (lin_sl2_equiv_H2 F)

theorem h2_even_lin (h2 : (2 : F) ≠ 0) : 2 ∣ Nat.card ↥(ModelData.lin F).H2 :=
  two_dvd_natCard_H2 _ h2

end Lin

section Uni

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem h2_quasisimple_uni (hF : Nat.card F = (p ^ f) ^ 2) (h5 : 5 ≤ p ^ f) :
    CFSG.IsQuasisimple ↥(ModelData.uni hF).H2 := by
  obtain ⟨e⟩ := nonempty_sl2_equiv_uni_H2 hF
  exact isQuasisimple_of_equiv_sl2 (by rw [card_fixedSubfield hF]; omega) e

theorem h2_center_two_uni (hF : Nat.card F = (p ^ f) ^ 2) :
    IsPGroup 2 ↥(Subgroup.center ↥(ModelData.uni hF).H2) := by
  obtain ⟨e⟩ := nonempty_sl2_equiv_uni_H2 hF
  exact isPGroup_two_center_of_equiv_sl2 e

theorem h2_even_uni (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    2 ∣ Nat.card ↥(ModelData.uni hF).H2 := by
  refine two_dvd_natCard_H2 _ fun h => hp2 ?_
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h'

end Uni

section Sp

variable (F : Type) [Field F]

theorem h2_quasisimple_sp [Finite F] (h5 : 5 ≤ Nat.card F) :
    CFSG.IsQuasisimple ↥(ModelData.sp F).H2 :=
  isQuasisimple_of_equiv_sl2 (by omega) (ModelSp.sp_sl2_equiv_H2 F)

theorem h2_center_two_sp : IsPGroup 2 ↥(Subgroup.center ↥(ModelData.sp F).H2) :=
  isPGroup_two_center_of_equiv_sl2 (ModelSp.sp_sl2_equiv_H2 F)

theorem h2_even_sp (h2 : (2 : F) ≠ 0) : 2 ∣ Nat.card ↥(ModelData.sp F).H2 :=
  two_dvd_natCard_H2 _ h2

end Sp

end CFSG.GH74.GLS.Stage2.Final.ModelH2
