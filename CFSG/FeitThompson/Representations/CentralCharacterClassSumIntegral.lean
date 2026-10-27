module

public import CFSG.FeitThompson.Representations.ClassSumsIntegerStructureConstants
import Mathlib.Analysis.Complex.Polynomial.Basic
import CFSG.FeitThompson.Representations.StableModuleAlgebraicIntegrality
public import CFSG.FeitThompson.Representations.CentralCharacterHomomorphism
public import Mathlib.Basic.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

section ClassSum

variable {k : Type*} [CommSemiring k] {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem classSum_mk (x : G) : classSum k (ConjClasses.mk x) = conjClassSum k x := by
  refine MonoidAlgebra.coeff_inj.1 ?_
  ext g
  rw [coeff_classSum, conjClassSum_def, MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  rw [Finset.sum_ite_eq' (conjClassFinset x) g (fun _ => (1 : k))]
  simp only [ConjClasses.mk_eq_mk_iff_isConj, mem_conjClassFinset]
  exact if_congr isConj_comm rfl rfl

theorem centerClassSum_mk (k : Type*) [CommRing k] (x : G) :
    centerClassSum k (ConjClasses.mk x) = ⟨conjClassSum k x, conjClassSum_mem_center k x⟩ :=
  Subtype.ext (by rw [coe_centerClassSum, classSum_mk])

end ClassSum

namespace Representation

open Module

section Fintype

variable {G V : Type*} [Group G] [Fintype G] [DecidableEq G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : _root_.Representation ℂ G V) [ρ.IsIrreducible]

noncomputable def centralCharacterClassSum (M : ConjClasses G) : ℂ :=
  centralCharacter ρ (centerClassSum ℂ M)

@[simp]
theorem centralCharacterClassSum_one : centralCharacterClassSum ρ (1 : ConjClasses G) = 1 := by
  rw [centralCharacterClassSum, show centerClassSum ℂ (1 : ConjClasses G) = 1 from
    Subtype.ext (by simp), centralCharacter_one]

theorem centralCharacterClassSum_mk (x : G) :
    centralCharacterClassSum ρ (ConjClasses.mk x)
      = ((conjClassFinset x).card : ℂ) * ρ.character x / ρ.character 1 := by
  rw [centralCharacterClassSum, centerClassSum_mk, centralCharacter_conjClassSum]

theorem centralCharacterClassSum_mul (K M : ConjClasses G) :
    centralCharacterClassSum ρ K * centralCharacterClassSum ρ M
      = ∑ N, (classStructureConstant K M N : ℂ) * centralCharacterClassSum ρ N := by
  have hmul : centerClassSum ℂ K * centerClassSum ℂ M
      = ∑ N, (classStructureConstant K M N : ℂ) • centerClassSum ℂ N := by
    refine Subtype.ext ?_
    push_cast [coe_centerClassSum]
    simpa using classSum_mul_classSum (k := ℂ) K M
  rw [centralCharacterClassSum, centralCharacterClassSum, ← map_mul, hmul, map_sum]
  simp [centralCharacterClassSum, smul_eq_mul]

theorem mul_mem_span_range_centralCharacterClassSum (K : ConjClasses G) (y : ℂ)
    (hy : y ∈ Submodule.span ℤ (Set.range (centralCharacterClassSum ρ))) :
    centralCharacterClassSum ρ K * y ∈
      Submodule.span ℤ (Set.range (centralCharacterClassSum ρ)) := by
  refine Submodule.span_induction
    (p := fun y _ => centralCharacterClassSum ρ K * y ∈
      Submodule.span ℤ (Set.range (centralCharacterClassSum ρ))) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨M, rfl⟩
    rw [centralCharacterClassSum_mul]
    refine Submodule.sum_mem _ fun N _ => ?_
    rw [← nsmul_eq_mul]
    exact nsmul_mem (Submodule.subset_span (Set.mem_range_self N)) _
  · rw [mul_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    rw [mul_add]
    exact add_mem ha hb
  · intro n a _ ha
    rw [mul_smul_comm]
    exact zsmul_mem ha n

theorem isIntegral_centralCharacterClassSum (K : ConjClasses G) :
    IsIntegral ℤ (centralCharacterClassSum ρ K) :=
  isIntegral_int_of_mul_mem_span (centralCharacterClassSum ρ)
    ⟨1, by rw [centralCharacterClassSum_one]; exact one_ne_zero⟩ _
    (mul_mem_span_range_centralCharacterClassSum ρ K)

end Fintype

section Finite

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : _root_.Representation ℂ G V) [ρ.IsIrreducible]

theorem isIntegral_card_conjClass_mul_character_div (x : G) :
    IsIntegral ℤ (((conjClassFinset x).card : ℂ) * ρ.character x / ρ.character 1) := by
  have := Fintype.ofFinite G
  classical
  rw [← centralCharacterClassSum_mk ρ x]
  exact isIntegral_centralCharacterClassSum ρ _

theorem exists_monic_natDegree_pos_conjClass_character (x : G) :
    ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧
      aeval (((conjClassFinset x).card : ℂ) * ρ.character x / ρ.character 1) p = 0 :=
  (isIntegral_int_iff_exists_monic_natDegree_pos _).1
    (isIntegral_card_conjClass_mul_character_div ρ x)

end Finite

end Representation

end CFSG.FeitThompson
