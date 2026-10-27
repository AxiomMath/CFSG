module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MonoidAlgebra

section Rep

variable {G : Type*} [Group G]

noncomputable def classRep (M : ConjClasses G) : G := M.out

@[simp]
theorem mk_classRep (M : ConjClasses G) : ConjClasses.mk (classRep M) = M := Quotient.out_eq M

theorem isConj_classRep_mk (g : G) : IsConj (classRep (ConjClasses.mk g)) g :=
  ConjClasses.mk_eq_mk_iff_isConj.1 (mk_classRep _)

theorem mk_conj (c g : G) : ConjClasses.mk (c * g * c⁻¹) = ConjClasses.mk g :=
  ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨c⁻¹, by group⟩)

end Rep

section Center

variable {k : Type*} [CommSemiring k] {G : Type*} [Group G]

theorem coeff_mul_comm_of_mem_center {x : MonoidAlgebra k G}
    (hx : x ∈ Subalgebra.center k (MonoidAlgebra k G)) (a b : G) :
    x.coeff (a * b) = x.coeff (b * a) := by
  have hc := (Subalgebra.mem_center_iff.1 hx (MonoidAlgebra.single a (1 : k))).symm
  have h2 := congrArg (fun z => MonoidAlgebra.coeff z (a * b * a)) hc
  simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
    mul_one, one_mul] at h2
  rwa [show a⁻¹ * (a * b * a) = b * a by group, show a * b * a * a⁻¹ = a * b by group] at h2

theorem coeff_eq_of_isConj_of_mem_center {x : MonoidAlgebra k G}
    (hx : x ∈ Subalgebra.center k (MonoidAlgebra k G)) {g g' : G} (h : IsConj g g') :
    x.coeff g = x.coeff g' := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [show c * g * c⁻¹ = c * (g * c⁻¹) by group, coeff_mul_comm_of_mem_center hx]
  congr 1
  group

end Center

section ClassSum

variable (k : Type*) [CommSemiring k] {G : Type*} [Group G] [Fintype G] [DecidableEq G]

noncomputable def classSum (K : ConjClasses G) : MonoidAlgebra k G :=
  ∑ g ∈ K.carrier.toFinset, of k G g

variable {k}

theorem coeff_classSum (K : ConjClasses G) (g : G) :
    (classSum k K).coeff g = if ConjClasses.mk g = K then 1 else 0 := by
  rw [classSum, MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  rw [Finset.sum_ite_eq' K.carrier.toFinset g (fun _ => (1 : k))]
  simp [ConjClasses.mem_carrier_iff_mk_eq]

theorem coeff_sum_smul_classSum (c : ConjClasses G → k) (g : G) :
    (∑ M, c M • classSum k M).coeff g = c (ConjClasses.mk g) := by
  rw [MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    coeff_classSum, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

@[simp]
theorem classSum_one : classSum k (1 : ConjClasses G) = 1 := by
  refine MonoidAlgebra.coeff_inj.1 ?_
  ext g
  rw [coeff_classSum, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have h : (ConjClasses.mk g = (1 : ConjClasses G)) ↔ (1 : G) = g := by
    rw [show (1 : ConjClasses G) = ConjClasses.mk 1 from rfl, ConjClasses.mk_eq_mk_iff_isConj,
      isConj_one_left]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  simp only [h]

theorem classSum_mem_center (K : ConjClasses G) :
    classSum k K ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_on with
  | of g =>
      refine MonoidAlgebra.coeff_inj.1 ?_
      ext h
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply,
        MonoidAlgebra.coeff_single_mul_apply, coeff_classSum, coeff_classSum]
      rw [show ConjClasses.mk (g⁻¹ * h) = ConjClasses.mk (h * g⁻¹) from
        ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨h, by group⟩)]
      ring
  | add u v hu hv => rw [add_mul, mul_add, hu, hv]
  | smul r u hu => rw [smul_mul_assoc, mul_smul_comm, hu]

theorem eq_sum_smul_classSum {x : MonoidAlgebra k G}
    (hx : x ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    ∑ M, x.coeff (classRep M) • classSum k M = x := by
  refine MonoidAlgebra.coeff_inj.1 ?_
  ext g
  rw [coeff_sum_smul_classSum]
  exact coeff_eq_of_isConj_of_mem_center hx (isConj_classRep_mk g)

end ClassSum

section StructureConstants

variable {k : Type*} [CommSemiring k] {G : Type*} [Group G] [Fintype G] [DecidableEq G]

def classProdPairs (K L : ConjClasses G) (z : G) : Finset (G × G) :=
  {p ∈ K.carrier.toFinset ×ˢ L.carrier.toFinset | p.1 * p.2 = z}

theorem mem_classProdPairs {K L : ConjClasses G} {z : G} {p : G × G} :
    p ∈ classProdPairs K L z ↔
      ConjClasses.mk p.1 = K ∧ ConjClasses.mk p.2 = L ∧ p.1 * p.2 = z := by
  simp [classProdPairs, ConjClasses.mem_carrier_iff_mk_eq, and_assoc]

theorem card_classProdPairs_conj (K L : ConjClasses G) (z c : G) :
    (classProdPairs K L (c * z * c⁻¹)).card = (classProdPairs K L z).card := by
  refine Finset.card_nbij' (i := fun p => (c⁻¹ * p.1 * c, c⁻¹ * p.2 * c))
    (j := fun p => (c * p.1 * c⁻¹, c * p.2 * c⁻¹)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, mem_classProdPairs] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · rw [show c⁻¹ * p.1 * c = c⁻¹ * p.1 * c⁻¹⁻¹ by group, mk_conj, h1]
    · rw [show c⁻¹ * p.2 * c = c⁻¹ * p.2 * c⁻¹⁻¹ by group, mk_conj, h2]
    · rw [show c⁻¹ * p.1 * c * (c⁻¹ * p.2 * c) = c⁻¹ * (p.1 * p.2) * c by group, h3]; group
  · intro p hp
    simp only [Finset.mem_coe, mem_classProdPairs] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by rw [mk_conj, h1], by rw [mk_conj, h2], ?_⟩
    rw [show c * p.1 * c⁻¹ * (c * p.2 * c⁻¹) = c * (p.1 * p.2) * c⁻¹ by group, h3]
  · intro p _; refine Prod.ext ?_ ?_ <;> group
  · intro p _; refine Prod.ext ?_ ?_ <;> group

theorem card_classProdPairs_eq_of_isConj (K L : ConjClasses G) {z z' : G} (h : IsConj z z') :
    (classProdPairs K L z).card = (classProdPairs K L z').card := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (card_classProdPairs_conj K L z c).symm

noncomputable def classStructureConstant (K L M : ConjClasses G) : ℕ :=
  (classProdPairs K L (classRep M)).card

theorem classStructureConstant_eq_card (K L : ConjClasses G) (z : G) :
    classStructureConstant K L (ConjClasses.mk z) = (classProdPairs K L z).card :=
  card_classProdPairs_eq_of_isConj K L (isConj_classRep_mk z)

theorem coeff_classSum_mul_classSum (K L : ConjClasses G) (g : G) :
    (classSum k K * classSum k L).coeff g = ((classProdPairs K L g).card : k) := by
  rw [classSum, classSum, Finset.sum_mul_sum, ← Finset.sum_product', MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
    mul_one, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_boole (p := fun p : G × G => p.1 * p.2 = g)]
  rfl

theorem classSum_mul_classSum (K L : ConjClasses G) :
    classSum k K * classSum k L
      = ∑ M, (classStructureConstant K L M : k) • classSum k M := by
  refine MonoidAlgebra.coeff_inj.1 ?_
  ext g
  rw [coeff_classSum_mul_classSum, coeff_sum_smul_classSum, classStructureConstant_eq_card]

end StructureConstants

section Basis

variable (k : Type*) [CommRing k] {G : Type*} [Group G] [Fintype G] [DecidableEq G]

noncomputable def centerClassSum (K : ConjClasses G) :
    Subalgebra.center k (MonoidAlgebra k G) :=
  ⟨classSum k K, classSum_mem_center K⟩

variable {k}

@[simp]
theorem coe_centerClassSum (K : ConjClasses G) :
    (centerClassSum k K : MonoidAlgebra k G) = classSum k K := (rfl)

theorem linearIndependent_centerClassSum :
    LinearIndependent k (centerClassSum k (G := G)) := by
  refine LinearIndependent.of_comp
    (Subalgebra.center k (MonoidAlgebra k G)).val.toLinearMap ?_
  rw [Fintype.linearIndependent_iff]
  intro c hc M
  have h := coeff_sum_smul_classSum c (classRep (G := G) M)
  rw [show ∑ M, c M • classSum k M = 0 from by simpa using hc] at h
  simpa using h.symm

theorem span_range_centerClassSum :
    Submodule.span k (Set.range (centerClassSum k (G := G))) = ⊤ := by
  refine top_unique fun x _ => ?_
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun M => (x : MonoidAlgebra k G).coeff (classRep M), Subtype.ext ?_⟩
  push_cast
  exact eq_sum_smul_classSum x.2

noncomputable def classSumBasis (k : Type*) [CommRing k] {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] :
    Module.Basis (ConjClasses G) k (Subalgebra.center k (MonoidAlgebra k G)) :=
  Module.Basis.mk linearIndependent_centerClassSum (span_range_centerClassSum (k := k)).ge

@[simp]
theorem classSumBasis_apply (K : ConjClasses G) :
    classSumBasis k K = centerClassSum k K := by
  rw [classSumBasis, Module.Basis.mk_apply]

end Basis

section IntegralSpan

variable (k : Type*) [CommRing k] {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private theorem one_mem_span_range_classSum :
    (1 : MonoidAlgebra k G) ∈ Submodule.span ℤ (Set.range (classSum k (G := G))) :=
  classSum_one (k := k) (G := G) ▸ Submodule.subset_span ⟨1, rfl⟩

private theorem span_range_classSum_mul_le :
    Submodule.span ℤ (Set.range (classSum k (G := G)))
        * Submodule.span ℤ (Set.range (classSum k (G := G)))
      ≤ Submodule.span ℤ (Set.range (classSum k (G := G))) := by
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro z ⟨a, ⟨K, rfl⟩, b, ⟨L, rfl⟩, rfl⟩
  change classSum k K * classSum k L ∈ Submodule.span ℤ (Set.range (classSum k (G := G)))
  rw [classSum_mul_classSum]
  refine Submodule.sum_mem _ fun M _ => ?_
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem (Submodule.subset_span (Set.mem_range_self M)) _

noncomputable def integralClassSpan : Subring (MonoidAlgebra k G) :=
  Subalgebra.toSubring <|
    (Submodule.span ℤ (Set.range (classSum k (G := G)))).toSubalgebra
      (one_mem_span_range_classSum k)
      fun _ _ hx hy => span_range_classSum_mul_le k (Submodule.mul_mem_mul hx hy)

variable {k}

theorem mem_integralClassSpan {x : MonoidAlgebra k G} :
    x ∈ integralClassSpan k ↔ x ∈ Submodule.span ℤ (Set.range (classSum k (G := G))) := (Iff.rfl)

theorem classSum_mem_integralClassSpan (K : ConjClasses G) :
    classSum k K ∈ integralClassSpan k :=
  mem_integralClassSpan.2 (Submodule.subset_span ⟨K, rfl⟩)

theorem integralClassSpan_le_center :
    integralClassSpan k ≤ (Subalgebra.center k (MonoidAlgebra k G)).toSubring := by
  intro x hx
  refine Submodule.span_induction (p := fun y _ => y ∈ Subalgebra.center k (MonoidAlgebra k G))
    ?_ ?_ ?_ ?_ (mem_integralClassSpan.1 hx)
  · rintro y ⟨K, rfl⟩
    exact classSum_mem_center K
  · exact zero_mem _
  · intro y z _ _ hy hz
    exact add_mem hy hz
  · intro n y _ hy
    exact zsmul_mem hy n

end IntegralSpan

end CFSG.FeitThompson
