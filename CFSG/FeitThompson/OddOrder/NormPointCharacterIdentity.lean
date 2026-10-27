module

public import CFSG.FeitThompson.OddOrder.NormPointClassCoefficient
public import CFSG.FeitThompson.Representations.AbelianByAbelianFrobeniusCharacters
public import CFSG.FeitThompson.Representations.ClassMultiplicationCharacterFormula
public import CFSG.FeitThompson.Representations.CentralFrobeniusLayerDegreeSquareSum
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open SemidirectProduct FrobeniusInduction
open scoped ComplexConjugate

theorem charValueKernel_character {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    charValueKernel ρ.character = (ρ.asGroupHom.ker : Set G) := by
  ext g
  rw [mem_charValueKernel, Representation.char_one ρ, SetLike.mem_coe, MonoidHom.mem_ker,
    Representation.character_eq_finrank_iff_of_finite ρ]
  refine ⟨fun h => Units.ext (by simpa [Representation.asGroupHom] using h), fun h => ?_⟩
  simpa [Representation.asGroupHom] using
    congrArg (fun u : (V →ₗ[ℂ] V)ˣ => (u : V →ₗ[ℂ] V)) h

variable {F : Type*} [Field F] {U : Subgroup Fˣ} {p q m : ℕ}

theorem fixedPointFree_mulRightInvAutOn {v : U} (hv : v ≠ 1) :
    MonoidHom.FixedPointFree (mulRightInvAutOn U v : Multiplicative F → Multiplicative F) := by
  intro w hw
  have h : Multiplicative.toAdd w * (((v : Fˣ)⁻¹ : Fˣ) : F) = Multiplicative.toAdd w := by
    rw [← toAdd_mulRightInvAutOn_apply, hw]
  have hv1 : (((v : Fˣ)⁻¹ : Fˣ) : F) - 1 ≠ 0 := by
    intro h0
    refine hv (Subtype.ext ?_)
    have h1 : ((v : Fˣ)⁻¹ : Fˣ) = 1 := Units.ext (by rw [sub_eq_zero] at h0; exact h0)
    simpa using inv_eq_one.mp h1
  have hz : Multiplicative.toAdd w * ((((v : Fˣ)⁻¹ : Fˣ) : F) - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  simpa using (mul_eq_zero.mp hz).resolve_right hv1

theorem apply_of_mem_fieldAffineBase_of_mem_inflatedIrr {f : fieldAffineGroup F U → ℂ}
    (hf : f ∈ inflatedIrr (mulRightInvAutOn U)) {x : fieldAffineGroup F U}
    (hx : x ∈ fieldAffineBase F U) : f x = 1 := by
  obtain ⟨χ, hχ, rfl⟩ := mem_inflatedIrr.1 hf
  change χ (rightHom x) = 1
  rw [rightHom_eq_right, mem_fieldAffineBase_iff.1 hx, Irr.apply_one_eq_one hχ]

theorem fieldAffineBase_subset_charValueKernel_of_mem_inflatedIrr
    {f : fieldAffineGroup F U → ℂ} (hf : f ∈ inflatedIrr (mulRightInvAutOn U)) :
    (fieldAffineBase F U : Set (fieldAffineGroup F U)) ⊆ charValueKernel f := fun x hx =>
  mem_charValueKernel.2 <| by
    rw [apply_of_mem_fieldAffineBase_of_mem_inflatedIrr hf hx,
      apply_of_mem_fieldAffineBase_of_mem_inflatedIrr hf (one_mem _)]

theorem mem_fieldAffineBase_fieldAffinePointOne :
    fieldAffinePointOne F U ∈ fieldAffineBase F U := by
  rw [fieldAffinePointOne_eq]; exact inl_mem_fieldAffineBase _

section Finite

variable [Finite F]

noncomputable def fieldAffineDetectFinset (F : Type*) [Field F] [Finite F] (U : Subgroup Fˣ) :
    Finset (fieldAffineGroup F U → ℂ) :=
  (finite_irrDetect (fieldAffineBase F U)).toFinset

@[simp] theorem mem_fieldAffineDetectFinset {χ : fieldAffineGroup F U → ℂ} :
    χ ∈ fieldAffineDetectFinset F U ↔
      χ ∈ Irr (fieldAffineGroup F U) ∧
        ¬ (fieldAffineBase F U : Set (fieldAffineGroup F U)) ⊆ charValueKernel χ := by
  rw [fieldAffineDetectFinset, Set.Finite.mem_toFinset, mem_irrDetect, ← Irr_eq_irrChar]

theorem coe_fieldAffineDetectFinset :
    (fieldAffineDetectFinset F U : Set (fieldAffineGroup F U → ℂ))
      = irrDetect ℂ (fieldAffineBase F U) := Set.Finite.coe_toFinset _

theorem fieldAffineDetectFinset_subset_irrFinset :
    fieldAffineDetectFinset F U ⊆ irrFinset (fieldAffineGroup F U) := fun _ hχ =>
  mem_irrFinset.2 (mem_fieldAffineDetectFinset.1 hχ).1

theorem apply_one_of_mem_fieldAffineDetectFinset {χ : fieldAffineGroup F U → ℂ}
    (hχ : χ ∈ fieldAffineDetectFinset F U) : χ 1 = (Nat.card U : ℂ) := by
  have _i1 : Fintype (Multiplicative F) := Fintype.ofFinite _
  have _i2 : Fintype U := Fintype.ofFinite _
  rw [mem_fieldAffineDetectFinset,
    Irr_eq_union (fun v hv => fixedPointFree_mulRightInvAutOn hv)] at hχ
  obtain ⟨h1 | h1, h2⟩ := hχ
  · exact absurd (fieldAffineBase_subset_charValueKernel_of_mem_inflatedIrr h1) h2
  · exact apply_one_of_mem_frobeniusInducedIrr h1

theorem sum_irrFinset_eq_add (g : (fieldAffineGroup F U → ℂ) → ℂ) :
    ∑ χ ∈ irrFinset (fieldAffineGroup F U), g χ
      = ∑ χ ∈ inflatedIrrFinset (mulRightInvAutOn U), g χ
        + ∑ χ ∈ fieldAffineDetectFinset F U, g χ := by
  classical
  have hdisj : Disjoint (inflatedIrrFinset (mulRightInvAutOn U))
      (fieldAffineDetectFinset F U) := by
    rw [Finset.disjoint_right]
    intro χ hχ hχ'
    rw [mem_fieldAffineDetectFinset] at hχ
    rw [mem_inflatedIrrFinset] at hχ'
    exact hχ.2 (fieldAffineBase_subset_charValueKernel_of_mem_inflatedIrr hχ')
  have hunion : inflatedIrrFinset (mulRightInvAutOn U) ∪ fieldAffineDetectFinset F U
      = irrFinset (fieldAffineGroup F U) := by
    ext χ
    rw [Finset.mem_union, mem_inflatedIrrFinset, mem_fieldAffineDetectFinset, mem_irrFinset]
    refine ⟨?_, fun h => ?_⟩
    · rintro (h | ⟨h, -⟩)
      · exact inflatedIrr_subset_Irr h
      · exact h
    · by_cases hc : (fieldAffineBase F U : Set (fieldAffineGroup F U)) ⊆ charValueKernel χ
      · refine Or.inl ?_
        rw [inflatedIrr_eq_irrTrivialOn]
        refine mem_irrTrivialOn.2 ⟨h, fun n hn => mem_charValueKernel.1 (hc ?_)⟩
        rw [SetLike.mem_coe, fieldAffineBase_eq_range_inl]
        exact hn
      · exact Or.inr ⟨h, hc⟩
  rw [← hunion, Finset.sum_union hdisj]

omit [Finite F] in
theorem card_conjPairsProdEq_fieldAffinePointOne
    [Fintype (fieldAffineGroup F U)] [DecidableEq (fieldAffineGroup F U)] :
    (conjPairsProdEq (fieldAffinePointOne F U) (fieldAffinePointOne F U)
        (fieldAffinePointOne F U ^ 2)).card = (fieldAffineSquarePairs F U).ncard := by
  rw [← Set.ncard_coe_finset, coe_conjPairsProdEq]
  congr 1
  ext ⟨x, y⟩
  rw [Set.mem_ofPred_eq, mem_fieldAffineSquarePairs]
  exact Iff.rfl

theorem card_conjClassFinset_fieldAffinePointOne :
    (conjClassFinset (fieldAffinePointOne F U)).card = Nat.card U := by
  rw [← Set.ncard_coe_finset, ← ncard_conjugatesOf_fieldAffinePointOne (F := F) (U := U)]
  congr 1
  ext x
  rw [Finset.mem_coe, mem_conjClassFinset]
  exact Iff.rfl

theorem natCard_mul_ncard_fieldAffineSquarePairs_sub_sq :
    (Nat.card F : ℂ) * (fieldAffineSquarePairs F U).ncard - (Nat.card U : ℂ) ^ 2
      = ∑ χ ∈ fieldAffineDetectFinset F U,
          χ (fieldAffinePointOne F U) ^ 2 * conj (χ (fieldAffinePointOne F U ^ 2)) := by
  classical
  have _i1 : Fintype (Multiplicative F) := Fintype.ofFinite _
  have _i2 : Fintype U := Fintype.ofFinite _
  have _i3 : Fintype (fieldAffineGroup F U) := Fintype.ofFinite _
  set s : fieldAffineGroup F U := fieldAffinePointOne F U with hs
  set n : ℂ := (Nat.card F : ℂ) with hn
  set m : ℂ := (Nat.card U : ℂ) with hm
  set S : ℂ := ∑ χ ∈ fieldAffineDetectFinset F U, χ s * χ s * conj (χ (s ^ 2)) with hS
  have hn0 : n ≠ 0 := by rw [hn, Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  have hm0 : m ≠ 0 := by rw [hm, Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  have key := card_conjPairsProdEq s s (s ^ 2)
  rw [card_conjPairsProdEq_fieldAffinePointOne, card_conjClassFinset_fieldAffinePointOne,
    natCard_fieldAffineGroup, sum_irrFinset_eq_add, Nat.cast_mul] at key
  have hinfl : ∑ χ ∈ inflatedIrrFinset (mulRightInvAutOn U),
      χ s * χ s * conj (χ (s ^ 2)) / χ 1 = m := by
    rw [Finset.sum_congr rfl fun χ hχ => ?_, Finset.sum_const, card_inflatedIrrFinset,
      nsmul_eq_mul, mul_one]
    have hmem := mem_inflatedIrrFinset.1 hχ
    rw [apply_of_mem_fieldAffineBase_of_mem_inflatedIrr hmem
        mem_fieldAffineBase_fieldAffinePointOne,
      apply_of_mem_fieldAffineBase_of_mem_inflatedIrr hmem
        (pow_mem mem_fieldAffineBase_fieldAffinePointOne 2),
      apply_of_mem_fieldAffineBase_of_mem_inflatedIrr hmem (one_mem _)]
    simp
  have hdet : ∑ χ ∈ fieldAffineDetectFinset F U, χ s * χ s * conj (χ (s ^ 2)) / χ 1
      = S / m := by
    rw [hS, Finset.sum_div]
    exact Finset.sum_congr rfl fun χ hχ => by
      rw [apply_one_of_mem_fieldAffineDetectFinset hχ]
  rw [hinfl, hdet, ← hn, ← hm] at key
  have hgoal : n * ((fieldAffineSquarePairs F U).ncard : ℂ) - m ^ 2 = S := by
    field_simp at key
    linear_combination key
  rw [hgoal, hS]
  exact Finset.sum_congr rfl fun χ _ => by rw [sq (χ s)]

end Finite

section Config

theorem norm_point_character_identity_of_config (hp : p.Prime) (_hq : q.Prime) (_hqp : q < p)
    (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (_hcop : Nat.Coprime m (p - 1)) :
    haveI : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
    ((p ^ q : ℕ) : ℂ) * (normOneShiftSet F m).ncard - (m : ℂ) ^ 2
      = ∑ χ ∈ fieldAffineDetectFinset F (normOneSubgroup F m),
          χ (fieldAffinePointOne F (normOneSubgroup F m)) ^ 2
            * conj (χ (fieldAffinePointOne F (normOneSubgroup F m) ^ 2)) := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
  have hm0 : m ≠ 0 := by
    rw [hm, ← Nat.geomSum_eq hp.two_le]
    exact (geomSum_pos_of_natCard_eq_prime_pow (F := F) hp hFcard).ne'
  have hU : Nat.card (normOneSubgroup F m) = m := natCard_normOneSubgroup hp hFcard hm
  have key := natCard_mul_ncard_fieldAffineSquarePairs_sub_sq (F := F) (U := normOneSubgroup F m)
  rwa [ncard_fieldAffineSquarePairs (F := F) hm0, hU, hFcard] at key

end Config

end

end CFSG.FeitThompson
