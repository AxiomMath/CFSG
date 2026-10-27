module

public import CFSG.LieType.Chevalley.OddSignRootComponent

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem pinnedX_mem_commutator_of_conj_eq_mul
    {S : Subgroup (ModGL τ K)} {h : ModGL τ K} (hh : h ∈ S)
    {α : Fin τ.rank → ℤ} (hS : ∀ c, pinnedX τ K α c ∈ S) {u : K} (hu : u ≠ 1)
    (hconj : ∀ c, h * pinnedX τ K α c * h⁻¹ = pinnedX τ K α (u * c)) (c : K) :
    pinnedX τ K α c ∈ ⁅S, S⁆ := by
  have hu' : u - 1 ≠ 0 := sub_ne_zero.2 hu
  have e : pinnedX τ K α c = h * pinnedX τ K α ((u - 1)⁻¹ * c) * h⁻¹ *
      (pinnedX τ K α ((u - 1)⁻¹ * c))⁻¹ := by
    rw [hconj, pinnedX_neg, ← pinnedX_add]
    congr 1
    field_simp
    ring
  rw [e, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hh (hS _)

variable {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem canonicalRep_conj_torusElt_conj_pinnedX_self
    (w : WeylGroup τ) (k : Fin τ.rank) (t : Kˣ) (c : K) :
    (canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹) *
        pinnedX τ K (w • (Pi.single k 1 : Fin τ.rank → ℤ)) c *
      (canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹)⁻¹ =
      pinnedX τ K (w • (Pi.single k 1 : Fin τ.rank → ℤ)) (((t ^ 2 : Kˣ) : K) * c) := by
  have hα : IsRoot τ (w • (Pi.single k 1 : Fin τ.rank → ℤ)) :=
    isRoot_iff_exists_smul_single.2 ⟨w, k, rfl⟩
  rw [canonicalRep_conj_torusElt_conj_pinnedX w k t hα c, inv_smul_smul]
  congr 3
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp [Tag.cartan_self]

theorem isPerfect_componentRootSpan_of_sq_ne_one
    {t : Kˣ} (ht : t ^ 2 ≠ 1)
    (i : KernelComponent χ) : Group.IsPerfect (componentRootSpan K χ i) := by
  refine Subgroup.isPerfect_iff.2 (le_antisymm (Subgroup.commutator_le_self _) ?_)
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  have hαr := isRoot_of_mem_componentRoots hα
  obtain ⟨w, k, rfl⟩ := isRoot_iff_exists_smul_single.1 hαr
  have hh := componentTorus_le_componentRootSpan K χ i
    (canonicalRep_conj_torusElt_mem (K := K) hα t)
  refine pinnedX_mem_commutator_of_conj_eq_mul hh (fun d => pinnedX_mem_rootSpan hα d)
    (u := ((t ^ 2 : Kˣ) : K)) (fun h => ht (Units.ext (by simpa using h)))
    (fun d => canonicalRep_conj_torusElt_conj_pinnedX_self w k t d) c

theorem isQuasisimple_componentRootSpan_of_sq_ne_one
    {t : Kˣ} (ht : t ^ 2 ≠ 1) (i : KernelComponent χ) :
    CFSG.IsQuasisimple (componentRootSpan K χ i) := by
  have hperf := isPerfect_componentRootSpan_of_sq_ne_one ht i (χ := χ)
  obtain ⟨⟨α, hαk⟩, rfl⟩ := Quotient.exists_rep i
  have hα : α ∈ componentRoots χ ⟦⟨α, hαk⟩⟧ := ⟨hαk, rfl⟩
  have : Nontrivial (componentRootSpan K χ ⟦⟨α, hαk⟩⟧) := by
    refine (Subgroup.nontrivial_iff_ne_bot _).2 fun h => ?_
    have h1 : pinnedX τ K α 1 ∈ componentRootSpan K χ ⟦⟨α, hαk⟩⟧ := pinnedX_mem_rootSpan hα 1
    rw [h, Subgroup.mem_bot, ← pinnedX_zero τ K α] at h1
    exact one_ne_zero (pinnedX_injective τ K α h1)
  refine CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf fun N hN => ?_
  by_cases hZ : N ≤ Subgroup.center (componentRootSpan K χ ⟦⟨α, hαk⟩⟧)
  · exact Or.inl hZ
  · exact Or.inr (CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf
      isSolvable_componentBorel_subgroupOf (sup_componentBorel_eq_top hN hZ))

theorem orderOf_canonicalRep_conj_torusElt
    {p : ℕ} (hp : p.Prime)
    (w : WeylGroup τ) (k : Fin τ.rank) {t : Kˣ} (htp : orderOf t = p) (ht : t ^ 2 ≠ 1) :
    orderOf (canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
      (canonicalRep (coxeterSystem τ) K w)⁻¹) = p := by
  have : Fact p.Prime := ⟨hp⟩
  set h := canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
    (canonicalRep (coxeterSystem τ) K w)⁻¹ with hhdef
  have hpow : ∀ n : ℕ, h ^ n = canonicalRep (coxeterSystem τ) K w * torusElt τ K k (t ^ n) *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
    intro n
    induction n with
    | zero => simp [torusElt_one]
    | succ n ih =>
      rw [pow_succ, ih, hhdef, pow_succ, torusElt_mul]
      group
  refine orderOf_eq_prime ?_ fun h1 => ht ?_
  · rw [hpow, ← htp, pow_orderOf_eq_one, torusElt_one]
    group
  · have e := canonicalRep_conj_torusElt_conj_pinnedX_self (K := K) w k t 1
    rw [← hhdef, h1, one_mul, inv_one, mul_one, mul_one] at e
    have e2 := pinnedX_injective τ K _ e
    exact Units.ext (by simpa using e2.symm)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
