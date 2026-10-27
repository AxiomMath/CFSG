module

public import CFSG.FeitThompson.Representations.NormInequalityDisjointDadeSupports
import CFSG.FeitThompson.Representations.CoverInequalitySupportDeficit
import CFSG.FeitThompson.Representations.ZeroCrossedProductIndicesBoundedMass
import CFSG.FeitThompson.Representations.MinimumOddKernelSizeGap
import CFSG.FeitThompson.Representations.FrobeniusSupportDeficitPositive

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CoherentFrobeniusUncovered

open CrossFamilyProjection NormalInducedFamily ZeroCrossedMass MultipleCoverDeficit

theorem odd_natCard_of_subgroup_subgroup {G : Type*} [Group G] (hodd : Odd (Nat.card G))
    {L : Subgroup G} (H : Subgroup ↥L) : Odd (Nat.card ↥H) :=
  hodd.of_dvd_nat ((Subgroup.card_subgroup_dvd_card H).trans (Subgroup.card_subgroup_dvd_card L))

section One

variable {G : Type*} [Group G] [Finite G] {I : Type*} {Lsub : I → Subgroup G} {A : I → Set G}
  {J : I → G → Subgroup G}

theorem one_mem_dadeCoverComplement (hDade : ∀ i, IsDadeData (Lsub i) (A i) (J i)) :
    (1 : G) ∈ dadeCoverComplement A J :=
  mem_dadeCoverComplement_iff.2 fun j => (hDade j).one_notMem_totalDadeSupport

end One

section Main

variable {G : Type*} [Group G] [Fintype G] {I : Type*} [Finite I] [Nonempty I]
  {Lsub : I → Subgroup G} [∀ i, Fintype ↥(Lsub i)] {A : I → Set G} {J : I → G → Subgroup G}
  {H : ∀ i, Subgroup ↥(Lsub i)} [∀ i, (H i).Normal]
  {ι : I → Type*} [∀ i, Finite (ι i)] {ξ : ∀ i, ι i → (↥(Lsub i) → ℂ)} {k₀ : ∀ i, ι i}
  {τ : ∀ i, charSpanZero (Set.range (ξ i)) →+ virtualChars G}
  {ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G}

variable (hodd : Odd (Nat.card G))
  (hDade : ∀ i, IsDadeData (Lsub i) (A i) (J i))
  (hA : ∀ i, A i = (fun x : ↥(Lsub i) => (x : G)) '' (((H i) : Set ↥(Lsub i)) \ {1}))
  (hS : ∀ i, Set.range (ξ i) = indFam (H i) (Irr ↥(H i) \ {1}))
  (hIrr : ∀ i, Set.range (ξ i) ⊆ Irr ↥(Lsub i))
  (hinj : ∀ i, Function.Injective (ξ i))
  (hν : ∀ i, IsCoherentWith (Set.range (ξ i)) (τ i) (ν i))
  (hτ : ∀ (i : I) (f : charSpanZero (Set.range (ξ i))) (F : dadeDomain (Lsub i) (A i)),
    (f : ↥(Lsub i) → ℂ) = (F : ↥(Lsub i) → ℂ) →
      (τ i f : G → ℂ) = ((dadeMap (hDade i) F : classFun G) : G → ℂ))
  (hζ1 : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
  (hdisj : Pairwise fun i j =>
    Disjoint (totalDadeSupport (A i) (J i)) (totalDadeSupport (A j) (J j)))
  (hindex : ∀ i, 1 < (H i).index)
  (hbound : ∀ i, 2 * (H i).index + 1 ≤ Nat.card ↥(H i))
  (hdistinct : Function.Injective fun i => Nat.card ↥(H i))

include hodd hDade hA hS hIrr hinj hν hτ hζ1 hdisj hindex hbound hdistinct in
theorem one_lt_ncard_dadeCoverComplement : 1 < (dadeCoverComplement A J).ncard := by
  classical
  have _ : Fintype I := Fintype.ofFinite I
  have _ : ∀ i, Fintype (ι i) := fun i => Fintype.ofFinite (ι i)
  obtain ⟨i, -, hgap⟩ := exists_min_odd_add_two_le_nat (I := (Finset.univ : Finset I))
    Finset.univ_nonempty (fun i => Nat.card ↥(H i))
    (fun i _ => odd_natCard_of_subgroup_subgroup hodd (H i)) hdistinct.injOn
  have hstep : ∀ j ≠ i, Nat.card ↥(H i) + 2 ≤ Nat.card ↥(H j) :=
    fun j hj => hgap j (Finset.mem_univ j) hj
  have he : (1 : ℝ) < ((H i).index : ℝ) := by exact_mod_cast hindex i
  have hh : 2 * ((H i).index : ℝ) + 1 ≤ (Nat.card ↥(H i) : ℝ) := by
    have h := hbound i
    have h' : ((2 * (H i).index + 1 : ℕ) : ℝ) ≤ (Nat.card ↥(H i) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hpos := frobenius_deficit_pos he hh
  have hB := sum_normalMass_zeroCrossedIndices_le hodd hDade hA hS hIrr hinj hν hτ hζ1 hdisj
    hbound i hstep
  have hB' : ∑ j ∈ zeroCrossedIndices A J H ξ ν k₀ i,
      ((Nat.card ↥(H j) : ℝ) - 1) / (((H j).index : ℝ) * (Nat.card ↥(H j) : ℝ))
        ≤ (((H i).index : ℝ) - 1) / ((Nat.card ↥(H i) : ℝ) + 2) := by
    rw [Finset.sum_congr rfl fun j (_ : j ∈ _) => (normalMass_eq (H j)).symm]
    exact hB
  have hcov := cover_deficit_bound hodd hDade hA hS hinj hIrr hν hτ hζ1 hdisj hbound i
    (zeroCrossedIndices A J H ξ ν k₀ i) (fun j => by
      rw [show cfInner (dadeBeta (A j) (J j) (H j) (ξ j (k₀ j)))
            (coherentImage (ξ i) (ν i) (k₀ i)) = crossedProd A J H ξ ν k₀ j i from
          (crossedProd_eq j i).symm]
      exact mem_zeroCrossedIndices)
  have hGpos : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hfrac : 0 < (((dadeCoverComplement A J).ncard : ℝ) - 1) / (Nat.card G : ℝ) := by
    linarith
  have hnum : 0 < ((dadeCoverComplement A J).ncard : ℝ) - 1 := by
    rcases div_pos_iff.1 hfrac with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · linarith
  have hlt : (1 : ℝ) < ((dadeCoverComplement A J).ncard : ℝ) := by linarith
  exact_mod_cast hlt

include hodd hDade hA hS hIrr hinj hν hτ hζ1 hdisj hindex hbound hdistinct in
theorem exists_mem_dadeCoverComplement_ne_one : ∃ x ∈ dadeCoverComplement A J, x ≠ 1 :=
  (Set.one_lt_ncard_iff_nontrivial_and_finite.1
    (one_lt_ncard_dadeCoverComplement hodd hDade hA hS hIrr hinj hν hτ hζ1 hdisj hindex hbound
      hdistinct)).1.exists_ne 1

end Main

end CoherentFrobeniusUncovered

end CFSG.FeitThompson
