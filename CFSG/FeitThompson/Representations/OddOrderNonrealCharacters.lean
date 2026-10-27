module

public import CFSG.FeitThompson.Representations.FrobeniusSchurIndicatorReality
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G]

theorem frobeniusSchurIndicator_eq_cfInner_one_of_odd [Fintype G] (hodd : Odd (Nat.card G))
    (f : G → ℂ) : frobeniusSchurIndicator f = cfInner f (1 : G → ℂ) := by
  rw [frobeniusSchurIndicator_def, cfInner_one_right]
  congr 1
  exact (Nat.Coprime.pow_left_bijective (n := 2) (Nat.coprime_two_right.2 hodd)).sum_comp f

theorem frobeniusSchurIndicator_eq_zero_of_ne_one_of_odd [Fintype G] (hodd : Odd (Nat.card G))
    {χ : G → ℂ} (hχ : χ ∈ Irr G) (hne : χ ≠ 1) : frobeniusSchurIndicator χ = 0 := by
  rw [frobeniusSchurIndicator_eq_cfInner_one_of_odd hodd,
    cfInner_eq_ite_of_mem_Irr hχ one_mem_Irr, if_neg hne]

theorem ne_conj_of_mem_Irr_of_ne_one_of_odd [Finite G] (hodd : Odd (Nat.card G))
    {χ : G → ℂ} (hχ : χ ∈ Irr G) (hne : χ ≠ 1) : χ ≠ fun g => conj (χ g) := by
  have : Fintype G := Fintype.ofFinite G
  exact (frobeniusSchurIndicator_eq_zero_iff hχ).1
    (frobeniusSchurIndicator_eq_zero_of_ne_one_of_odd hodd hχ hne)

theorem exists_im_ne_zero_of_mem_Irr_of_ne_one_of_odd [Finite G] (hodd : Odd (Nat.card G))
    {χ : G → ℂ} (hχ : χ ∈ Irr G) (hne : χ ≠ 1) : ∃ g, (χ g).im ≠ 0 := by
  have : Fintype G := Fintype.ofFinite G
  have h := (frobeniusSchurIndicator_eq_zero_iff_not_forall_im_eq_zero hχ).1
    (frobeniusSchurIndicator_eq_zero_of_ne_one_of_odd hodd hχ hne)
  exact not_forall.1 h

def nonprincipalIrr (G : Type*) [Group G] : Set (G → ℂ) := {χ ∈ Irr G | χ ≠ 1}

theorem mem_nonprincipalIrr {χ : G → ℂ} : χ ∈ nonprincipalIrr G ↔ χ ∈ Irr G ∧ χ ≠ 1 := Iff.rfl

theorem nonprincipalIrr_subset_Irr : nonprincipalIrr G ⊆ Irr G := fun _ h => h.1

theorem finite_nonprincipalIrr [Finite G] : (nonprincipalIrr G).Finite :=
  finite_Irr.subset nonprincipalIrr_subset_Irr

instance finite_coe_nonprincipalIrr [Finite G] : Finite (nonprincipalIrr G) :=
  finite_nonprincipalIrr.to_subtype

theorem conj_mem_nonprincipalIrr [Finite G] {χ : G → ℂ} (hχ : χ ∈ nonprincipalIrr G) :
    (fun g => conj (χ g)) ∈ nonprincipalIrr G := by
  refine ⟨conj_mem_Irr hχ.1, fun h => hχ.2 ?_⟩
  funext g
  simpa using congrArg conj (congrFun h g)

section ConjPair

omit [Group G]

def conjPair (χ : G → ℂ) : Set (G → ℂ) := {χ, fun g => conj (χ g)}

theorem self_mem_conjPair (χ : G → ℂ) : χ ∈ conjPair χ := Set.mem_insert _ _

theorem conj_mem_conjPair (χ : G → ℂ) : (fun g => conj (χ g)) ∈ conjPair χ :=
  Set.mem_insert_of_mem _ rfl

theorem conjPair_conj (χ : G → ℂ) : conjPair (fun g => conj (χ g)) = conjPair χ := by
  have h : (fun g => conj (conj (χ g))) = χ := by funext g; simp
  rw [conjPair, h, conjPair, Set.pair_comm]

theorem conjPair_eq_of_mem {χ ψ : G → ℂ} (h : ψ ∈ conjPair χ) : conjPair ψ = conjPair χ := by
  rcases h with h | h
  · rw [h]
  · rw [show ψ = fun g => conj (χ g) from h, conjPair_conj]

end ConjPair

theorem apply_one_eq_of_mem_conjPair {χ ψ : G → ℂ} (hχ : χ ∈ Irr G) (h : ψ ∈ conjPair χ) :
    ψ 1 = χ 1 := by
  rcases h with h | h
  · rw [h]
  · rw [show ψ = fun g => conj (χ g) from h]
    exact conj_apply_one_of_mem_Irr hχ

theorem conjPair_subset_nonprincipalIrr [Finite G] {χ : G → ℂ} (hχ : χ ∈ nonprincipalIrr G) :
    conjPair χ ⊆ nonprincipalIrr G := by
  rintro ψ (h | h)
  · exact h ▸ hχ
  · exact (show ψ = fun g => conj (χ g) from h) ▸ conj_mem_nonprincipalIrr hχ

theorem ncard_conjPair_of_odd [Finite G] (hodd : Odd (Nat.card G)) {χ : G → ℂ}
    (hχ : χ ∈ nonprincipalIrr G) : (conjPair χ).ncard = 2 :=
  Set.ncard_pair (ne_conj_of_mem_Irr_of_ne_one_of_odd hodd hχ.1 hχ.2)

def conjPairs (G : Type*) [Group G] : Set (Set (G → ℂ)) := conjPair '' nonprincipalIrr G

theorem mem_conjPairs_iff {P : Set (G → ℂ)} :
    P ∈ conjPairs G ↔ ∃ χ ∈ nonprincipalIrr G, conjPair χ = P := Iff.rfl

theorem conjPair_mem_conjPairs {χ : G → ℂ} (hχ : χ ∈ nonprincipalIrr G) :
    conjPair χ ∈ conjPairs G := ⟨χ, hχ, rfl⟩

theorem sUnion_conjPairs [Finite G] : ⋃₀ conjPairs G = nonprincipalIrr G := by
  refine Set.Subset.antisymm ?_ fun χ hχ =>
    Set.mem_sUnion_of_mem (self_mem_conjPair χ) (conjPair_mem_conjPairs hχ)
  rintro ψ ⟨P, ⟨χ, hχ, rfl⟩, hψ⟩
  exact conjPair_subset_nonprincipalIrr hχ hψ

theorem pairwiseDisjoint_conjPairs : (conjPairs G).PairwiseDisjoint id := by
  rintro P ⟨χ, -, rfl⟩ Q ⟨ψ, -, rfl⟩ hne
  refine Set.disjoint_left.2 fun f hf hf' => hne ?_
  rw [← conjPair_eq_of_mem hf, ← conjPair_eq_of_mem hf']

def conjNonprincipalIrr (G : Type*) [Group G] [Finite G] : Equiv.Perm (nonprincipalIrr G) :=
  Function.Involutive.toPerm
    (fun χ => ⟨fun g => conj ((χ : G → ℂ) g), conj_mem_nonprincipalIrr χ.2⟩)
    fun χ => by ext g; simp

@[simp]
theorem coe_conjNonprincipalIrr_apply [Finite G] (χ : nonprincipalIrr G) :
    ((conjNonprincipalIrr G χ : G → ℂ)) = fun g => conj ((χ : G → ℂ) g) := (rfl)

theorem conjNonprincipalIrr_involutive [Finite G] :
    Function.Involutive (conjNonprincipalIrr G) := fun χ => by ext g; simp

theorem sq_conjNonprincipalIrr [Finite G] : conjNonprincipalIrr G ^ 2 = 1 := by
  rw [pow_two]
  exact Equiv.ext fun χ => conjNonprincipalIrr_involutive χ

theorem conjNonprincipalIrr_ne_self [Finite G] (hodd : Odd (Nat.card G))
    (χ : nonprincipalIrr G) : conjNonprincipalIrr G χ ≠ χ := by
  intro h
  refine ne_conj_of_mem_Irr_of_ne_one_of_odd hodd χ.2.1 χ.2.2 ?_
  have h' := congrArg (fun ψ : nonprincipalIrr G => (ψ : G → ℂ)) h
  simpa using h'.symm

theorem even_natCard_nonprincipalIrr [Finite G] (hodd : Odd (Nat.card G)) :
    Even (Nat.card (nonprincipalIrr G)) := by
  classical
  have : Fintype (nonprincipalIrr G) := Fintype.ofFinite _
  have hsupp : (conjNonprincipalIrr G).support = Finset.univ := by
    ext χ
    simp [Equiv.Perm.mem_support, conjNonprincipalIrr_ne_self hodd χ]
  have h2 := Equiv.Perm.two_dvd_card_support (sq_conjNonprincipalIrr (G := G))
  rw [hsupp, Finset.card_univ] at h2
  rw [Nat.card_eq_fintype_card]
  exact even_iff_two_dvd.2 h2

end CFSG.FeitThompson
