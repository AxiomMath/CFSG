module

public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.NormalCommuteModIntersection

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] [Finite G] (H : (Nat.card G).primeFactors → Subgroup G)
  (hcard : ∀ p : (Nat.card G).primeFactors,
    Nat.card (H p) = (p : ℕ) ^ (Nat.card G).factorization (p : ℕ))

omit [Finite G] in
include hcard in
theorem coprime_natCard_of_ne {i j : (Nat.card G).primeFactors} (hij : i ≠ j) :
    (Nat.card (H i)).Coprime (Nat.card (H j)) := by
  rw [hcard i, hcard j]
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors i.2)
    (Nat.prime_of_mem_primeFactors j.2)).2 (Subtype.coe_ne_coe.2 hij))

omit [Finite G] in
include hcard in
theorem pairwise_commute_of_normal_sylow_family (hn : ∀ p, (H p).Normal) :
    Pairwise fun i j : (Nat.card G).primeFactors =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
  intro i j hij x y hx hy
  have := hn i
  have := hn j
  exact (commute_iff_eq x y).2
    (mul_comm_of_normal_of_coprime_natCard _ _ (coprime_natCard_of_ne H hcard hij) hx hy)

noncomputable def normalSylowPiHom (hn : ∀ p, (H p).Normal) :
    (∀ p : (Nat.card G).primeFactors, H p) →* G :=
  Subgroup.noncommPiCoprod (pairwise_commute_of_normal_sylow_family H hcard hn)

omit [Finite G] in
theorem normalSylowPiHom_apply (hn : ∀ p, (H p).Normal)
    (u : ∀ p : (Nat.card G).primeFactors, H p) :
    normalSylowPiHom H hcard hn u =
      Finset.noncommProd Finset.univ (fun i => (u i : G))
        (fun i _ j _ h => pairwise_commute_of_normal_sylow_family H hcard hn h _ _ (u i).2
          (u j).2) :=
  Subgroup.noncommPiCoprod_apply _ _

omit [Finite G] in
theorem normalSylowPiHom_apply_list (hn : ∀ p, (H p).Normal)
    (l : List (Nat.card G).primeFactors) (hl : l.Nodup) (hmem : ∀ i, i ∈ l)
    (u : ∀ p : (Nat.card G).primeFactors, H p) :
    normalSylowPiHom H hcard hn u = (l.map fun i => (u i : G)).prod := by
  have huniv : (Finset.univ : Finset (Nat.card G).primeFactors) = l.toFinset := by
    ext i; simp [hmem i]
  rw [normalSylowPiHom_apply]
  refine Eq.trans (Finset.noncommProd_congr huniv (fun x _ => rfl) _) ?_
  exact Finset.noncommProd_toFinset _ _ _ hl

omit [Finite G] in
theorem normalSylowPiHom_mulSingle [DecidableEq (Nat.card G).primeFactors]
    (hn : ∀ p, (H p).Normal) (i : (Nat.card G).primeFactors) (y : H i) :
    normalSylowPiHom H hcard hn (Pi.mulSingle i y) = (y : G) :=
  Subgroup.noncommPiCoprod_mulSingle _ _

omit [Finite G] in
theorem range_normalSylowPiHom (hn : ∀ p, (H p).Normal) :
    (normalSylowPiHom H hcard hn).range = ⨆ p : (Nat.card G).primeFactors, H p :=
  Subgroup.noncommPiCoprod_range

include hcard in
theorem natCard_pi_eq_natCard :
    Nat.card (∀ p : (Nat.card G).primeFactors, H p) = Nat.card G := by
  rw [Nat.card_pi]
  simp only [hcard]
  rw [Finset.prod_coe_sort (Nat.card G).primeFactors
      (fun p => p ^ (Nat.card G).factorization p),
    ← Nat.prod_factorization_eq_prod_primeFactors]
  exact Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'

theorem bijective_normalSylowPiHom (hn : ∀ p, (H p).Normal) :
    Function.Bijective (normalSylowPiHom H hcard hn) := by
  have : ∀ p : (Nat.card G).primeFactors, Fintype (H p) := fun _ => Fintype.ofFinite _
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨?_, natCard_pi_eq_natCard H hcard⟩
  rw [normalSylowPiHom]
  refine Subgroup.injective_noncommPiCoprod_of_iSupIndep
    (Subgroup.independent_of_coprime_order
      (pairwise_commute_of_normal_sylow_family H hcard hn) ?_)
  intro i j hij
  simpa [Nat.card_eq_fintype_card] using coprime_natCard_of_ne H hcard hij

noncomputable def normalSylowPiMulEquiv (hn : ∀ p, (H p).Normal) :
    (∀ p : (Nat.card G).primeFactors, H p) ≃* G :=
  MulEquiv.ofBijective _ (bijective_normalSylowPiHom H hcard hn)

@[simp]
theorem normalSylowPiMulEquiv_apply (hn : ∀ p, (H p).Normal)
    (u : ∀ p : (Nat.card G).primeFactors, H p) :
    normalSylowPiMulEquiv H hcard hn u = normalSylowPiHom H hcard hn u := (rfl)

omit [Finite G] in
theorem subsingleton_pi_of_natCard_eq_one (h : Nat.card G = 1) :
    Subsingleton (∀ p : (Nat.card G).primeFactors, H p) := by
  have : IsEmpty ((Nat.card G).primeFactors : Type) := by
    rw [Finset.isEmpty_coe_sort, h, Nat.primeFactors_one]
  infer_instance

theorem natCard_sylow_eq_pow_factorization
    (P : ∀ p : (Nat.card G).primeFactors, Sylow (p : ℕ) G) (p : (Nat.card G).primeFactors) :
    Nat.card (P p : Subgroup G) = (p : ℕ) ^ (Nat.card G).factorization (p : ℕ) :=
  have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  (P p).card_eq_multiplicity

noncomputable def sylowPiMulEquiv (P : ∀ p : (Nat.card G).primeFactors, Sylow (p : ℕ) G)
    (hn : ∀ p, (P p : Subgroup G).Normal) :
    (∀ p : (Nat.card G).primeFactors, (P p : Subgroup G)) ≃* G :=
  normalSylowPiMulEquiv (fun p => (P p : Subgroup G)) (natCard_sylow_eq_pow_factorization P) hn

end

end CFSG.FeitThompson
