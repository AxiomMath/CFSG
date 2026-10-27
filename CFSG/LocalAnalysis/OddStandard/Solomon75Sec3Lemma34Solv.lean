module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusLemma24
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability
public import CFSG.Assembly.OrderReductions.PermutationReduction

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

theorem aux_isSolvable_of_isCommProd_sup {G : Type} [Group G] (S : Finset (Subgroup G))
    (hc : (S : Set (Subgroup G)).Pairwise fun F F' => ⁅F, F'⁆ = ⊥)
    (hS : ∀ F ∈ S, Group.IsSolvable ↥F) : Group.IsSolvable ↥(S.sup id) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    infer_instance
  | insert F S hF ih =>
    have hSc : (S : Set (Subgroup G)).Pairwise fun F F' => ⁅F, F'⁆ = ⊥ :=
      hc.mono (by simp)
    have hSs : ∀ F ∈ S, Group.IsSolvable ↥F := fun A hA => hS A (Finset.mem_insert_of_mem hA)
    have := ih hSc hSs
    have := hS F (Finset.mem_insert_self _ _)
    have hcomm : ⁅F, S.sup id⁆ = ⊥ := by
      refine commutator_sup_eq_bot fun A hA => ?_
      have hne : F ≠ A := fun h => hF (h ▸ hA)
      exact hc (by simp) (by simp [hA]) hne
    rw [Finset.sup_insert]
    show Group.IsSolvable ↥(F ⊔ S.sup id)
    let φ : ↥F × ↥(S.sup id) →* ↥(F ⊔ S.sup id) :=
      (prodHom hcomm).codRestrict (F ⊔ S.sup id) (fun p => by
        rw [prodHom_apply]
        exact (F ⊔ S.sup id).mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2))
    have hφ : Function.Surjective φ := by
      rintro ⟨z, hz⟩
      obtain ⟨f, hf, n, hn, rfl⟩ := (mem_sup_of_commutator_eq_bot hcomm).mp hz
      exact ⟨(⟨f, hf⟩, ⟨n, hn⟩), Subtype.ext (by simp [φ, prodHom_apply])⟩
    exact Group.isSolvable_of_surjective hφ

theorem isSolvable_of_isCommProd {Q : Type} [Group Q] [Group.IsSolvable Q] {G : Type} [Group G]
    {N : Subgroup G} (h : IsCommProd Q N) : Group.IsSolvable ↥N := by
  obtain ⟨S, hS, hc, rfl⟩ := h
  refine aux_isSolvable_of_isCommProd_sup S hc fun F hF => ?_
  obtain ⟨e⟩ := hS F hF
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem aux_isSolvable_NOne_SL23 : Group.IsSolvable SL23 := by
  have h24 : Nat.card SL23 = 24 := by
    rw [Nat.card_eq_fintype_card, QModels.card_SL23]
    decide +kernel
  refine CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable SL23 2 3 Nat.prime_two
    Nat.prime_three fun d hd hdvd => ?_
  rw [h24, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hd).1 hdvd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).1 (hd.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).1 h)

theorem isSolvable_NOne {G : Type} [Group G] [Finite G] (h3 : pCore 3 G = ⊥) :
    Group.IsSolvable ↥(NOne G) := by
  have := aux_isSolvable_NOne_SL23
  exact isSolvable_of_isCommProd (lemma_2_4_one h3).2.1

theorem aux_isSolvable_NTwo_A4 : Group.IsSolvable A4 :=
  CFSG.OrderReductions.PermutationReduction.alternating_four_solvable

theorem isSolvable_NTwo {G : Type} [Group G] [Finite G] (h3 : pCore 3 G = ⊥) :
    Group.IsSolvable ↥(NTwo G) := by
  have := aux_isSolvable_NTwo_A4
  exact isSolvable_of_isCommProd (lemma_2_4_two h3).2.1

end CFSG.OddStandard.Solomon75
