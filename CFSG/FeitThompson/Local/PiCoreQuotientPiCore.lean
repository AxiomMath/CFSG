module

public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] {π : Set ℕ}

theorem natCard_comap_mk' [Finite X] (N : Subgroup X) [N.Normal] (T : Subgroup (X ⧸ N)) :
    Nat.card (T.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card T := by
  set S := T.comap (QuotientGroup.mk' N) with hS
  have hidx : S.index = T.index :=
    Subgroup.index_comap_of_surjective T (QuotientGroup.mk'_surjective N)
  have h1 : Nat.card S * S.index = Nat.card X := Subgroup.card_mul_index S
  have h2 : Nat.card T * T.index = Nat.card (X ⧸ N) := Subgroup.card_mul_index T
  have h3 : Nat.card X = Nat.card (X ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < T.index := Nat.pos_of_ne_zero (by
    rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne')
  have key : Nat.card S * T.index = Nat.card N * Nat.card T * T.index := by
    rw [← hidx, h1, h3, ← h2, hidx]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem IsPiSubgroup.comap_mk' [Finite X] {N : Subgroup X} [N.Normal] (hN : IsPiSubgroup π N)
    {T : Subgroup (X ⧸ N)} (hT : IsPiSubgroup π T) :
    IsPiSubgroup π (T.comap (QuotientGroup.mk' N)) := by
  refine isPiSubgroup_iff.2 fun p hp => ?_
  rw [natCard_comap_mk' N T, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hp
  rcases Finset.mem_union.1 hp with h | h
  · exact isPiSubgroup_iff.1 hN p h
  · exact isPiSubgroup_iff.1 hT p h

theorem eq_bot_of_normal_isPiSubgroup_quotient_piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X]
    {T : Subgroup (X ⧸ piCore π X)} (hT : T.Normal) (hπ : IsPiSubgroup π T) : T = ⊥ := by
  have : (piCore π X).Normal := piCore_normal π X
  have hS : T.comap (QuotientGroup.mk' (piCore π X)) ≤ piCore π X :=
    le_piCore (hT.comap _) ((isPiSubgroup_piCore π X).comap_mk' hπ)
  have hmap : (T.comap (QuotientGroup.mk' (piCore π X))).map
      (QuotientGroup.mk' (piCore π X)) = T :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) T
  rw [← hmap, eq_bot_iff, Subgroup.map_le_iff_le_comap]
  refine hS.trans fun x hx => ?_
  simpa [QuotientGroup.eq_one_iff] using hx

theorem piCore_quotient_piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    piCore π (X ⧸ piCore π X) = ⊥ :=
  le_bot_iff.1 <| piCore_le fun _ hT hπ =>
    le_of_eq (eq_bot_of_normal_isPiSubgroup_quotient_piCore π X hT hπ)

theorem piCore_quotient_eq_bot_of_eq_piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN : N = piCore π X) : piCore π (X ⧸ N) = ⊥ := by
  subst hN
  exact piCore_quotient_piCore π X

theorem pCore_quotient_pCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pCore p (X ⧸ pCore p X) = ⊥ := by
  rw [pCore_eq_piCore p (X ⧸ pCore p X)]
  exact piCore_quotient_eq_bot_of_eq_piCore _ X (pCore_eq_piCore p X)

theorem pComplCore_quotient_pComplCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pComplCore p (X ⧸ pComplCore p X) = ⊥ := by
  rw [pComplCore_eq_piCore p (X ⧸ pComplCore p X)]
  exact piCore_quotient_eq_bot_of_eq_piCore _ X (pComplCore_eq_piCore p X)

end

end CFSG.FeitThompson
