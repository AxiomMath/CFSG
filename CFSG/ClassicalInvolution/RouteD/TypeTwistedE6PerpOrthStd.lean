module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthCount

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution CFSG.LieType.Universal.Spin

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {K : Type} [Field K] [Finite K]

section Dim

variable {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

omit [Finite K] in
theorem card_frame_eq_o4 [FiniteDimensional K V] (hdim : Module.finrank K V = 4) (F : OFrame Q) :
    Nat.card (OFrame Q) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
  have htop : ∀ G : OFrame Q, G.span = ⊤ := by
    intro G
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hdim]
    have hinj : Function.Injective G.incl := fun X Y h => by
      have := congrArg G.coords h
      simpa [Frame.coords_incl] using this
    have h4 : Module.finrank K (Matrix (Fin 2) (Fin 2) K) = 4 := by
      rw [Module.finrank_matrix]; simp
    rw [Frame.span, LinearMap.finrank_range_of_inj hinj, h4]
  rw [← card_frames_span F]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun G => (htop G).trans (htop F).symm).symm

end Dim

section Counts

omit [Field K] [Finite K] in
theorem card_plus_space (m : ℕ) : Nat.card (Fin m ⊕ Fin m → K) = Nat.card K ^ (2 * m) := by
  rw [card_coord_fun, Fintype.card_sum, Fintype.card_fin, two_mul]

omit [Field K] [Finite K] in
theorem card_minus_space (m : ℕ) :
    Nat.card (Fin m ⊕ Fin m ⊕ Fin 2 → K) = Nat.card K ^ (2 * m + 2) := by
  rw [card_coord_fun, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  ring_nf

theorem card_singular_plus_nat (m : ℕ) :
    Nat.card {v : Fin (m + 1) ⊕ Fin (m + 1) → K // quadPlus (m + 1) K v = 0} =
      (Nat.card K ^ (m + 1) - 1) * (Nat.card K ^ m + 1) + 1 := by
  have h := card_singular_quadPlus (K := K) m
  have hq : 1 ≤ Nat.card K ^ (m + 1) := Nat.one_le_pow _ _ Nat.card_pos
  zify [hq]
  linarith

theorem card_singular_minus_nat (h2 : (2 : K) ≠ 0) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ) :
    Nat.card {v // quadMinus (m + 1) K b c v = 0} =
      (Nat.card K ^ (m + 1) + 1) * (Nat.card K ^ m - 1) + 1 := by
  have h := card_singular_quadMinus_of_two_ne_zero h2 hirr m
  have hq : 1 ≤ Nat.card K ^ m := Nat.one_le_pow _ _ Nat.card_pos
  zify [hq]
  linarith

theorem card_singular_odd_nat (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Nat.card {v : Fin n ⊕ Fin n ⊕ Unit → K // quadOdd n K v = 0} = Nat.card K ^ (2 * n) := by
  have h := card_singular_quadOdd_of_two_ne_zero h2 n
  exact_mod_cast h

end Counts

section Families

variable (K)

theorem card_frame_plus (j : ℕ) :
    Nat.card (OFrame (quadPlus (j + 1 + 1) K)) =
      ((Nat.card K ^ (j + 1 + 1) - 1) * (Nat.card K ^ (j + 1) + 1)) * Nat.card K ^ (2 * (j + 1)) *
        (((Nat.card K ^ (j + 1) - 1) * (Nat.card K ^ j + 1)) * Nat.card K ^ (2 * j)) := by
  rw [card_frame_two_step (nondegenerate_polarBilin_quadPlus j K)
    (nondegenerate_polarBilin_quadPlus (j + 1) K) (plusIsometry K (j + 1)) (plusIsometry K j),
    card_singular_plus_nat (j + 1), card_singular_plus_nat j, card_plus_space, card_plus_space]
  simp only [Nat.add_sub_cancel]

theorem card_frame_minus (h2 : (2 : K) ≠ 0) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (j : ℕ) :
    Nat.card (OFrame (quadMinus (j + 1 + 1 + 1) K b c)) =
      ((Nat.card K ^ (j + 1 + 1 + 1) + 1) * (Nat.card K ^ (j + 1 + 1) - 1)) *
          Nat.card K ^ (2 * (j + 1 + 1)) *
        (((Nat.card K ^ (j + 1 + 1) + 1) * (Nat.card K ^ (j + 1) - 1)) *
          Nat.card K ^ (2 * (j + 1))) := by
  rw [card_frame_two_step (nondegenerate_polarBilin_quadMinus_of_finite (j + 1) K hirr)
    (nondegenerate_polarBilin_quadMinus_of_finite (j + 1 + 1) K hirr)
    (minusIsometry K (j + 1) b c) (minusIsometry K j b c),
    card_singular_minus_nat h2 hirr (j + 1 + 1), card_singular_minus_nat h2 hirr (j + 1),
    card_minus_space, card_minus_space]
  simp only [Nat.add_sub_cancel]
  have e1 : 2 * (j + 1) + 2 = 2 * (j + 1 + 1) := by ring
  have e2 : 2 * j + 2 = 2 * (j + 1) := by ring
  rw [e1, e2]

theorem card_frame_odd (h2 : (2 : K) ≠ 0) (j : ℕ) :
    Nat.card (OFrame (quadOdd (j + 1 + 1) K)) =
      (Nat.card K ^ (2 * (j + 1 + 1)) - 1) * Nat.card K ^ (2 * (j + 1) + 1) *
        ((Nat.card K ^ (2 * (j + 1)) - 1) * Nat.card K ^ (2 * j + 1)) := by
  rw [card_frame_two_step (nondegenerate_polarBilin_quadOdd j K h2)
    (nondegenerate_polarBilin_quadOdd (j + 1) K h2) (oddIsometry K (j + 1)) (oddIsometry K j),
    card_singular_odd_nat h2 (j + 1 + 1), card_singular_odd_nat h2 (j + 1)]
  rw [show Nat.card (Fin (j + 1) ⊕ Fin (j + 1) ⊕ Unit → K) = Nat.card K ^ (2 * (j + 1) + 1) from
      card_coord_fun_odd (j + 1),
    show Nat.card (Fin j ⊕ Fin j ⊕ Unit → K) = Nat.card K ^ (2 * j + 1) from card_coord_fun_odd j]

theorem card_frame_minus_two {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (OFrame (quadMinus 2 K b c)) = 0 :=
  card_frame_one_step_aniso (nondegenerate_polarBilin_quadMinus_of_finite 1 K hirr)
    (minusIsometry K 0 b c) fun v hv =>
      by_contra fun h => quadMinus_one_ne_zero hirr v h hv

theorem card_frame_odd_one (h2 : (2 : K) ≠ 0) : Nat.card (OFrame (quadOdd 1 K)) = 0 :=
  card_frame_one_step_aniso (nondegenerate_polarBilin_quadOdd 0 K h2) (oddIsometry K 0)
    fun v hv => by
      rw [quadOdd_apply, Finset.sum_eq_zero (fun i _ => i.elim0), zero_add] at hv
      funext k
      rcases k with i | i | ⟨⟩
      · exact i.elim0
      · exact i.elim0
      · exact pow_eq_zero_iff two_ne_zero |>.mp hv

theorem card_o4 :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      ((Nat.card K ^ (0 + 1 + 1) - 1) * (Nat.card K ^ (0 + 1) + 1)) * Nat.card K ^ (2 * (0 + 1)) *
        (((Nat.card K ^ (0 + 1) - 1) * (Nat.card K ^ 0 + 1)) * Nat.card K ^ (2 * 0)) := by
  obtain ⟨F₀, -⟩ := exists_frame_perp_emb
    ((plusIsometry K 1).trans (hypSumCongr (plusIsometry K 0)))
  rw [← card_frame_plus K 0, ← card_frame_eq_o4 (Q := quadPlus (0 + 1 + 1) K) ?_ F₀]
  simp

end Families

end CFSG.ClassicalInvolution.RouteD.NonClassical
