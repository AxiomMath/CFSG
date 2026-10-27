module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthFrame
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthGeom
public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.RouteD.Exotic
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section NonAbelian

theorem exists_sl2_not_comm : ∃ A B : SL(2, K), A * B ≠ B * A := by
  have key : (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) ≠
      !![1, 0; 1, 1] * !![1, 1; 0, 1] := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
  exact ⟨⟨!![1, 1; 0, 1], by simp⟩, ⟨!![1, 0; 1, 1], by simp⟩,
    fun h => key (congrArg Subtype.val h)⟩

theorem not_commutes_self_range (F : OFrame Q) : ¬ Commutes F.La.range F.La.range := by
  intro h
  obtain ⟨A, B, hAB⟩ := exists_sl2_not_comm (K := K)
  exact hAB (F.La_injective (by
    rw [map_mul, map_mul]
    exact h _ ⟨A, rfl⟩ _ ⟨B, rfl⟩))

end NonAbelian

section Nbhd

variable [Finite K] [Finite V]

instance finite_linearEquiv : Finite (V ≃ₗ[K] V) :=
  Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective

omit [Finite V] in
theorem nbhd_eq_insert (hodd : Odd (Nat.card K)) (F₀ : OFrame Q) :
    {S : Subgroup (V ≃ₗ[K] V) | S ∈ fundSet Q ∧ Commutes S F₀.La.range} =
      insert F₀.swap.La.range
        {S | ∃ F : OFrame Q, F.La.range = S ∧ F.span ≤ F₀.perp} := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  ext S
  constructor
  · rintro ⟨⟨i, F, hSF, rfl⟩, hc⟩
    subst hSF
    rcases orth_or_twin hodd (IsFundamental.of_frame F₀) (IsFundamental.of_frame F) hc.symm with
      h | h
    · exact Or.inr ⟨F, rfl, span_le_perp_of_negSpace hodd h⟩
    · rcases Frame.La_range_eq_or_eq_swap h2 h with h' | h'
      · exact absurd (h' ▸ hc) (not_commutes_self_range F₀)
      · exact Or.inl h'
  · rintro (rfl | ⟨F, rfl, hF⟩)
    · refine ⟨⟨_, IsFundamental.of_frame_swap F₀⟩, ?_⟩
      rintro _ ⟨B, rfl⟩ _ ⟨A, rfl⟩
      exact (F₀.La_comm_La_swap A B).symm
    · refine ⟨⟨_, IsFundamental.of_frame F⟩, ?_⟩
      rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
      exact Frame.La_comm_of_orth (fun X Y =>
        (Frame.mem_perp_iff_forall_incl F₀).mp (hF ⟨X, rfl⟩) Y) A B

omit [Finite V] in
theorem swap_range_notMem (hodd : Odd (Nat.card K)) (F₀ : OFrame Q) :
    F₀.swap.La.range ∉ {S : Subgroup (V ≃ₗ[K] V) | ∃ F : OFrame Q, F.La.range = S ∧
      F.span ≤ F₀.perp} := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  rintro ⟨F, hF, hle⟩
  have hneg : F.La (-1) = F₀.La (-1) :=
    (frame_La_neg_one_eq_of_range_eq hodd hF).trans (Frame.La_swap_neg_one F₀)
  have hsp : F.span = F₀.span := Frame.span_eq_of_La_neg_one_eq h2 hneg
  have hbot : F₀.span = ⊥ :=
    F₀.isCompl_span_perp.disjoint.eq_bot_of_le (hsp ▸ hle)
  have hmem : F₀.e₁ ∈ F₀.span := ⟨!![1, 0; 0, 0], (Frame.e₁_eq_incl F₀).symm⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact F₀.P.e_ne_zero hmem

theorem two_mul_card_frames_perp (hodd : Odd (Nat.card K)) (F₀ : OFrame Q) :
    2 * Nat.card {F : OFrame Q // F.span ≤ F₀.perp} +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      Nat.card {S : Subgroup (V ≃ₗ[K] V) // S ∈ fundSet Q ∧ Commutes S F₀.La.range} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set N' : Set (Subgroup (V ≃ₗ[K] V)) :=
    {S | ∃ F : OFrame Q, F.La.range = S ∧ F.span ≤ F₀.perp} with hN'
  have hcardN : Nat.card {S : Subgroup (V ≃ₗ[K] V) // S ∈ fundSet Q ∧ Commutes S F₀.La.range} =
      N'.ncard + 1 := by
    have h1 : Nat.card {S : Subgroup (V ≃ₗ[K] V) // S ∈ fundSet Q ∧ Commutes S F₀.La.range} =
        ({S : Subgroup (V ≃ₗ[K] V) | S ∈ fundSet Q ∧ Commutes S F₀.La.range} :
          Set (Subgroup (V ≃ₗ[K] V))).ncard := Nat.card_coe_set_eq _
    rw [h1, nbhd_eq_insert hodd F₀, Set.ncard_insert_of_notMem (swap_range_notMem hodd F₀)
      (Set.toFinite _)]
  have hle : ∀ F : OFrame Q, F.La.range ∈ N' → F.span ≤ F₀.perp := by
    rintro F ⟨F', hF', hle⟩
    have hneg := frame_La_neg_one_eq_of_range_eq hodd hF'
    exact (Frame.span_eq_of_La_neg_one_eq h2 hneg.symm).symm ▸ hle
  let f : {F : OFrame Q // F.span ≤ F₀.perp} → N' := fun F => ⟨F.1.La.range, F.1, rfl, F.2⟩
  let _ : Fintype N' := Fintype.ofFinite N'
  have hfib : ∀ S : N', 2 * Nat.card {F : {F : OFrame Q // F.span ≤ F₀.perp} // f F = S} =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
    intro S
    obtain ⟨F₁, hF₁, hF₁le⟩ := S.2
    have e : {F : {F : OFrame Q // F.span ≤ F₀.perp} // f F = S} ≃
        {F : OFrame Q // F.La.range = F₁.La.range} :=
      { toFun := fun F => ⟨F.1.1, (congrArg Subtype.val F.2).trans hF₁.symm⟩
        invFun := fun F => ⟨⟨F.1, hle F.1 ⟨F₁, F.2.symm, hF₁le⟩⟩, Subtype.ext (F.2.trans hF₁)⟩
        left_inv := fun F => rfl
        right_inv := fun F => rfl }
    rw [Nat.card_congr e]
    exact two_mul_card_frames_range hodd F₁
  have hsum : Nat.card {F : OFrame Q // F.span ≤ F₀.perp} =
      ∑ S : N', Nat.card {F : {F : OFrame Q // F.span ≤ F₀.perp} // f F = S} := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv f)]
  have hF : 2 * Nat.card {F : OFrame Q // F.span ≤ F₀.perp} =
      N'.ncard * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
    rw [hsum, Finset.mul_sum, Finset.sum_congr rfl fun S _ => hfib S, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hF, hcardN]
  ring

omit [Finite K] [Finite V] in
theorem span_map_le_perp_map_iff {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (G F : OFrame Q) :
    (G.map hg).span ≤ (F.map hg).perp ↔ G.span ≤ F.perp := by
  rw [span_le_perp_iff, span_le_perp_iff]
  constructor
  · intro h X Y
    have := h X Y
    rwa [Frame.map_incl, Frame.map_incl, polar_map_of_mem hg] at this
  · intro h X Y
    rw [Frame.map_incl, Frame.map_incl, polar_map_of_mem hg]
    exact h X Y

omit [Finite K] [Finite V] in
theorem frame_map_map_inv {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (F : OFrame Q) : (F.map hg).map (inv_mem hg) = F := by
  refine Frame.ext_vec ?_ ?_ ?_ ?_
  · exact g.symm_apply_apply _
  · exact g.symm_apply_apply _
  · exact g.symm_apply_apply _
  · exact g.symm_apply_apply _

omit [Finite V] in
theorem card_frames_perp_conj [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    (F F₁ : OFrame Q) :
    Nat.card {F' : OFrame Q // F'.span ≤ F.perp} =
      Nat.card {F' : OFrame Q // F'.span ≤ F₁.perp} := by
  have : Invertible (2 : K) := invertibleOfNonzero (IsFundamental.two_ne_zero_of_odd hodd)
  obtain ⟨g, hg, hgi⟩ := exists_isometry_incl_eq F F₁
  have hmap : F.map hg = F₁ := Frame.map_eq_of_incl hg hgi
  have hg' := inv_mem hg
  refine Nat.card_congr
    { toFun := fun F' => ⟨F'.1.map hg, by
        rw [← hmap]
        exact (span_map_le_perp_map_iff hg F'.1 F).mpr F'.2⟩
      invFun := fun F' => ⟨F'.1.map hg', by
        have h := (span_map_le_perp_map_iff hg' F'.1 F₁).mpr F'.2
        have h1 : F₁.map hg' = F := by rw [← hmap]; exact frame_map_map_inv hg F
        rwa [h1] at h⟩
      left_inv := fun F' => Subtype.ext (by
        change (F'.1.map hg).map hg' = F'.1
        exact frame_map_map_inv hg F'.1)
      right_inv := fun F' => Subtype.ext (by
        refine Frame.ext_vec ?_ ?_ ?_ ?_
        · exact g.apply_symm_apply _
        · exact g.apply_symm_apply _
        · exact g.apply_symm_apply _
        · exact g.apply_symm_apply _) }

end Nbhd

end CFSG.ClassicalInvolution.RouteD.NonClassical
