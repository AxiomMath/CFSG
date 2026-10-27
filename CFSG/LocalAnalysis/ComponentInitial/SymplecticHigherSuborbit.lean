module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherProjective

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

variable {r : ℕ} {K : Type} [Field K]

instance [Finite K] : Finite (SpPoint r K) :=
  Finite.of_injective (fun L : SpPoint r K => (L.line : Set (Fin r ⊕ Fin r → K)))
    fun _ _ h => SpPoint.ext (SetLike.coe_injective h)

@[expose] def pointsLeEquiv (U : Submodule K (Fin r ⊕ Fin r → K)) :
    {M : SpPoint r K // M.line ≤ U} ≃ {H : Submodule K U // finrank K H = 1} where
  toFun M := ⟨M.1.line.comap U.subtype,
    ((comapSubtypeEquivOfLe M.2).finrank_eq).trans M.1.finrank_line⟩
  invFun H := ⟨⟨H.1.map U.subtype, (finrank_map_subtype_eq U H.1).trans H.2⟩,
    map_subtype_le U H.1⟩
  left_inv M := Subtype.ext (SpPoint.ext (by
    change (M.1.line.comap U.subtype).map U.subtype = M.1.line
    rw [map_comap_subtype]
    exact inf_eq_right.mpr M.2))
  right_inv H := Subtype.ext (comap_map_eq_of_injective U.injective_subtype H.1)

theorem card_pointsLe_mul [Finite K] (U : Submodule K (Fin r ⊕ Fin r → K)) :
    Nat.card {M : SpPoint r K // M.line ≤ U} * (Nat.card K - 1) =
      Nat.card K ^ finrank K U - 1 := by
  rw [Nat.card_congr ((pointsLeEquiv U).trans (Projectivization.equivSubmodule K U).symm),
    ← Projectivization.card K U, Module.natCard_eq_pow_finrank (K := K) (V := U)]

theorem card_pointsLe [Finite K] (U : Submodule K (Fin r ⊕ Fin r → K)) :
    (Nat.card {M : SpPoint r K // M.line ≤ U} : ℚ) =
      ((Nat.card K : ℚ) ^ finrank K U - 1) / ((Nat.card K : ℚ) - 1) := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h := congrArg (Nat.cast : ℕ → ℚ) (card_pointsLe_mul U)
  rw [Nat.cast_mul, Nat.cast_sub hq.le, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),
    Nat.cast_pow, Nat.cast_one] at h
  have hq' : (Nat.card K : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < Nat.card K := by exact_mod_cast hq
    linarith
  rw [eq_div_iff hq', h]

theorem spOrth_iff_le_orthogonal {L M : SpPoint r K} :
    SpOrth L M ↔ M.line ≤ (pairedSympForm K r).orthogonal L.line :=
  ⟨fun h y hy => BilinForm.mem_orthogonal_iff.mpr fun x hx => h x hx y hy,
    fun h x hx _ hy => BilinForm.mem_orthogonal_iff.mp (h hy) x hx⟩

theorem finrank_orthogonal_line (L : SpPoint r K) :
    finrank K ((pairedSympForm K r).orthogonal L.line) = 2 * r - 1 := by
  have h := BilinForm.finrank_add_finrank_orthogonal
    SymplecticFlag.pairedSympForm_isAlt.isRefl L.line
  rw [BilinForm.orthogonal_top_eq_bot SymplecticFlag.pairedSympForm_nondegenerate, inf_bot_eq,
    finrank_bot, add_zero, finrank_standard, L.finrank_line] at h
  omega

theorem mem_projStabilizer_proj_iff {g : StatedSp r K} {W : Submodule K (Fin r ⊕ Fin r → K)} :
    proj r K g ∈ projStabilizer r K W ↔ g ∈ stabilizer r K W := by
  rw [← Subgroup.mem_comap, comap_projStabilizer]

theorem projStabilizer_eq_stabilizer (L : SpPoint r K) :
    projStabilizer r K L.line = MulAction.stabilizer (StatedProj (StatedSp r K)) L := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [MulAction.mem_stabilizer_iff, proj_smul_spPoint, mem_projStabilizer_proj_iff,
    mem_stabilizer]
  exact ⟨fun h => SpPoint.ext h, fun h => congrArg SpPoint.line h⟩

theorem orbit_stabilizer_eq {L M : SpPoint r K} (hLM : L ≠ M) :
    MulAction.orbit (MulAction.stabilizer (StatedProj (StatedSp r K)) L) M =
      {M' | M' ≠ L ∧ (SpOrth L M' ↔ SpOrth L M)} := by
  ext M'
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective x
    rw [MulAction.mem_stabilizer_iff, proj_smul_spPoint] at hx
    change proj r K g • M ≠ L ∧ (SpOrth L (proj r K g • M) ↔ SpOrth L M)
    rw [proj_smul_spPoint]
    refine ⟨fun h => hLM (smul_left_cancel g (hx.trans h.symm)), ?_⟩
    conv_lhs => rw [← hx]
    exact spOrth_smul_iff g
  · rintro ⟨hM'L, hiff⟩
    obtain ⟨g, hgL, hgM⟩ := ((symplectic_projective_orbits (r := r) (K := K)).2.1 L M L M' hLM
      (Ne.symm hM'L)).mpr hiff.symm
    refine ⟨⟨proj r K g, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, proj_smul_spPoint, hgL]
    · change proj r K g • M = M'
      rw [proj_smul_spPoint, hgM]

theorem relIndex_eq_ncard {L M : SpPoint r K} (hLM : L ≠ M) :
    (projStabilizer r K L.line ⊓ projStabilizer r K M.line).relIndex
      (projStabilizer r K L.line) =
      {M' : SpPoint r K | M' ≠ L ∧ (SpOrth L M' ↔ SpOrth L M)}.ncard := by
  rw [Subgroup.inf_relIndex_left, projStabilizer_eq_stabilizer, projStabilizer_eq_stabilizer,
    Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer,
    orbit_stabilizer_eq hLM]

theorem point_suborbit_indices [Finite K] {q : ℕ} (hq : Nat.card K = q) (hr : 2 ≤ r) :
    (∀ L M : SpPoint r K, L ≠ M → SpOrth L M →
      ((projStabilizer r K L.line ⊓ projStabilizer r K M.line).relIndex
        (projStabilizer r K L.line) : ℚ) = q * ((q : ℚ) ^ (2 * r - 2) - 1) / ((q : ℚ) - 1)) ∧
    (∀ L M : SpPoint r K, L ≠ M → ¬SpOrth L M →
      ((projStabilizer r K L.line ⊓ projStabilizer r K M.line).relIndex
        (projStabilizer r K L.line) : ℚ) = (q : ℚ) ^ (2 * r - 1)) ∧
    ∀ q' : ℕ, 2 ≤ q' → 0 < (q' : ℚ) * ((q' : ℚ) ^ (2 * r - 2) - 1) / ((q' : ℚ) - 1) ∧
      (q' : ℚ) * ((q' : ℚ) ^ (2 * r - 2) - 1) / ((q' : ℚ) - 1) < (q' : ℚ) ^ (2 * r - 1) := by
  classical
  have hq1 : (1 : ℚ) < q := by
    have : 1 < Nat.card K := Finite.one_lt_card
    rw [hq] at this
    exact_mod_cast this
  have hq0 : (q : ℚ) - 1 ≠ 0 := by linarith
  have horth : ∀ L : SpPoint r K, ({M' : SpPoint r K | SpOrth L M'}.ncard : ℚ) =
      ((q : ℚ) ^ (2 * r - 1) - 1) / ((q : ℚ) - 1) := by
    intro L
    have h := card_pointsLe ((pairedSympForm K r).orthogonal L.line)
    rw [finrank_orthogonal_line, hq] at h
    rw [← h, ← Nat.card_coe_set_eq]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun M => spOrth_iff_le_orthogonal)
  have hall : ((Set.univ : Set (SpPoint r K)).ncard : ℚ) =
      ((q : ℚ) ^ (2 * r) - 1) / ((q : ℚ) - 1) := by
    have h := card_pointsLe (⊤ : Submodule K (Fin r ⊕ Fin r → K))
    rw [finrank_top, finrank_standard, hq] at h
    rw [← h, Set.ncard_univ]
    congr 1
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun M => le_top).symm
  refine ⟨fun L M hLM hor => ?_, fun L M hLM hor => ?_, fun a ha => ?_⟩
  · rw [relIndex_eq_ncard hLM]
    have hset : {M' : SpPoint r K | M' ≠ L ∧ (SpOrth L M' ↔ SpOrth L M)} =
        {M' : SpPoint r K | SpOrth L M'} \ {L} := by
      ext M'
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, iff_true_intro hor,
        iff_true]
      exact and_comm
    rw [hset, Set.ncard_sdiff_singleton_of_mem (spOrth_self L), Nat.cast_sub
      ((Set.ncard_pos (Set.toFinite _)).mpr ⟨L, spOrth_self L⟩), horth, Nat.cast_one]
    rw [show 2 * r - 1 = (2 * r - 2) + 1 by omega, pow_succ]
    field_simp
    ring
  · rw [relIndex_eq_ncard hLM]
    have hset : {M' : SpPoint r K | M' ≠ L ∧ (SpOrth L M' ↔ SpOrth L M)} =
        Set.univ \ {M' : SpPoint r K | SpOrth L M'} := by
      ext M'
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, true_and, iff_false_intro hor,
        iff_false]
      exact ⟨fun h => h.2, fun h => ⟨fun e => h (e ▸ spOrth_self L), h⟩⟩
    rw [hset, Set.ncard_sdiff (Set.subset_univ _), Nat.cast_sub
      (Set.ncard_le_ncard (Set.subset_univ _)), hall, horth]
    rw [show 2 * r = (2 * r - 1) + 1 by omega, pow_succ, show 2 * r - 1 + 1 - 1 = 2 * r - 1 by
      omega]
    field_simp
    ring
  · have ha' : (2 : ℚ) ≤ a := by exact_mod_cast ha
    have hx : (1 : ℚ) ≤ (a : ℚ) ^ (2 * r - 2) := one_le_pow₀ (by linarith)
    have hx' : (1 : ℚ) < (a : ℚ) ^ (2 * r - 2) := one_lt_pow₀ (by linarith) (by omega)
    have hpow : (a : ℚ) ^ (2 * r - 1) = a * (a : ℚ) ^ (2 * r - 2) := by
      rw [show 2 * r - 1 = (2 * r - 2) + 1 by omega, pow_succ, mul_comm]
    refine ⟨div_pos (mul_pos (by linarith) (by linarith)) (by linarith), ?_⟩
    rw [div_lt_iff₀ (by linarith), hpow]
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (a : ℚ) ^ (2 * r - 2)) (by linarith :
      (0 : ℚ) ≤ a - 2)]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
