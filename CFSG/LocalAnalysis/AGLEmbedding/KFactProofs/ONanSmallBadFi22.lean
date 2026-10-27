module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveOrbit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad.Fi22

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore CFSG.AGLEmbedding.KFactProofs.Fi22Five
  CFSG.AGLEmbedding.KFactProofs.RankOneCore CFSG.AGLEmbedding.KFactProofs.SmallIdent
open scoped commutatorElement

theorem fi22_norm_data :
    ∃ x y n₁ n₂ : fi22P, PlaneData x y ∧ n₁ * x * n₁⁻¹ = x ^ 2 * y ^ 3 ∧
      n₁ * y * n₁⁻¹ = x ^ 1 * y ^ 2 ∧ n₂ * x * n₂⁻¹ = x ^ 4 * y ^ 1 ∧
      n₂ * y * n₂⁻¹ = x ^ 1 * y ^ 1 := by
  have h := orb_check
  unfold orbCheck at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hlx, hly, hl1, hl2, hx5, hy5, hcomm, hne, c1x, c1y, c2x, c2y, -⟩ := h
  obtain ⟨X, hXP, hX⟩ := exists_rep_evalW hlx
  obtain ⟨Y, hYP, hY⟩ := exists_rep_evalW hly
  obtain ⟨N1, hN1P, hN1⟩ := exists_rep_evalW hl1
  obtain ⟨N2, hN2P, hN2⟩ := exists_rep_evalW hl2
  have hX' : Rep 3510 xA X := hX
  have hY' : Rep 3510 yA Y := hY
  have hN1' : Rep 3510 n1A N1 := hN1
  have hN2' : Rep 3510 n2A N2 := hN2
  have hX5 : X ^ 5 = 1 := (eqA_iff (rep_pw hX' 5) rep_idA).1 hx5
  have hY5 : Y ^ 5 = 1 := (eqA_iff (rep_pw hY' 5) rep_idA).1 hy5
  have hXY : X * Y = Y * X := (eqA_iff (rep_compA hX' hY') (rep_compA hY' hX')).1 hcomm
  have hne' : ∀ i < 5, ∀ j < 5, ¬ (i = 0 ∧ j = 0) → X ^ i * Y ^ j ≠ 1 := by
    intro i hi j hj hij h1
    have h2 := allLt_spec (allLt_spec hne hi) hj
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
    rcases h2 with h2 | h2
    · exact hij h2
    · have := (eqA_iff (rep_planeA hX' hY' i j) rep_idA).2 h1
      rw [this] at h2
      exact Bool.noConfusion h2
  have hN1X : N1 * X = X ^ 2 * Y ^ 3 * N1 :=
    (eqA_iff (rep_compA hN1' hX') (rep_compA (rep_planeA hX' hY' 2 3) hN1')).1 c1x
  have hN1Y : N1 * Y = X ^ 1 * Y ^ 2 * N1 :=
    (eqA_iff (rep_compA hN1' hY') (rep_compA (rep_planeA hX' hY' 1 2) hN1')).1 c1y
  have hN2X : N2 * X = X ^ 4 * Y ^ 1 * N2 :=
    (eqA_iff (rep_compA hN2' hX') (rep_compA (rep_planeA hX' hY' 4 1) hN2')).1 c2x
  have hN2Y : N2 * Y = X ^ 1 * Y ^ 1 * N2 :=
    (eqA_iff (rep_compA hN2' hY') (rep_compA (rep_planeA hX' hY' 1 1) hN2')).1 c2y
  set x : fi22P := ⟨X, hXP⟩ with hx_def
  set y : fi22P := ⟨Y, hYP⟩ with hy_def
  set n1 : fi22P := ⟨N1, hN1P⟩ with hn1_def
  set n2 : fi22P := ⟨N2, hN2P⟩ with hn2_def
  have hD : PlaneData x y := by
    refine ⟨Subtype.ext hX5, Subtype.ext hY5, Subtype.ext hXY, fun v hv h => ?_⟩
    refine hne' (v 0).val (ZMod.val_lt _) (v 1).val (ZMod.val_lt _) ?_ (congrArg Subtype.val h)
    rintro ⟨h0, h1⟩
    exact hv (funext fun i => by
      fin_cases i
      · exact (ZMod.val_eq_zero _).1 h0
      · exact (ZMod.val_eq_zero _).1 h1)
  have hconj_of : ∀ (n a b : fi22P), n * a = b * n → n * a * n⁻¹ = b := fun n a b h => by
    rw [h]
    group
  exact ⟨x, y, n1, n2, hD, hconj_of _ _ _ (Subtype.ext hN1X), hconj_of _ _ _ (Subtype.ext hN1Y),
    hconj_of _ _ _ (Subtype.ext hN2X), hconj_of _ _ _ (Subtype.ext hN2Y)⟩

theorem not_normalizerQuotientComm_fi22P :
    ¬ NormalizerQuotientComm 5 fi22P := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, y, n₁, n₂, hD, h1x, h1y, h2x, h2y⟩ := fi22_norm_data
  obtain ⟨-, hcard, -⟩ := hD.closure_facts
  have hP : Nat.card fi22P = 5 ^ 2 * 2582470066176 := by rw [card_fi22P]; norm_num
  have hfac : (Nat.card fi22P).factorization 5 = 2 := by
    rw [hP]
    exact factorization_pow_mul (by norm_num) (by norm_num) (by norm_num)
  let T : Sylow 5 fi22P := Sylow.ofCard (Subgroup.closure ({x, y} : Set fi22P))
    (by rw [hcard, hfac])
  have hT : (T : Subgroup fi22P) = Subgroup.closure ({x, y} : Set fi22P) := rfl
  have hTne : (T : Subgroup fi22P) ≠ ⊥ := by
    intro hbot
    rw [hT] at hbot
    have : Nat.card (Subgroup.closure ({x, y} : Set fi22P)) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [hcard] at this
    norm_num at this
  have hxm : ∀ i j : ℕ, x ^ i * y ^ j ∈ Subgroup.closure ({x, y} : Set fi22P) := fun i j =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hn₁ := mem_normalizer_closure_pair (x := x) (y := y) (n := n₁)
    (by rw [h1x]; exact hxm 2 3) (by rw [h1y]; exact hxm 1 2)
  have hn₂ := mem_normalizer_closure_pair (x := x) (y := y) (n := n₂)
    (by rw [h2x]; exact hxm 4 1) (by rw [h2y]; exact hxm 1 1)
  have hind : ∀ m n : ℕ, x ^ m * y ^ n = 1 → (m : ZMod 5) = 0 ∧ (n : ZMod 5) = 0 := by
    intro m n h1
    by_contra hcon
    have hv : (![(m : ZMod 5), (n : ZMod 5)] : Fin 2 → ZMod 5) ≠ 0 := by
      intro h0
      apply hcon
      exact ⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩
    apply hD.ne _ hv
    have e1 : x ^ (m % 5) = x ^ m := (pow_eq_pow_mod m hD.x_pow).symm
    have e2 : y ^ (n % 5) = y ^ n := (pow_eq_pow_mod n hD.y_pow).symm
    simpa [e1, e2] using h1
  refine not_normalizerQuotientComm_of_witness T hTne (by rw [hT]; exact hn₁)
    (by rw [hT]; exact hn₂) fun hmem => ?_
  rw [hT] at hmem
  exact commutator_not_mem_plane hD.comm hD.x_pow hD.y_pow hind 2 3 1 2 4 1 1 1 h1x h1y h2x h2y
    (by decide) (by simpa only [commutatorElement_def] using hmem)

theorem not_normalizerQuotientComm_isFi22
    {L : Type} [Group L] [Finite L]
    (hs : IsSimpleGroup L) (hK : CFSG.AGLEmbedding.IsFi22 L) : ¬ NormalizerQuotientComm 5 L := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_equiv_fi22 hs hK
  intro hc
  exact not_normalizerQuotientComm_fi22P
    (NormalizerQuotientComm.of_mulEquiv (e.trans fi22PermEquiv) hc)

end CFSG.AGLEmbedding.KFactProofs.SmallBad.Fi22
