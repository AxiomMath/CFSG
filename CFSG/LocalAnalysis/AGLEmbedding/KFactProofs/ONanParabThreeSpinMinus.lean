module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabInvol
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusPosLift

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

section Minus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit [CharP F 2] in
theorem minusTorus_pow_eq_one (k : Fin (n - 1)) {g : spinGroup (quadMinus n F b c)}
    (hg : g ∈ minusTorus n hirr k) : g ^ (Nat.card F ^ 2 - 1) = 1 := by
  have h := SpinMinusClosed.pow_eq_one_of_mem_minusTorus hirr k hg
  rwa [SpinMinusClosed.card_shortField] at h

omit hirr in
theorem odd_card_sq_sub_one : Odd (Nat.card F ^ 2 - 1) := by
  obtain ⟨f, hf, hcard⟩ := exists_card_eq_two_pow F
  rw [hcard, ← pow_mul]
  have h1 : 1 ≤ 2 ^ (f * 2 - 1) := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ (f * 2) = 2 * 2 ^ (f * 2 - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  exact ⟨2 ^ (f * 2 - 1) - 1, by omega⟩

theorem borelQuotient_spinMinus (hn : 4 ≤ n) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) :
    BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr)
      (e.symm.toMonoidHom.comp
        (spinToStatedProj (quadMinus n F b c) (range_spinMatrix_quadMinus hn hirr)))
      (Nat.card F ^ 2 - 1) :=
  borelQuotient_of_spin (range_spinMatrix_quadMinus hn hirr)
    (spinToStatedProj_quadMinus hn hirr).2.2.le
    (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero) e (sub_one_dvd_sq_sub_one _)
    odd_card_sq_sub_one (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
    (fun _ hγ => isPGroup_minusRootGroup hirr hγ) (fun k _ hg => minusTorus_pow_eq_one hirr k hg)

omit [Finite F] [CharP F 2] in
theorem hasSL2Node_spinMinus_long {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    HasSL2Node (minusDatum n hirr) k F := by
  refine ⟨(minusFrame n b c).longSL2 (succ_ne_of_lt n hk) true false,
    SpinFrame.longSL2_injective _ (succ_ne_of_lt n hk) true false, fun a => ?_,
    fun a => ?_⟩
  · have h : (minusFrame n b c).longSL2 (succ_ne_of_lt n hk) true false (sl2Upper a) =
        (minusFrame n b c).longRoot (succ_ne_of_lt n hk) true false (.ofAdd a) :=
      (minusFrame n b c).longSL2_upperSL2 (succ_ne_of_lt n hk) true false a
    rw [h]
    have hmem : (minusFrame n b c).longRoot (succ_ne_of_lt n hk) true false (.ofAdd a) ∈
        minusRootGroup n hirr (Pi.single k 1) := by
      rw [minusRootGroup_single_of_lt n hirr hk]
      exact ⟨_, rfl⟩
    exact hmem
  · have h : (minusFrame n b c).longSL2 (succ_ne_of_lt n hk) true false (sl2Lower a) =
        (minusFrame n b c).longRoot (succ_ne_of_lt n hk).symm true false (.ofAdd a) :=
      (minusFrame n b c).longSL2_lowerSL2 (succ_ne_of_lt n hk) true false a
    rw [h]
    have hmem : (minusFrame n b c).longRoot (succ_ne_of_lt n hk).symm true false (.ofAdd a) ∈
        minusRootGroup n hirr (-Pi.single k 1) := by
      rw [minusRootGroup_neg_single_of_lt n hirr hk]
      exact ⟨_, rfl⟩
    exact hmem

theorem hasOrderThree_spinMinus_short {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    HasOrderThree (minusDatum n hirr) k := by
  have := fact_shortField hirr
  have h2 : (1 : ShortField b c) + 1 = 0 := by
    have h := congrArg (algebraMap F (ShortField b c)) (CharTwo.add_self_eq_zero (1 : F))
    simpa using h
  obtain ⟨hx2, hy2, hbraid⟩ := braid_of_rankOneRels h2 (shortRels n hirr k)
  refine HasOrderThree.of_involutions (minusDatum_steinbergExtras n hirr)
    (x := (shortRels n hirr k).x 1) (y := (shortRels n hirr k).y 1)
    ((mem_minusRootGroup_single_iff hirr hk _).2 ⟨1, rfl⟩)
    ((mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨1, rfl⟩) (fun h => ?_) hx2 hy2 hbraid
  have h0 : (shortRels n hirr k).x 0 = 1 := RankOneRels.x_zero _
  exact one_ne_zero (shortRels_x_injective hirr k (h.trans h0.symm))

theorem hasOrderThree_spinMinus (i : Fin (n - 1)) : HasOrderThree (minusDatum n hirr) i := by
  by_cases hk : i.val + 1 < n - 1
  · exact (hasSL2Node_spinMinus_long hirr hk).hasOrderThree
  · exact hasOrderThree_spinMinus_short hirr hk

include hirr in
theorem threeDvd_spinMinus (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact (borelQuotient_spinMinus hirr hn e).three_dvd_card
    (fun i => hasOrderThree_spinMinus hirr i) T J hNJ hJ

end Minus

theorem threeDvd_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact threeDvd_spinMinus hirr (by omega) e T J hNJ hJ

end CFSG.AGLEmbedding.ParabHub
