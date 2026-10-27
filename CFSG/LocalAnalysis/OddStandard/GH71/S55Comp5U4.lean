module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5U4Blk
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5U4W
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Arith
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Tr
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Typ

public section

namespace CFSG.OddStandard.GH71.S55

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.Blueprint C5U

namespace C5U

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K)

include h in
theorem dvd_card_four {p : ℕ} {y : StatedProj (StatedSU 4 (r ^ f) K)} (hy : orderOf y = p) :
    p ∣ (r ^ f) ^ 6 * (((r ^ f) ^ 2 - 1) * (((r ^ f) ^ 3 + 1) * ((r ^ f) ^ 4 - 1))) := by
  have := h.finite
  have h1 : p ∣ Nat.card (StatedSU 4 (r ^ f) K) :=
    (hy ▸ orderOf_dvd_natCard y).trans (Subgroup.card_quotient_dvd_card _)
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ h.prime.pos
  have e : Nat.card (StatedSU 4 (r ^ f) K) =
      (r ^ f) ^ 6 * (((r ^ f) ^ 2 - 1) * (((r ^ f) ^ 3 + 1) * ((r ^ f) ^ 4 - 1))) := by
    have e3 := card_statedSU_four_int h
    zify [Nat.one_le_pow 2 _ hq1, Nat.one_le_pow 4 _ hq1]
    exact_mod_cast e3
  rwa [e] at h1

include h in
theorem comp5Concl_psu4 (hr2 : r ≠ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hrp : r ≠ p)
    {y : StatedProj (StatedSU 4 (r ^ f) K)} (hy : orderOf y = p) (hyr : RFree r y) :
    Comp5Concl r y := by
  have := h.finite
  have : Fact r.Prime := ⟨h.prime⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K r := h.charP
  have hK := h.card_eq_sq
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq3 := C5.three_le_pow h.prime hr2 h.one_le
  have hpq := C5.not_dvd_pow (f := f) hp h.prime hrp
  have e4 := card_statedSU_four_int h
  have hnd : ∀ a b : ℕ, ¬ p ∣ a → ¬ p ∣ b → ¬ p ∣ a * b := fun a b ha hb hd =>
    (hp.dvd_mul.1 hd).elim ha hb
  have hpq3 : ¬ p ∣ (r ^ f) ^ 3 := fun hd => hpq (hp.dvd_of_dvd_pow hd)
  rcases dvd_cases_four hp hq1 hpq (dvd_card_four h hy) with h1 | h2 | h6 | h4
  · obtain ⟨e0⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two hK
    have hq3' : r ^ f ≠ 3 := fun h3 => by
      rw [h3] at h1
      exact absurd (Nat.le_of_dvd (by norm_num) h1) (by omega)
    obtain ⟨hq, hc, hrL⟩ := typ_sl h.prime hr2 h.one_le (Or.inl rfl)
      (CFSG.LieType.Steinberg.card_fixedSubfield hK) (Or.inr hq3')
      (e0.trans (blkLEquiv h 2 4 (by norm_num)))
    obtain ⟨-, h2', -, h4', h6', -⟩ := C5.cyc1_excl hp5 hq1 h1
    have e : (r ^ f) ^ 3 + 1 = (r ^ f + 1) * ((r ^ f) ^ 2 - r ^ f + 1) := by
      zify [Nat.le_self_pow two_ne_zero (r ^ f)]
      ring
    refine comp5Concl_of_le_normalizer h (by norm_num) ?_ (range_su22_le_normalizer h) hq hc hrL
      ?_ hy hyr
    · rw [index_su22 h, e]
      exact hnd _ _ (fun hd => hpq (hp.dvd_of_dvd_pow hd)) (hnd _ _ (hnd _ _ h2' h6') h4')
    · rw [CFSG.RankThree.SubgroupLists.card_statedSU_two hK]
      zify [Nat.one_le_pow 2 _ hq1]
      rw [e4]
      exact lt_four_two _ (by exact_mod_cast hq3)
  all_goals
    obtain ⟨hq, hc, hrL⟩ := typ_su3 h.prime hr2 h.one_le hK (blkLEquiv h 3 4 (by norm_num))
    refine comp5Concl_of_le_normalizer h (by norm_num) ?_ (range_blkGU_le_normalizer h 3) hq hc
      hrL ?_ hy hyr
    rotate_left
    · zify
      rw [card_statedSU_three_int h, e4]
      exact lt_four_three _ (by exact_mod_cast hq3)
  · obtain ⟨-, h1', -, h4', -, -⟩ := C5.cyc2_excl hp5 hq1 h2
    rw [index_blkGU_three h]
    exact hnd _ _ hpq3 (hnd _ _ h1' h4')
  · obtain ⟨-, h1', -, -, h4', -⟩ := C5.cyc6_excl hp5 hq1 h6
    rw [index_blkGU_three h]
    exact hnd _ _ hpq3 (hnd _ _ h1' h4')
  · exact absurd hyr (not_rFree_of_dvd_sq_add_one h hp (by omega) h4 hy)

end C5U

theorem comp5_fu4d : Comp5 FU4d := by
  refine comp5_of fun r p Y _ _ hr hr2 hp hp5 hrp hY y g hy hyr hJ => ?_
  obtain ⟨f, hf, -, hLM⟩ := hY
  have hcm : StatedClassicalModel Y .PSU 4 r f := by
    rcases hLM with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  have h : UnitaryFieldData r f K := ⟨hr, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  exact comp5Concl_of_mulEquiv e (fun hy' hyr' _ => comp5Concl_psu4 h hr2 hp hp5 hrp hy' hyr')
    hy hyr hJ

end CFSG.OddStandard.GH71.S55
