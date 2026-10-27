module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddGood
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddPSLCard
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.U3TwoAdic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.U3OddIndexTwoPart

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.BenderSuzuki.MatrixGroups CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem not_two_dvd_index_of_count {G P : Type*} [Group G] [Finite G] [Group P] [Finite P]
    {W K : Subgroup G} {H : Subgroup P} {q : ℕ} (hq : q % 2 = 1) (hq1 : 1 < q)
    (hcount : Nat.card (W ⊓ K : Subgroup G) * (q - 1) = 2 * Nat.card H * (q ^ 2 - 1))
    (hP : Nat.card P = q * (q ^ 2 - 1) / 2) (hH : ¬ 2 ∣ H.index)
    (hG : Nat.card G = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) : ¬ 2 ∣ W.index := by
  have hodd : Odd q := Nat.odd_iff.2 hq
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hsub : q ^ 2 - 1 ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  have hq10 : q - 1 ≠ 0 := by omega
  have hHP : padicValNat 2 (Nat.card H) = padicValNat 2 (Nat.card P) :=
    u3_padic_card_eq_of_index_odd H hH
  have hsqv := u3two_padic_sq_sub_one q hodd hq1
  have hPe : Nat.card P * 2 = q * (q ^ 2 - 1) := by
    rw [hP]
    apply Nat.div_mul_cancel
    obtain ⟨a, ha⟩ := hodd
    exact Dvd.dvd.mul_left (by
      have : q ^ 2 - 1 = 4 * a * (a + 1) := by
        have h : q ^ 2 = 4 * a * (a + 1) + 1 := by rw [ha]; ring
        omega
      rw [this]
      exact ⟨2 * a * (a + 1), by ring⟩) q
  have hPpos : Nat.card P ≠ 0 := Nat.card_pos.ne'
  have hHpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hWKpos : Nat.card (W ⊓ K : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  have hPv : padicValNat 2 (Nat.card P) + 1 = padicValNat 2 (q ^ 2 - 1) := by
    have h1 := congrArg (padicValNat 2) hPe
    rw [padicValNat.mul hPpos (by norm_num), padicValNat.mul hq0 hsub,
      u3two_padic_of_odd hodd, padicValNat_self] at h1
    omega
  have hcv := congrArg (padicValNat 2) hcount
  rw [padicValNat.mul hWKpos hq10, padicValNat.mul (mul_ne_zero (by norm_num) hHpos) hsub,
    padicValNat.mul (by norm_num) hHpos, padicValNat_self] at hcv
  have hGv := u3two_padic_order q hodd hq1
  rw [← hG] at hGv
  have hWK : padicValNat 2 (Nat.card (W ⊓ K : Subgroup G)) = padicValNat 2 (Nat.card G) := by
    omega
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (inf_le_left : W ⊓ K ≤ W)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    exact Nat.card_pos.ne' hm
  have hGW : Nat.card W * W.index = Nat.card G := W.card_mul_index
  have hWpos : Nat.card W ≠ 0 := Nat.card_pos.ne'
  have hidx0 : W.index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hGW
    exact Nat.card_pos.ne' hGW.symm
  have h1 := congrArg (padicValNat 2) hm
  rw [padicValNat.mul hWKpos hm0] at h1
  have h2 := congrArg (padicValNat 2) hGW
  rw [padicValNat.mul hWpos hidx0] at h2
  have h3 : padicValNat 2 W.index = 0 := by omega
  rcases padicValNat.eq_zero_iff.1 h3 with h | h | h
  · omega
  · exact absurd h hidx0
  · exact h

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem u3OddGood_of_dickson (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq3 : (p ^ f) % 3 = 1) (hq4 : (p ^ f) % 4 = 3)
    (hD : ∀ A H : Subgroup (PSL2MatrixGroup (fixedSubfield F p f)), Nat.card A = 3 →
      Nat.card (fixedSubfield F p f) - 1 ∣
        Nat.card (Subgroup.normalizer (A : Set (PSL2MatrixGroup (fixedSubfield F p f)))) →
      Subgroup.normalizer (A : Set _) ≤ H → H = Subgroup.normalizer (A : Set _) ∨ ¬ 2 ∣ H.index) :
    U3OddGood F p f hF := by
  intro ω hω W hNW ⟨x, hxW, hxz, hxN⟩
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  have hω' := pow_eq_self_of_orderOf_three hω hq3
  have hTN := range_tSU_le_normA0 hF hω hq3
  have hTW : (tSU hF).range ≤ W := hTN.trans hNW
  obtain ⟨l, hl, t, ht, rfl⟩ := (mem_centralizer_zSU_iff hF hp2 x).1 hxz
  have hlW : l ∈ W := by
    have : l = (l * t) * t⁻¹ := by group
    rw [this]
    exact W.mul_mem hxW (W.inv_mem (hTW ht))
  have hlN : l ∉ normA0 hF ω := fun h => hxN ((normA0 hF ω).mul_mem h (hTN ht))
  rw [← range_levi hζ0 hζ] at hl
  obtain ⟨w, rfl⟩ := hl
  have hA := card_zpowers_pslMk_diagSL hζ0 hζ hF hω hq3
  have hAH := (normalizer_psl_le_map_comap hζ0 hζ hF hω hq3).trans
    (Subgroup.map_mono (Subgroup.comap_mono hNW))
  have hF0 : Nat.card (fixedSubfield F p f) = p ^ f := card_fixedSubfield hF
  have hN : Nat.card (fixedSubfield F p f) - 1 ∣ Nat.card (Subgroup.normalizer
      ((Subgroup.zpowers (pslMk (fixedSubfield F p f)
        (diagSL (pow_eq_self_of_orderOf_three hω hq3))) : Subgroup
          (PSL2MatrixGroup (fixedSubfield F p f))) : Set (PSL2MatrixGroup (fixedSubfield F p f)))) := by
    rw [card_normalizer_psl hζ0 hζ hF hω hq3 hp2, hF0]
  rcases hD _ _ hA hN hAH with hEq | hodd
  · exfalso
    apply hlN
    have hmem : pslMk (fixedSubfield F p f) w ∈
        (W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) :=
      ⟨w, Subgroup.mem_comap.2 hlW, rfl⟩
    rw [hEq] at hmem
    exact levi_mem_normA0_of_psl_normalizer hζ0 hζ hF hω hq3 hmem
  · have hF0 : Nat.card (fixedSubfield F p f) = p ^ f := card_fixedSubfield hF
    have hodd2 : Odd (p ^ f) := odd_prime_pow hp2
    have hq1 : 1 < p ^ f := by omega
    exact not_two_dvd_index_of_count (Nat.odd_iff.1 hodd2) hq1
      (card_inf_centralizer_zSU_eq hζ0 hζ hF hp2 W hTW)
      (CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF0 hp2) hodd (card_SU3 hF)

theorem overgroupL32U3Odd_of_dickson
    (hD : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime], Nat.card K = p ^ f →
      p ≠ 2 → Nat.card K % 3 = 1 → Nat.card K % 4 = 3 →
      ∀ A H : Subgroup (PSL2MatrixGroup K), Nat.card A = 3 →
        Nat.card K - 1 ∣ Nat.card (Subgroup.normalizer (A : Set (PSL2MatrixGroup K))) →
        Subgroup.normalizer (A : Set _) ≤ H →
        H = Subgroup.normalizer (A : Set _) ∨ ¬ 2 ∣ H.index) : OvergroupL32U3Odd :=
  overgroupL32U3Odd_of_good fun F _ _ p f _ _ hF hp2 hq3 hq4 =>
    u3OddGood_of_dickson hF hp2 hq3 hq4 (fun A H hA hN hAH =>
      hD (fixedSubfield F p f) p f (card_fixedSubfield hF) hp2
        (by rw [card_fixedSubfield hF]; exact hq3) (by rw [card_fixedSubfield hF]; exact hq4)
        A H hA hN hAH)

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
