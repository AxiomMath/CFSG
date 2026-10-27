module

public import CFSG.CGT.Timmesfeld75.ListWCCert
public import CFSG.LargeExtraspecial.D73TI
public import CFSG.LargeExtraspecial.D73IdentPSL

public section

namespace CFSG.LargeExtraspecial.DW.D73


open Subgroup CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

theorem nonempty_mulEquiv_SL_of_ti (hNode : NodeStatement) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {N : ℕ} (hN : 6 ≤ N) (T : Subgroup G)
    [IsElementaryAbelian 2 T] (hcard : Nat.card T = 2 ^ (N - 1))
    (hC : centralizer (T : Set G) = T)
    (hti : ∀ g : G, T ⊓ conjSubgroup g⁻¹ T = ⊥ ∨ T ⊓ conjSubgroup g⁻¹ T = T)
    (h2 : 2 ^ (N * (N - 1) / 2) ∣ Nat.card G) : Nonempty (G ≃* SL(N, ZMod 2)) := by
  have hEl : CFSG.Open.IsElemAbelian 2 T :=
    ⟨inferInstance, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have h32 : 32 ≤ Nat.card T := by
    rw [hcard]
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (N - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ≤ Nat.card T := by omega
  have hwc := weaklyClosed_of_isTI hC hti
  have hL := hNode G hnab T hEl h4 hti hwc
  have hstd : StdPair G T := listWCIdentification_of_cert G hL T
    (isWC_of_corBHyp (corBHyp_of_ti_of_weaklyClosed hEl hti hwc)) h4
  have hSyl : ∀ P : Sylow 2 G, ¬ (P : Subgroup G) ≤ T := by
    intro P hP
    have h1 := Nat.le_of_dvd Nat.card_pos (P.pow_dvd_card_of_pow_dvd_card h2)
    have h3 := (h1.trans (Subgroup.card_le_of_le hP)).trans_eq hcard
    have h5 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
    have h6 : 4 * (N - 1) ≤ N * (N - 1) := Nat.mul_le_mul_right _ (by omega)
    have h7 : 4 * (N - 1) / 2 ≤ N * (N - 1) / 2 := Nat.div_le_div_right h6
    omega
  have hCen : ∀ P : Sylow 2 G,
      T ≠ (center (P : Subgroup G)).map (P : Subgroup G).subtype := by
    intro P hP
    refine hSyl P fun p hp => ?_
    rw [← hC, mem_centralizer_iff]
    intro t ht
    rw [hP] at ht
    obtain ⟨c, hc, rfl⟩ := ht
    exact (congrArg Subtype.val (mem_center_iff.mp hc ⟨p, hp⟩)).symm
  rcases hL with ⟨m, s, hm, hs, hmodel⟩ | ⟨s, hs, hmodel⟩ | ⟨s, hso, hs3, hmodel⟩ |
    ⟨k, hk6, hk9, hk⟩ | hM | hM | hM
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨-, ⟨P, hP⟩, -⟩ := hstd.of_psl2 hmodel
      exact absurd hP.le (hSyl P)
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
      have hNm : N - 1 = s * (m - 1) :=
        Nat.pow_right_injective le_rfl (hcard.symm.trans (hstd.of_psl hm3 K hK e).1)
      have hle : N * (N - 1) / 2 ≤ s * (m * (m - 1) / 2) :=
        le_of_two_pow_dvd_card_statedProj hK (Nat.card_congr e.toEquiv ▸ h2)
      have e1 : N * (N - 1) / 2 * 2 = N * (N - 1) :=
        Nat.div_mul_cancel (Nat.even_mul_pred_self N).two_dvd
      have e2 : m * (m - 1) / 2 * 2 = m * (m - 1) :=
        Nat.div_mul_cancel (Nat.even_mul_pred_self m).two_dvd
      have h1 : N * (N - 1) ≤ m * (N - 1) := by
        calc N * (N - 1) = N * (N - 1) / 2 * 2 := e1.symm
          _ ≤ s * (m * (m - 1) / 2) * 2 := Nat.mul_le_mul_right 2 hle
          _ = m * (s * (m - 1)) := by rw [mul_assoc, e2]; ring
          _ = m * (N - 1) := by rw [hNm]
      have hNm' : N ≤ m := Nat.le_of_mul_le_mul_right h1 (by omega)
      have hs1 : s = 1 := by
        rcases Nat.lt_or_ge s 2 with h | h
        · omega
        · have h' : 2 * (m - 1) ≤ s * (m - 1) := Nat.mul_le_mul_right _ h
          omega
      subst hs1
      have hmN : m = N := by omega
      subst hmN
      exact (nonempty_mulEquiv_SL_of_card_two (K := K) (by rw [hK, pow_one]) _).map
        fun e' => e.trans e'
  · obtain ⟨-, ⟨P, hP⟩, -⟩ := hstd.of_psu3 hs hmodel
    exact absurd hP (hCen P)
  · obtain ⟨-, ⟨P, hP⟩, -⟩ := hstd.of_sz hso hs3 hmodel
    exact absurd hP (hCen P)
  · have h := hstd.card_alternating hk6 hk9 hk
    split_ifs at h <;> omega
  · have h := hstd.card_sporadic (Or.inl hM)
    omega
  · have h := hstd.card_sporadic (Or.inr (Or.inl hM))
    omega
  · have h := hstd.card_sporadic (Or.inr (Or.inr hM))
    omega

end CFSG.LargeExtraspecial.DW.D73
