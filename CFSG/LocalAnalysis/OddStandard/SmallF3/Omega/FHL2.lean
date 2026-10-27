module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR20
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHTransfer
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint
open CFSG.GH74.GLS
open CFSG.GH74.GLS.IVK
open CFSG.GH74.GLS.Th2.Obs

private theorem fh_not_three_dvd_card_fixed {F : Type} [Field F] [Finite F] {Y : Type} [Group Y]
    [Finite Y] (hF : L2Field F) (e : Y ≃* L2 F) (h3 : 3 ∣ Nat.card F) (x : MulAut Y)
    (hx : x ∈ innDiagSub e) (hx2 : orderOf x = 2) :
    ¬ 3 ∣ Nat.card ↥(fixedSubgroup Y x) := by
  have hFgt : 3 < Nat.card F := hF.2
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  have key : ∀ d : ℕ, ((d : ℤ) = Nat.card F - ε ∨ (d : ℤ) = Nat.card F + ε) →
      IsDihedralOrder ↥(fixedSubgroup Y x) d →
      ¬ 3 ∣ Nat.card ↥(fixedSubgroup Y x) := by
    intro d hd hdih
    obtain ⟨k, hkd, _hk2, ⟨ψ⟩⟩ := hdih
    have hcard : Nat.card ↥(fixedSubgroup Y x) = d := by
      rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
      omega
    rw [hcard]
    rintro ⟨m, hm⟩
    obtain ⟨c, hc⟩ := h3
    rcases hd with hd | hd <;> rcases hε1 with hε1 | hε1 <;> omega
  by_cases hin : x ∈ innAut Y
  · obtain ⟨u, rfl⟩ := hin
    have hu2 : orderOf u = 2 := by
      rw [← orderOf_conj_eq e u]
      exact hx2
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
      ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hdih : IsDihedralOrder ↥(fixedSubgroup Y (MulAut.conj u)) d := by
      rw [Proofs2.Lemma118.fixedSubgroup_conj u]
      exact (ivk_1_3a F hF Y e ε hε1 hε d hd u hu2).2.1
    exact key d (Or.inl hd) hdih
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
      ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by omega)⟩
    exact key d (Or.inr hd) ((ivk_1_3b F hF Y e ε hε1 hε d hd x hx hin hx2).2.1)

theorem fh_fixedO3Free_psl2
    {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (h : LieModel Y .PSL 2 3 f) : FHFixedO3Free Y := by
  rcases h with ⟨-, hadm, F, hFld, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · letI : Field F := hFld
    letI : Finite F := hFin
    obtain ⟨_hp, hf, -, _h2, h3⟩ := hadm
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have hf1 : f = 1 := by omega
      subst hf1
      exact h3 (by norm_num)
    have hFodd : Odd (Nat.card F) := by
      rw [hcard]
      exact Odd.pow (by norm_num)
    have hFgt : 3 < Nat.card F := by
      rw [hcard]
      have h2' : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num : 0 < 3) hf2
      have h9 : (9 : ℕ) ≤ 3 ^ f := by simpa using h2'
      omega
    have hF : L2Field F := ⟨hFodd, hFgt⟩
    have h3div : 3 ∣ Nat.card F := by
      rw [hcard]
      exact dvd_pow_self 3 (by omega : f ≠ 0)
    have hsimple : IsSimpleGroup Y := Proofs2.isSimpleGroup_of_l2 hF e
    have heven : Even (Nat.card Y) := Proofs2.even_card_of_l2 hF e
    intro σ hσ2 N hN3 hfix hnorm
    have hσ2' : σ ^ 2 = 1 := by rw [pow_two]; exact hσ2
    by_cases hσ1 : σ = 1
    · subst hσ1
      haveI : IsSimpleGroup Y := hsimple
      haveI : N.Normal := ⟨fun n hn g => by simpa using hnorm g rfl n hn⟩
      rcases Subgroup.Normal.eq_bot_or_eq_top N with hbot | htop
      · exact hbot
      · exfalso
        haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
        obtain ⟨n, hn⟩ := hN3.exists_card_eq
        have hYN : Nat.card Y = 3 ^ n := by
          rw [← Subgroup.card_top (G := Y), ← htop, hn]
        exact (Nat.not_even_iff_odd.mpr (Odd.pow (by norm_num))) (hYN ▸ heven)
    · have hσord : orderOf σ = 2 := orderOf_eq_prime hσ2' hσ1
      by_cases hin : σ ∈ innDiagSub e
      · have hnot3 : ¬ 3 ∣ Nat.card ↥(fixedSubgroup Y σ) :=
          fh_not_three_dvd_card_fixed hF e h3div σ hin hσord
        have hNle : N ≤ fixedSubgroup Y σ := fun x hx => hfix x hx
        have hdvd : Nat.card N ∣ Nat.card ↥(fixedSubgroup Y σ) :=
          Subgroup.card_dvd_of_le hNle
        haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
        obtain ⟨n, hn⟩ := hN3.exists_card_eq
        by_cases hn0 : n = 0
        · apply Subgroup.eq_bot_of_card_eq
          rw [hn, hn0, pow_zero]
        · exfalso
          have h3N : 3 ∣ Nat.card N := by
            rw [hn]
            exact dvd_pow_self 3 hn0
          exact hnot3 (h3N.trans hdvd)
      · have hpc : pPrimeCoreOf 2 (fixedSubgroup Y σ) = ⊥ :=
          pPrimeCoreOf_fixed_outer_eq_bot hF e σ hσ2' hin
        have hNle : N ≤ fixedSubgroup Y σ := fun x hx => hfix x hx
        have hle : N ≤ pPrimeCoreOf 2 (fixedSubgroup Y σ) := by
          have hDnorm : fixedSubgroup Y σ ≤ Subgroup.normalizer (N : Set Y) := by
            rw [Subgroup.le_normalizer_iff]
            intro y hy x hx
            exact hnorm y hy x hx
          have hnormal : (N.subgroupOf (fixedSubgroup Y σ)).Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hDnorm
          have hcop : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf (fixedSubgroup Y σ))) := by
            have hcardND : Nat.card ↥(N.subgroupOf (fixedSubgroup Y σ)) = Nat.card N :=
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
            rw [hcardND]
            obtain ⟨n, hn⟩ := hN3.exists_card_eq
            rw [hn]
            rcases Nat.eq_zero_or_pos n with hn0 | hnpos
            · rw [hn0, pow_zero]
              decide
            · rw [Nat.coprime_pow_right_iff hnpos]
              decide
          have hsub : N.subgroupOf (fixedSubgroup Y σ) ≤
              pPrimeCore 2 ↥(fixedSubgroup Y σ) := le_sSup ⟨hnormal, hcop⟩
          rw [pPrimeCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hNle]
          exact Subgroup.map_mono hsub
        rw [hpc] at hle
        exact le_bot_iff.mp hle
  all_goals exact absurd h0 (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
