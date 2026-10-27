module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclKLeft
public import CFSG.Quasithin.Background.C35Insp
public import CFSG.Quasithin.Background.C35NatFF
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329
public import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.KGC31 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open scoped IsMulCommutative

private theorem pslTwo_card_ne_small {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n * (4 ^ n - 1) ≠ 168 ∧ 2 ^ n * (4 ^ n - 1) ≠ 20160 ∧
      2 ^ n * (4 ^ n - 1) ≠ 6048 := by
  have hbound : ∀ m : ℕ, 2 ^ n * (4 ^ n - 1) = m → m ≤ 20160 → n ≤ 14 := by
    intro m hm hmle
    have h1 : 1 ≤ 4 ^ n - 1 := by
      have : 4 ^ 2 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      norm_num at this ⊢
      omega
    have h2n : 2 ^ n ≤ m := by
      rw [← hm]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have h20160 : 2 ^ n ≤ 20160 := h2n.trans hmle
    by_contra h15
    have hpow : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hpow
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hnle := hbound 168 h (by norm_num)
    interval_cases n <;> norm_num at h
  · intro h
    have hnle := hbound 20160 h le_rfl
    interval_cases n <;> norm_num at h
  · intro h
    have hnle := hbound 6048 h (by norm_num)
    interval_cases n <;> norm_num at h

theorem KConfig.conclKLeft_of_c35Concl1 {X : Type} [Group X] [Finite X] {L V MK : Subgroup X}
    (h : KConfig X L V MK) {Y : Subgroup X}
    (hc : CFSG.Quasithin.C35Concl1 (⊤ : Subgroup X) Y L V) :
    ConclKLeft X L V MK := by
  obtain ⟨n, -, -, hpsl, hnat⟩ := hc
  obtain ⟨-, hn1, -, hne, -⟩ := hpsl.1
  have hn : 2 ≤ n := by
    by_contra h
    have hn1' : n = 1 := by omega
    subst hn1'
    exact hne rfl
  have hQ : CFSG.IsQuasisimple (ModO2 L) := by
    refine isQuasisimple_of_isPSL hpsl (Nat.card_pos.ne') ?_
    intro hp
    have hcard : Nat.card (ModO2 L) = 2 ^ n * (4 ^ n - 1) :=
      CFSG.Quasithin.F420.card_of_statedPSL_two_two hpsl
    have h2dvd : 2 ∣ Nat.card (ModO2 L) := by
      rw [hcard]
      refine dvd_mul_of_dvd_left ?_ _
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [hk, pow_succ]
      exact dvd_mul_of_dvd_right (dvd_refl 2) _
    have hge : 2 < Nat.card (ModO2 L) := by
      rw [hcard]
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h15 : 15 ≤ 4 ^ n - 1 := by
        have : 16 ≤ 4 ^ n := by
          calc 16 = 4 ^ 2 := by norm_num
            _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
      have h60 : 60 ≤ 2 ^ n * (4 ^ n - 1) := by
        calc 60 = 4 * 15 := by norm_num
          _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h4 h15
      omega
    have hodd : Odd (Nat.card (ModO2 L)) := hp.odd_of_ne_two (by omega)
    have heven : Even (Nat.card (ModO2 L)) := even_iff_two_dvd.mpr h2dvd
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hshape : Shape443 (ModO2 L) := Or.inl ⟨n, hn, Or.inl ⟨by decide, hpsl⟩⟩
  have hN : (CFSG.pCore 2 ↥L).map L.subtype ≤ Subgroup.centralizer (V : Set X) := by
    have hEq : (CFSG.pCore 2 ↥L).map L.subtype = pCoreOf 2 L := by
      rw [← Hex.pCoreOf_subgroupOf']
      unfold pCoreOf
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)]
    rw [hEq]
    exact h.pCoreOf_le
  letI : IsMulCommutative ↥V := h.elemAbelian.1
  have hFF : IsFFModule (V := ↥V) (autOn L V) := by
    rcases hnat with ⟨F, hFld, hFintype, hFcard, hsec⟩ |
      ⟨-, F, hFld, hFintype, hFcard, hsec⟩
    · letI := hFld
      letI := hFintype
      have h2n : (2 : F) ^ n = 0 := by
        have h := FiniteField.cast_card_eq_zero F
        simpa [hFcard] using h
      have h2 : (2 : F) = 0 := (pow_eq_zero_iff (by omega : n ≠ 0)).1 h2n
      have hW : V ⊓ centerOf (⊤ : Subgroup X) ≤ Subgroup.centralizer (L : Set X) :=
        inf_le_right.trans (inf_le_right.trans
          (Subgroup.centralizer_le (le_top : L ≤ (⊤ : Subgroup X))))
      exact CFSG.Quasithin.isFFModule_autOn_of_isNaturalSection_two h2 h.elemAbelian.2 hW hN hsec
    · letI := hFld
      letI := hFintype
      have h2n : (2 : F) ^ n = 0 := by
        have h := FiniteField.cast_card_eq_zero F
        simpa [hFcard] using h
      have h2 : (2 : F) = 0 := (pow_eq_zero_iff (by omega : n ≠ 0)).1 h2n
      have hW : V ⊓ Subgroup.centralizer (L : Set X) ≤ Subgroup.centralizer (L : Set X) :=
        inf_le_right
      exact CFSG.Quasithin.isFFModule_autOn_of_isNaturalSection_two h2 h.elemAbelian.2 hW hN hsec
  have hFFN : IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set X)) V) :=
    CFSG.Quasithin.H13.Prop329.isFFModule_of_le (AutOn.autOn_mono h.le_normalizer) hFF
  have hcardQ : Nat.card (ModO2 L) = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hpsl
  unfold ConclKLeft
  refine ⟨hQ, hshape, Or.inl ⟨⟨h.elemAbelian.1, hFFN⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h168 := LieModel.card_psl_three_two h3
    exact absurd (hcardQ.symm.trans h168) (pslTwo_card_ne_small hn).1
  ·
    intro h4
    have h20160 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    exact absurd (hcardQ.symm.trans h20160) (pslTwo_card_ne_small hn).2.1
  ·
    rintro ⟨-, hcent, -⟩
    rw [CFSG.Quasithin.F420.center_eq_bot_of_statedPSL hpsl, Subgroup.card_bot] at hcent
    omega
  ·
    intro hU _
    have h6048 := LieModel.card_psu_three_three hU
    exact absurd (hcardQ.symm.trans h6048) (pslTwo_card_ne_small hn).2.2

end CFSG.SectionRank.QTK.Insp443

end
