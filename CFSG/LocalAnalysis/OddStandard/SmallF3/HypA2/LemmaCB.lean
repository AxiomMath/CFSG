module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Cl1Bridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SectionCard

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

private theorem exists_pow_two_of_two_pow_disj {c d : ℕ} (hd : ∃ j : ℕ, d = 2 ^ j)
    (h : c = 2 * d ∨ d = c ∨ d = 2 * c ∨ d = 4 * c ∨ d = 3 * c) :
    ∃ j : ℕ, c = 2 ^ j := by
  obtain ⟨j, rfl⟩ := hd
  rcases h with h | h | h | h | h
  · exact ⟨j + 1, by rw [h, pow_succ]; ring⟩
  · exact ⟨j, by rw [← h]⟩
  · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show c ∣ 2 ^ j from ⟨2, by rw [h, Nat.mul_comm]⟩)
    exact ⟨k, hk⟩
  · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show c ∣ 2 ^ j from ⟨4, by rw [h, Nat.mul_comm]⟩)
    exact ⟨k, hk⟩
  · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show c ∣ 2 ^ j from ⟨3, by rw [h, Nat.mul_comm]⟩)
    exact ⟨k, hk⟩

private theorem card_quot_center_le {G : Type} [Group G] [Finite G] :
    Nat.card (G ⧸ center G) ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center G))

private theorem ordD_four_three : CFSG.Open.ordD 4 (3 ^ 1) = 4952179814400 := by
  decide

private theorem ordTwistedD_four_three : CFSG.Open.ordTwistedD 4 (3 ^ 1) = 10151968619520 := by
  decide

private theorem card_lieModel_psl_two_two_three {G : Type} [Group G]
    (h : LieModel G .PSL 2 2 3) : Nat.card G = 504 := by
  rw [GH74.card_of_lieModel_PSL (G := G) (n := 2) (p := 2) (f := 3) (by norm_num) h]
  decide

theorem inS_of_properFixedComp_B (hC : ClosureLeaves) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : Catalog S) {σ : MulAut S} {P : Subgroup S} (hP : ProperFixedComp σ P)
    (h : InSB (P ⧸ center P)) :
    InS S ∧ Nat.card (P ⧸ center P) < Nat.card S := by
  obtain ⟨hch3, hb, hmod, hpow, hnplus, hnminus⟩ := h
  have hPtop : P < ⊤ := lt_of_le_of_ne (le_trans hP.2.1 le_top) hP.2.2.1
  have hPne : P ≠ ⊤ := hP.2.2.1
  have hlt : Nat.card (P ⧸ center P) < Nat.card S := by
    have hidx1 : P.index ≠ 1 := fun h1 => hPne ((Subgroup.index_eq_one).mp h1)
    have hidx0 : P.index ≠ 0 := P.index_ne_zero_of_finite
    have hidx2 : 2 ≤ P.index := by omega
    have hmul : Nat.card P * P.index = Nat.card S := P.card_mul_index
    have hstep : Nat.card P * 2 ≤ Nat.card S := by
      rw [← hmul]
      exact Nat.mul_le_mul_left _ hidx2
    have hquot : Nat.card (P ⧸ center P) ≤ Nat.card P := card_quot_center_le
    have hpos : 0 < Nat.card P := Nat.card_pos
    omega
  have hbS : classSBound ≤ Nat.card S := le_trans hb (le_of_lt hlt)
  have h20160S : 20160 ≤ Nat.card S := by
    have h20160b : 20160 ≤ classSBound := by norm_num [classSBound]
    omega
  by_cases hcaseA : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ HarrisLit.IsSimpleChevalleyOver r S
  ·
    have hnoPSL : ¬ LieModel S .PSL 3 2 2 := by
      intro hpsl
      have hcardS : Nat.card S = 20160 := card_lieModel_psl_three_two_two hpsl
      have hge : classSBound ≤ Nat.card S := hbS
      rw [hcardS] at hge
      norm_num [classSBound] at hge
    have hnoHe : ¬ NativeSporadic.IsSporadic S .He := by
      intro hsp
      rcases hC.cl3 S (Or.inr (Or.inl hsp)) σ P hP with hsmall | hmodel
      · have hbQ : classSBound ≤ Nat.card (P ⧸ center P) := hb
        norm_num [classSBound] at hbQ
        omega
      · have hcardQ : Nat.card (P ⧸ center P) = 20160 :=
          card_lieModel_psl_three_two_two hmodel
        have hbQ : classSBound ≤ Nat.card (P ⧸ center P) := hb
        rw [hcardQ] at hbQ
        norm_num [classSBound] at hbQ
    have hnoM12 : ¬ NativeSporadic.IsSporadic S .M12 := by
      intro hsp
      rcases hC.cl3 S (Or.inr (Or.inr (Or.inl hsp))) σ P hP with hsmall | hmodel
      · have hbQ : classSBound ≤ Nat.card (P ⧸ center P) := hb
        norm_num [classSBound] at hbQ
        omega
      · have hcardQ : Nat.card (P ⧸ center P) = 20160 :=
          card_lieModel_psl_three_two_two hmodel
        have hbQ : classSBound ≤ Nat.card (P ⧸ center P) := hb
        rw [hcardQ] at hbQ
        norm_num [classSBound] at hbQ
    have hnoJ2 : ¬ NativeSporadic.IsSporadic S .J2 := by
      intro hsp
      rcases hC.cl3 S (Or.inr (Or.inr (Or.inr hsp))) σ P hP with hsmall | hmodel
      · have hbQ : classSBound ≤ Nat.card (P ⧸ center P) := hb
        norm_num [classSBound] at hbQ
        omega
      · have hcardQ : Nat.card (P ⧸ center P) = 20160 :=
          card_lieModel_psl_three_two_two hmodel
        have hbQ : classSBound ≤ Nat.card (P ⧸ center P) := hb
        rw [hcardQ] at hbQ
        norm_num [classSBound] at hbQ
    have hSA : InSA S := by
      unfold InSA
      exact ⟨hS, h20160S, hcaseA, hnoPSL, hnoHe, hnoM12, hnoJ2⟩
    exact ⟨Or.inl hSA, hlt⟩
  ·
    push Not at hcaseA
    obtain ⟨r, hr, hr2, hrS⟩ := hcaseA
    rcases cl1_of_gls3 hC.cl1 hP hr hr2 hrS with hchev | h504
    ·
      have hr3 : r = 3 := by
        by_contra hr3
        have hle : Nat.card (P ⧸ center P) ≤ 25920 :=
          hC.cl5 (P ⧸ center P) r hr hr2 hr3 hch3 hchev
        have hbQ : classSBound ≤ Nat.card (P ⧸ center P) := hb
        norm_num [classSBound] at hbQ
        omega
      have hchS : HarrisLit.IsSimpleChevalleyOver 3 S := by
        rw [← hr3]
        exact hrS
      obtain ⟨j', τ', n', hm'⟩ := hmod
      obtain ⟨τ, n, c, hmS⟩ := hchS
      have hmodelS : ∃ (j : ℕ) (τ : CFSG.Open.StatedLieTag) (n : ℕ),
          LieModel S τ n 3 (2 ^ j) := by
        have hrel := hC.cl2 S σ P hP τ n c hmS τ' n' (2 ^ j') hm'
        obtain ⟨j, hc⟩ := exists_pow_two_of_two_pow_disj ⟨j', rfl⟩ hrel
        exact ⟨j, τ, n, hc ▸ hmS⟩
      have hpowS : ∀ e : ℕ, LieModel S .PSL 2 3 e → ∃ j : ℕ, e = 2 ^ j := by
        intro e he
        have hrel := hC.cl2 S σ P hP .PSL 2 e he τ' n' (2 ^ j') hm'
        exact exists_pow_two_of_two_pow_disj ⟨j', rfl⟩ hrel
      have hnplusS : ¬ LieModel S .POmegaPlus 4 3 1 := by
        intro hp
        have hcardS : Nat.card S = CFSG.Open.ordD 4 (3 ^ 1) :=
          (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := S)
            (t := .POmegaPlus) (n := 4) (p := 3) (f := 1) (by norm_num)
            (GH74.statedClassicalModel_of_lieModel (G := S) (t := .POmegaPlus) (n := 4)
              (p := 3) (f := 1) (by norm_num) hp)).2.2.2.2.1 rfl
        have hidx : 36 ≤ P.index := (hC.cl4 S P hPne).1 hp
        have hmul : Nat.card P * P.index = Nat.card S := P.card_mul_index
        have hstep : Nat.card P * 36 ≤ Nat.card S := by
          rw [← hmul]
          exact Nat.mul_le_mul_left _ hidx
        have hquot : Nat.card (P ⧸ center P) ≤ Nat.card P := card_quot_center_le
        have hQ : Nat.card (P ⧸ center P) * 36 ≤ Nat.card S :=
          (Nat.mul_le_mul_right 36 hquot).trans hstep
        rw [hcardS, ordD_four_three] at hQ
        have hbQ : 141214764960 ≤ Nat.card (P ⧸ center P) := by
          simpa [classSBound] using hb
        omega
      have hnminusS : ¬ LieModel S .POmegaMinus 4 3 1 := by
        intro hp
        have hcardS : Nat.card S = CFSG.Open.ordTwistedD 4 (3 ^ 1) :=
          (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := S)
            (t := .POmegaMinus) (n := 4) (p := 3) (f := 1) (by norm_num)
            (GH74.statedClassicalModel_of_lieModel (G := S) (t := .POmegaMinus) (n := 4)
              (p := 3) (f := 1) (by norm_num) hp)).2.2.2.2.2 rfl
        have hidx : 72 ≤ P.index := (hC.cl4 S P hPne).2 hp
        have hmul : Nat.card P * P.index = Nat.card S := P.card_mul_index
        have hstep : Nat.card P * 72 ≤ Nat.card S := by
          rw [← hmul]
          exact Nat.mul_le_mul_left _ hidx
        have hquot : Nat.card (P ⧸ center P) ≤ Nat.card P := card_quot_center_le
        have hQ : Nat.card (P ⧸ center P) * 72 ≤ Nat.card S :=
          (Nat.mul_le_mul_right 72 hquot).trans hstep
        rw [hcardS, ordTwistedD_four_three] at hQ
        have hbQ : 141214764960 ≤ Nat.card (P ⧸ center P) := by
          simpa [classSBound] using hb
        omega
      have hSB : InSB S := by
        unfold InSB
        exact ⟨⟨τ, n, c, hmS⟩, hbS, hmodelS, hpowS, hnplusS, hnminusS⟩
      exact ⟨Or.inr hSB, hlt⟩
    ·
      have hcardQ : Nat.card (P ⧸ center P) = 504 := card_lieModel_psl_two_two_three h504
      have hbQ : classSBound ≤ Nat.card (P ⧸ center P) := hb
      rw [hcardQ] at hbQ
      norm_num [classSBound] at hbQ

end CFSG.OddStandard.SmallF3.HypA2
