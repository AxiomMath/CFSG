module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcUntw
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE7Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcDC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration
open scoped commutatorElement Matrix

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Finite F] {p : ℕ}

namespace E7

open E7Data

theorem commutator_eq_top : commutator ↥(adjointGroup Tag.E7 F) = ⊤ :=
  (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 F).1.commutator_eq_top

theorem wordMat_e7One : wordMat Tag.E7 e7OneWord = 1 := wordMat_nil Tag.E7

theorem wp_e7TwoWord_smul (u : Fin Tag.E7.rank → ℤ) : wp Tag.E7 e7TwoWord • u = -u := by
  rw [wp, wordProd_smul_eq_wordMat_mulVec, wordMat_e7TwoWord]
  simp [Matrix.neg_mulVec, Matrix.one_mulVec]

theorem five_seven_or_eleven_le (hp : p.Prime) (hp5 : 5 ≤ p) : p = 5 ∨ p = 7 ∨ 11 ≤ p := by
  rcases (by omega : p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ 11 ≤ p) with
    h | h | h | h | h | h | h
  · exact Or.inl h
  · subst h
    norm_num at hp
  · exact Or.inr (Or.inl h)
  · subst h
    norm_num at hp
  · subst h
    norm_num at hp
  · subst h
    norm_num at hp
  · exact Or.inr (Or.inr h)

theorem wcOn_pair [Fact p.Prime] (hp11 : 11 ≤ p) (hpq : ¬ p ∣ Nat.card F) {e : ℕ}
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = e) (he12 : e = 1 ∨ e = 2) :
    WCOn p (adjointGroup Tag.E7 F) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 < p := by omega
  rcases he12 with rfl | rfl
  ·
    have hF : SylowFrame Tag.E7 F p (wp Tag.E7 e7OneWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inl rfl)) F hp hp3 hpq e7OneWord [1, 1, 1, 1, 1, 1, 1]
        e7One_charpoly e7One_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_5040 hp hp11 (by decide)) (by decide) commutator_eq_top
    have hc : ∀ x : List (Fin Tag.E7.rank),
        wordMat Tag.E7 x * wordMat Tag.E7 e7OneWord = wordMat Tag.E7 e7OneWord * wordMat Tag.E7 x := by
      intro x
      rw [wordMat_e7One, mul_one, one_mul]
    exact hF.wcOn_dcw2_cert (a₁ := u1a) (b₁ := u1b) (c₁ := u1c) (d₁ := u1d) (a₂ := u2a)
      (b₂ := u2b) (c₂ := u2c) (d₂ := u2d) (hc _) (hc _) (hc _) (hc _) (hc _) (hc _) (hc _) (hc _)
      pair_cert
  ·
    have hF : SylowFrame Tag.E7 F p (wp Tag.E7 e7TwoWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inl rfl)) F hp hp3 hpq e7TwoWord [2, 2, 2, 2, 2, 2, 2]
        e7Two_charpoly e7Two_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_5040 hp hp11 (by decide)) (by decide) commutator_eq_top
    have hc : ∀ x : List (Fin Tag.E7.rank),
        wordMat Tag.E7 x * wordMat Tag.E7 e7TwoWord = wordMat Tag.E7 e7TwoWord * wordMat Tag.E7 x := by
      intro x
      rw [wordMat_e7TwoWord]
      simp
    exact hF.wcOn_dcw2_cert (a₁ := u1a) (b₁ := u1b) (c₁ := u1c) (d₁ := u1d) (a₂ := u2a)
      (b₂ := u2b) (c₂ := u2c) (d₂ := u2d) (hc _) (hc _) (hc _) (hc _) (hc _) (hc _) (hc _) (hc _)
      pair_cert

theorem wcOn_toral [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F) {e : ℕ}
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = e) (hecases : e = 3 ∨ e = 4 ∨ e = 6) :
    WCOn p (adjointGroup Tag.E7 F) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  have hz1 : weylMat (1 : WeylGroup Tag.E7) =
      (1 : ℤ) • (1 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ) := by
    rw [weylMat_one, one_smul]
  rcases hecases with rfl | rfl | rfl
  ·
    have hF : SylowFrame Tag.E7 F p (wp Tag.E7 e7ThreeWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inl rfl)) F hp hp3 hpq e7ThreeWord [1, 3, 3, 3]
        e7Three_charpoly e7Three_pow he (not_dvd_of_blocks_small hp5 (by decide))
        (not_dvd_div_of_12 hp hp5 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r3a) (b := r3b) (c := r3c) (d := r3d) (z := 1) (s := 1) (k := 2)
      hp2 hpq he hz1 (Or.inl rfl) r3_comm_a r3_comm_b r3_comm_c r3_comm_d r3_dc
      (Or.inl ⟨rfl, by omega⟩)
  ·
    have hF : SylowFrame Tag.E7 F p (wp Tag.E7 e7FourWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inl rfl)) F hp hp3 hpq e7FourWord [1, 1, 1, 4, 4]
        e7Four_charpoly e7Four_pow he (not_dvd_of_blocks_small hp5 (by decide))
        (not_dvd_div_of_12 hp hp5 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r4a) (b := r4b) (c := r4c) (d := r4d) (z := 1) (s := 1) (k := 2)
      hp2 hpq he hz1 (Or.inl rfl) r4_comm_a r4_comm_b r4_comm_c r4_comm_d r4_dc
      (Or.inl ⟨rfl, by omega⟩)
  ·
    have hF : SylowFrame Tag.E7 F p (wp Tag.E7 e7SixWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inl rfl)) F hp hp3 hpq e7SixWord [2, 6, 6, 6]
        e7Six_charpoly e7Six_pow he (not_dvd_of_blocks_small hp5 (by decide))
        (not_dvd_div_of_12 hp hp5 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r6a) (b := r6b) (c := r6c) (d := r6d) (z := 1) (s := 1) (k := 4)
      hp2 hpq he hz1 (Or.inl rfl) r6_comm_a r6_comm_b r6_comm_c r6_comm_d r6_dc
      (Or.inl ⟨rfl, by omega⟩)

theorem wcOn_small_one [Fact p.Prime] (hpq : ¬ p ∣ Nat.card F) (hd : p ∣ Nat.card F - 1)
    {X Y S : List (Fin Tag.E7.rank)} (j : Fin Tag.E7.rank)
    (hv : wordMat Tag.E7 (cw X Y) ^ p = 1)
    (hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.E7.rank => if i = 0 then (1 : ℤ) else 0) i *
      ((wordMat Tag.E7 S.reverse - 1) * (wordMat Tag.E7 (cw X Y).reverse - 1)) i j) :
    WCOn p (adjointGroup Tag.E7 F) :=
  (weakFrame_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) F 1 commutator_eq_top).wcOn_noncomm_one hpq hd
    (wp_cw_pow_eq_one hv) _ j (by
      rw [weylMat_wp_inv, weylMat_cw_inv]
      exact hj)

theorem wcOn_small_two [Fact p.Prime] (hpq : ¬ p ∣ Nat.card F) (hd : p ∣ Nat.card F + 1)
    {X Y S : List (Fin Tag.E7.rank)} (j : Fin Tag.E7.rank)
    (hv : wordMat Tag.E7 (cw X Y) ^ p = 1)
    (hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.E7.rank => if i = 0 then (1 : ℤ) else 0) i *
      ((wordMat Tag.E7 S.reverse - 1) * (wordMat Tag.E7 (cw X Y).reverse - 1)) i j) :
    WCOn p (adjointGroup Tag.E7 F) :=
  (weakFrame_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) F (wp Tag.E7 e7TwoWord)
    commutator_eq_top).wcOn_noncomm_neg wp_e7TwoWord_smul hpq hd (wp_cw_pow_eq_one hv) _ j (by
      rw [weylMat_wp_inv, weylMat_cw_inv]
      exact hj)

theorem wcOn_small [Fact p.Prime] (hp : p = 3 ∨ p = 5 ∨ p = 7) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 1 ∨ orderOf ((Nat.card F : ℕ) : ZMod p) = 2) :
    WCOn p (adjointGroup Tag.E7 F) := by
  have hp' : p.Prime := Fact.out
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases he with he | he
  · have hd := dvd_sub_one_of_orderOf_eq_one' (by omega) he
    rcases hp with rfl | rfl | rfl
    · exact wcOn_small_one (X := [0]) (Y := [2]) (S := [0]) hpq hd 3 (by decide +kernel)
        (by decide +kernel)
    · exact wcOn_small_one (X := [0, 3]) (Y := [2, 4]) (S := [0]) hpq hd 0 (by decide +kernel)
        (by decide +kernel)
    · exact wcOn_small_one (X := [0, 3, 5]) (Y := [2, 4, 6]) (S := [0]) hpq hd 0
        (by decide +kernel) (by decide +kernel)
  · have hd := dvd_add_one_of_orderOf_eq_two' hp' he
    rcases hp with rfl | rfl | rfl
    · exact wcOn_small_two (X := [0]) (Y := [2]) (S := [0]) hpq hd 3 (by decide +kernel)
        (by decide +kernel)
    · exact wcOn_small_two (X := [0, 3]) (Y := [2, 4]) (S := [0]) hpq hd 0 (by decide +kernel)
        (by decide +kernel)
    · exact wcOn_small_two (X := [0, 3, 5]) (Y := [2, 4, 6]) (S := [0]) hpq hd 0
        (by decide +kernel) (by decide +kernel)

theorem wcOn_adjoint [Fact p.Prime] (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F) :
    WCOn p (adjointGroup Tag.E7 F) := by
  have hp : p.Prime := Fact.out
  by_cases hcnt : degCount Tag.E7 (orderOf ((Nat.card F : ℕ) : ZMod p)) ≤ 1
  · exact WCOn.of_rankLE1 (rankLE1_E7 F hp hpq hcnt)
  · push Not at hcnt
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
    rw [he] at hcnt
    have hlt : e < p := CFSG.LieType.SeitzGeneration.orderOf_lt_prime hp hpq he
    have he30 : e ≤ 30 := le_thirty_of_degCount_pos (τ := Tag.E7) (by simp) (by omega)
    have hecases : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
      interval_cases e <;> first | omega | exact absurd hcnt (by decide)
    rcases eq_three_or_five_le' hp hp2 with hp3 | hp5
    · refine wcOn_small (Or.inl hp3) hpq ?_
      rw [he]
      omega
    · by_cases he12 : e = 1 ∨ e = 2
      · rcases five_seven_or_eleven_le hp hp5 with h5 | h7 | h11
        · exact wcOn_small (Or.inr (Or.inl h5)) hpq (by rw [he]; exact he12)
        · exact wcOn_small (Or.inr (Or.inr h7)) hpq (by rw [he]; exact he12)
        · exact wcOn_pair h11 hpq he he12
      · refine wcOn_toral hp5 hpq he ?_
        omega

end E7

theorem wcOn_e7_model {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (h : UntwistedChevalleyModel K Tag.E7 (ℓ ^ f)) : WCOn p K :=
  wcOn_of_untwisted_model hℓ hpℓ h fun F _ _ _ hpq => E7.wcOn_adjoint hp2 hpq

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
