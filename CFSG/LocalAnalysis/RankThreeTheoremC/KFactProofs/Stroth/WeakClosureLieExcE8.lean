module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcUntw
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE8Data1
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE8Data2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE8Data3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE8Data4
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

namespace E8

open E8Data

theorem commutator_eq_top : commutator ↥(adjointGroup Tag.E8 F) = ⊤ :=
  (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 F).1.commutator_eq_top

theorem wordMat_e8One : wordMat Tag.E8 e8OneWord = 1 := wordMat_nil Tag.E8

theorem wp_e8TwoWord_smul (u : Fin Tag.E8.rank → ℤ) : wp Tag.E8 e8TwoWord • u = -u := by
  rw [wp, wordProd_smul_eq_wordMat_mulVec, wordMat_e8TwoWord]
  simp [Matrix.neg_mulVec, Matrix.one_mulVec]

theorem weylMat_wp_e8TwoWord :
    weylMat (wp Tag.E8 e8TwoWord) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  rw [weylMat_wp, wordMat_e8TwoWord]

theorem wcOn_toral [Fact p.Prime] (hp7 : 7 ≤ p) (hpq : ¬ p ∣ Nat.card F) {e : ℕ}
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = e)
    (hecases : e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12) :
    WCOn p (adjointGroup Tag.E8 F) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  rcases hecases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8ThreeWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8ThreeWord [3, 3, 3, 3]
        e8Three_charpoly e8Three_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_720 hp hp7 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r3a) (b := r3b) (c := r3c) (d := r3d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) r3_comm_a r3_comm_b
      r3_comm_c r3_comm_d (by rw [pow_zero]; exact r3_dc) (Or.inr ⟨rfl, dvd_zero _⟩)
  · have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8FourWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8FourWord [4, 4, 4, 4]
        e8Four_charpoly e8Four_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_720 hp hp7 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r4a) (b := r4b) (c := r4c) (d := r4d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) r4_comm_a r4_comm_b
      r4_comm_c r4_comm_d (by rw [pow_zero]; exact r4_dc) (Or.inr ⟨rfl, dvd_zero _⟩)
  · have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8FiveWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8FiveWord [5, 5]
        e8Five_charpoly e8Five_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_720 hp hp7 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r5a) (b := r5b) (c := r5c) (d := r5d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) r5_comm_a r5_comm_b
      r5_comm_c r5_comm_d (by rw [pow_zero]; exact r5_dc) (Or.inr ⟨rfl, dvd_zero _⟩)
  · have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8SixWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8SixWord [6, 6, 6, 6]
        e8Six_charpoly e8Six_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_720 hp hp7 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r6a) (b := r6b) (c := r6c) (d := r6d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) r6_comm_a r6_comm_b
      r6_comm_c r6_comm_d (by rw [pow_zero]; exact r6_dc) (Or.inr ⟨rfl, dvd_zero _⟩)
  · have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8EightWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8EightWord [8, 8]
        e8Eight_charpoly e8Eight_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_720 hp hp7 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r8a) (b := r8b) (c := r8c) (d := r8d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) r8_comm_a r8_comm_b
      r8_comm_c r8_comm_d (by rw [pow_zero]; exact r8_dc) (Or.inr ⟨rfl, dvd_zero _⟩)
  · have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8TenWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8TenWord [10, 10]
        e8Ten_charpoly e8Ten_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_720 hp hp7 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r10a) (b := r10b) (c := r10c) (d := r10d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) r10_comm_a r10_comm_b
      r10_comm_c r10_comm_d (by rw [pow_zero]; exact r10_dc) (Or.inr ⟨rfl, dvd_zero _⟩)
  · have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8TwelveWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8TwelveWord [12, 12]
        e8Twelve_charpoly e8Twelve_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_720 hp hp7 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r12a) (b := r12b) (c := r12c) (d := r12d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) r12_comm_a r12_comm_b
      r12_comm_c r12_comm_d (by rw [pow_zero]; exact r12_dc) (Or.inr ⟨rfl, dvd_zero _⟩)

theorem wcOn_one_two [Fact p.Prime] (hp11 : 11 ≤ p) (hpq : ¬ p ∣ Nat.card F) {e : ℕ}
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = e) (he12 : e = 1 ∨ e = 2) :
    WCOn p (adjointGroup Tag.E8 F) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  rcases he12 with rfl | rfl
  ·
    have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8OneWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8OneWord [1, 1, 1, 1, 1, 1, 1, 1]
        e8One_charpoly e8One_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_5040 hp hp11 (by decide)) (by decide) commutator_eq_top
    have hc : ∀ x : List (Fin Tag.E8.rank),
        wordMat Tag.E8 x * wordMat Tag.E8 e8OneWord = wordMat Tag.E8 e8OneWord * wordMat Tag.E8 x := by
      intro x
      rw [wordMat_e8One, mul_one, one_mul]
    exact hF.wcOn_dcw (a := q12a) (b := q12b) (c := q12c) (d := q12d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) (hc _) (hc _) (hc _) (hc _)
      (by rw [pow_zero]; exact q12_dc) (Or.inr ⟨rfl, dvd_zero _⟩)
  ·
    have hF : SylowFrame Tag.E8 F p (wp Tag.E8 e8TwoWord) :=
      sylowFrame_untw_blocks (Or.inr (Or.inr rfl)) F hp hp3 hpq e8TwoWord [2, 2, 2, 2, 2, 2, 2, 2]
        e8Two_charpoly e8Two_pow he (fun d hd hde => absurd (by simpa using hd) hde)
        (not_dvd_div_of_5040 hp hp11 (by decide)) (by decide) commutator_eq_top
    have hc : ∀ x : List (Fin Tag.E8.rank),
        wordMat Tag.E8 x * wordMat Tag.E8 e8TwoWord = wordMat Tag.E8 e8TwoWord * wordMat Tag.E8 x := by
      intro x
      rw [wordMat_e8TwoWord]
      simp
    exact hF.wcOn_dcw (a := q12a) (b := q12b) (c := q12c) (d := q12d) (z := wp Tag.E8 e8TwoWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_e8TwoWord (Or.inr rfl) (hc _) (hc _) (hc _) (hc _)
      (by rw [pow_zero]; exact q12_dc) (Or.inr ⟨rfl, dvd_zero _⟩)

theorem wcOn_small_one [Fact p.Prime] (hpq : ¬ p ∣ Nat.card F) (hd : p ∣ Nat.card F - 1)
    {X Y S : List (Fin Tag.E8.rank)} (j : Fin Tag.E8.rank)
    (hv : wordMat Tag.E8 (cw X Y) ^ p = 1)
    (hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.E8.rank => if i = 0 then (1 : ℤ) else 0) i *
      ((wordMat Tag.E8 S.reverse - 1) * (wordMat Tag.E8 (cw X Y).reverse - 1)) i j) :
    WCOn p (adjointGroup Tag.E8 F) :=
  (weakFrame_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) F 1 commutator_eq_top).wcOn_noncomm_one hpq hd
    (wp_cw_pow_eq_one hv) _ j (by
      rw [weylMat_wp_inv, weylMat_cw_inv]
      exact hj)

theorem wcOn_small_two [Fact p.Prime] (hpq : ¬ p ∣ Nat.card F) (hd : p ∣ Nat.card F + 1)
    {X Y S : List (Fin Tag.E8.rank)} (j : Fin Tag.E8.rank)
    (hv : wordMat Tag.E8 (cw X Y) ^ p = 1)
    (hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.E8.rank => if i = 0 then (1 : ℤ) else 0) i *
      ((wordMat Tag.E8 S.reverse - 1) * (wordMat Tag.E8 (cw X Y).reverse - 1)) i j) :
    WCOn p (adjointGroup Tag.E8 F) :=
  (weakFrame_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) F (wp Tag.E8 e8TwoWord)
    commutator_eq_top).wcOn_noncomm_neg wp_e8TwoWord_smul hpq hd (wp_cw_pow_eq_one hv) _ j (by
      rw [weylMat_wp_inv, weylMat_cw_inv]
      exact hj)

theorem wcOn_small [Fact p.Prime] (hp : p = 3 ∨ p = 5 ∨ p = 7) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 1 ∨ orderOf ((Nat.card F : ℕ) : ZMod p) = 2) :
    WCOn p (adjointGroup Tag.E8 F) := by
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

theorem wcOn_four_five [Fact p.Prime] (hp5 : p = 5) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 4) : WCOn p (adjointGroup Tag.E8 F) := by
  have hp : p.Prime := Fact.out
  have hd := dvd_phi4_of_orderOf' hp he
  subst hp5
  have hmod : Nat.card F % 5 = 2 ∨ Nat.card F % 5 = 3 := by
    have h1 : (Nat.card F ^ 2 + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd hd
    have h2 : Nat.card F ^ 2 % 5 = (Nat.card F % 5) ^ 2 % 5 := Nat.pow_mod _ _ _
    have h3 : Nat.card F % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : Nat.card F % 5 <;> omega
  have hF := weakFrame_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) F (wp Tag.E8 e8FourWord)
    commutator_eq_top
  have hX := wp_mem_centralizer (a := sx) (w := e8FourWord) sx_comm
  have hY := wp_mem_centralizer (a := sy) (w := e8FourWord) sy_comm
  have hS := wp_mem_centralizer (a := ss) (w := e8FourWord) ss_comm
  have hv : ⁅wp Tag.E8 sx, wp Tag.E8 sy⁆ ^ 5 = 1 := wp_cw_pow_eq_one s4_pow
  rcases hmod with h | h
  · exact hF.wcOn_noncomm_vec hpq hX hY hS hv (q₀ := 2) (by unfold Int.ModEq; omega)
      (fun i : Fin Tag.E8.rank => (![2, -2, 0, 2, 0, 0, 0, 1] : Fin 8 → ℤ) i) s4_hvec2 0 s4_hj2
  · exact hF.wcOn_noncomm_vec hpq hX hY hS hv (q₀ := 3) (by unfold Int.ModEq; omega)
      (fun i : Fin Tag.E8.rank => (![1, 2, 0, -2, 0, 0, 0, 1] : Fin 8 → ℤ) i) s4_hvec3 0 s4_hj3

theorem wcOn_adjoint [Fact p.Prime] (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F) :
    WCOn p (adjointGroup Tag.E8 F) := by
  have hp : p.Prime := Fact.out
  by_cases hcnt : degCount Tag.E8 (orderOf ((Nat.card F : ℕ) : ZMod p)) ≤ 1
  · exact WCOn.of_rankLE1 (rankLE1_E8 F hp hpq hcnt)
  · push Not at hcnt
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
    rw [he] at hcnt
    have hlt : e < p := CFSG.LieType.SeitzGeneration.orderOf_lt_prime hp hpq he
    have hdvd : e ∣ p - 1 := orderOf_dvd_sub_one' hp hpq he
    have he30 : e ≤ 30 := le_thirty_of_degCount_pos (τ := Tag.E8) (by simp) (by omega)
    have hecases : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
      interval_cases e <;> first | omega | exact absurd hcnt (by decide)
    rcases eq_three_or_five_le' hp hp2 with hp3 | hp5
    · refine wcOn_small (Or.inl hp3) hpq ?_
      rw [he]
      omega
    · rcases five_or_seven_le hp hp5 with h5 | h7
      ·
        subst h5
        have he124 : e = 1 ∨ e = 2 ∨ e = 4 := by
          clear he hcnt
          rcases hecases with h | h | h | h | h | h | h | h | h <;> subst h <;> omega
        rcases he124 with h1 | h2 | h4
        · exact wcOn_small (Or.inr (Or.inl rfl)) hpq (Or.inl (by rw [he, h1]))
        · exact wcOn_small (Or.inr (Or.inl rfl)) hpq (Or.inr (by rw [he, h2]))
        · exact wcOn_four_five rfl hpq (by rw [he, h4])
      · by_cases he12 : e = 1 ∨ e = 2
        · rcases seven_or_eleven_le hp h7 with h77 | h11
          · exact wcOn_small (Or.inr (Or.inr h77)) hpq (by rw [he]; exact he12)
          · exact wcOn_one_two h11 hpq he he12
        · refine wcOn_toral h7 hpq he ?_
          omega

end E8

theorem wcOn_e8_model {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (h : UntwistedChevalleyModel K Tag.E8 (ℓ ^ f)) : WCOn p K :=
  wcOn_of_untwisted_model hℓ hpℓ h fun F _ _ _ hpq => E8.wcOn_adjoint hp2 hpq

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
