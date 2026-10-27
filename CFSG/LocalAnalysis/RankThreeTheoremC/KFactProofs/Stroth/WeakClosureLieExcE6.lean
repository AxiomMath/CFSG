module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcUntw
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE6Data
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

namespace E6

open E6Data

theorem commutator_eq_top : commutator ↥(adjointGroup Tag.E6 F) = ⊤ :=
  (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 F).1.commutator_eq_top

theorem wordMat_e6One : wordMat Tag.E6 e6OneWord = 1 := wordMat_nil Tag.E6

theorem wcOn_one_toral [Fact p.Prime] (hp7 : 7 ≤ p) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 1) : WCOn p (adjointGroup Tag.E6 F) := by
  have hp : p.Prime := Fact.out
  have hF : SylowFrame Tag.E6 F p (wp Tag.E6 e6OneWord) :=
    sylowFrame_untw_blocks (Or.inl rfl) F hp (by omega) hpq e6OneWord [1, 1, 1, 1, 1, 1]
      e6One_charpoly e6One_pow he (fun d hd hde => absurd (by simpa using hd) hde)
      (not_dvd_div_of_720 hp hp7 (by decide)) (by decide) commutator_eq_top
  have hc : ∀ x : List (Fin Tag.E6.rank),
      wordMat Tag.E6 x * wordMat Tag.E6 e6OneWord = wordMat Tag.E6 e6OneWord * wordMat Tag.E6 x := by
    intro x
    rw [wordMat_e6One, mul_one, one_mul]
  refine hF.wcOn_dcw_cert (a := r1a) (b := r1b) (c := r1c) (d := r1d) (hc _) (hc _) (hc _) (hc _)
    r1_cert (N := 3) ?_
  intro h
  have h3 : p ∣ 3 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem wcOn_toral [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F) {e : ℕ}
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = e) (hecases : e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) :
    WCOn p (adjointGroup Tag.E6 F) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  have hz1 : weylMat (1 : WeylGroup Tag.E6) =
      (1 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) := by
    rw [weylMat_one, one_smul]
  rcases hecases with rfl | rfl | rfl | rfl
  ·
    have hF : SylowFrame Tag.E6 F p (wp Tag.E6 e6TwoWord) :=
      sylowFrame_untw_blocks (Or.inl rfl) F hp hp3 hpq e6TwoWord [1, 1, 2, 2, 2, 2] e6Two_charpoly
        e6Two_pow he (not_dvd_of_blocks_small hp5 (by decide))
        (not_dvd_div_of_12 hp hp5 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r2a) (b := r2b) (c := r2c) (d := r2d) (z := 1) (s := 1) (k := 1)
      hp2 hpq he hz1 (Or.inl rfl) r2_comm_a r2_comm_b r2_comm_c r2_comm_d r2_dc
      (Or.inl ⟨rfl, by omega⟩)
  ·
    have hF : SylowFrame Tag.E6 F p (wp Tag.E6 e6ThreeWord) :=
      sylowFrame_untw_blocks (Or.inl rfl) F hp hp3 hpq e6ThreeWord [3, 3, 3] e6Three_charpoly
        e6Three_pow he (not_dvd_of_blocks_small hp5 (by decide))
        (not_dvd_div_of_12 hp hp5 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r3a) (b := r3b) (c := r3c) (d := r3d) (z := 1) (s := 1) (k := 2)
      hp2 hpq he hz1 (Or.inl rfl) r3_comm_a r3_comm_b r3_comm_c r3_comm_d r3_dc
      (Or.inl ⟨rfl, by omega⟩)
  ·
    have hF : SylowFrame Tag.E6 F p (wp Tag.E6 e6FourWord) :=
      sylowFrame_untw_blocks (Or.inl rfl) F hp hp3 hpq e6FourWord [1, 1, 4, 4] e6Four_charpoly
        e6Four_pow he (not_dvd_of_blocks_small hp5 (by decide))
        (not_dvd_div_of_12 hp hp5 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r4a) (b := r4b) (c := r4c) (d := r4d) (z := 1) (s := 1) (k := 2)
      hp2 hpq he hz1 (Or.inl rfl) r4_comm_a r4_comm_b r4_comm_c r4_comm_d r4_dc
      (Or.inl ⟨rfl, by omega⟩)
  ·
    have hF : SylowFrame Tag.E6 F p (wp Tag.E6 e6SixWord) :=
      sylowFrame_untw_blocks (Or.inl rfl) F hp hp3 hpq e6SixWord [3, 6, 6] e6Six_charpoly
        e6Six_pow he (not_dvd_of_blocks_small hp5 (by decide))
        (not_dvd_div_of_12 hp hp5 (by decide)) (by decide) commutator_eq_top
    exact hF.wcOn_dcw (a := r6a) (b := r6b) (c := r6c) (d := r6d) (z := 1) (s := 1) (k := 3)
      hp2 hpq he hz1 (Or.inl rfl) r6_comm_a r6_comm_b r6_comm_c r6_comm_d r6_dc
      (Or.inl ⟨rfl, by omega⟩)

theorem wcOn_three [Fact p.Prime] (hp3 : p = 3) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 1 ∨ orderOf ((Nat.card F : ℕ) : ZMod p) = 2) :
    WCOn p (adjointGroup Tag.E6 F) := by
  have hp : p.Prime := Fact.out
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases he with he | he
  ·
    have hd := dvd_sub_one_of_orderOf_eq_one' (by omega) he
    have hv : ⁅wp Tag.E6 [0], wp Tag.E6 [2]⁆ ^ p = 1 := by
      subst hp3
      exact wp_cw_pow_eq_one (by decide +kernel)
    have hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.E6.rank => if i = 0 then (1 : ℤ) else 0) i *
        ((weylMat (wp Tag.E6 [0])⁻¹ - 1) * (weylMat ⁅wp Tag.E6 [0], wp Tag.E6 [2]⁆⁻¹ - 1)) i 3 := by
      subst hp3
      rw [weylMat_wp_inv, weylMat_cw_inv]
      decide +kernel
    exact (weakFrame_untw 3 (Or.inl ⟨rfl, rfl⟩) F 1 commutator_eq_top).wcOn_noncomm_one hpq hd hv
      _ 3 hj
  ·
    have hd := dvd_add_one_of_orderOf_eq_two' hp he
    have hq0 : (Nat.card F : ℤ) ≡ -1 [ZMOD p] := by
      refine (Int.modEq_iff_dvd).2 ?_
      have : (p : ℤ) ∣ (Nat.card F : ℤ) + 1 := by exact_mod_cast hd
      have h2 : (-1 : ℤ) - (Nat.card F : ℤ) = -((Nat.card F : ℤ) + 1) := by ring
      rw [h2]
      exact (dvd_neg).2 this
    have hv : ⁅wp Tag.E6 [1], wp Tag.E6 [3]⁆ ^ p = 1 := by
      subst hp3
      exact wp_cw_pow_eq_one (by decide +kernel)
    have hc : ∀ x : List (Fin Tag.E6.rank),
        (x = [1] ∨ x = [3]) → wp Tag.E6 x ∈
          Subgroup.centralizer ({wp Tag.E6 e6TwoWord} : Set (WeylGroup Tag.E6)) := by
      intro x hx
      refine wp_mem_centralizer ?_
      rcases hx with rfl | rfl <;> decide +kernel
    have hvec : ∀ j : Fin Tag.E6.rank, (p : ℤ) ∣ (-1 : ℤ) *
        (∑ i, (fun i : Fin Tag.E6.rank => if i = 1 ∨ i = 3 then (1 : ℤ) else 0) i *
          weylMat (wp Tag.E6 e6TwoWord)⁻¹ i j) -
        (fun i : Fin Tag.E6.rank => if i = 1 ∨ i = 3 then (1 : ℤ) else 0) j := by
      subst hp3
      rw [weylMat_wp_inv]
      decide +kernel
    have hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.E6.rank => if i = 1 ∨ i = 3 then (1 : ℤ) else 0) i *
        ((weylMat (wp Tag.E6 [1])⁻¹ - 1) * (weylMat ⁅wp Tag.E6 [1], wp Tag.E6 [3]⁆⁻¹ - 1)) i 2 := by
      subst hp3
      rw [weylMat_wp_inv, weylMat_cw_inv]
      decide +kernel
    exact (weakFrame_untw 3 (Or.inl ⟨rfl, rfl⟩) F (wp Tag.E6 e6TwoWord)
      commutator_eq_top).wcOn_noncomm_vec hpq (hc _ (Or.inl rfl)) (hc _ (Or.inr rfl))
      (hc _ (Or.inl rfl)) hv hq0 _ hvec 2 hj

theorem wcOn_five [Fact p.Prime] (hp5 : p = 5) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 1) : WCOn p (adjointGroup Tag.E6 F) := by
  have hp : p.Prime := Fact.out
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hd := dvd_sub_one_of_orderOf_eq_one' (by omega) he
  have hv : ⁅wp Tag.E6 [0, 3], wp Tag.E6 [2, 4]⁆ ^ p = 1 := by
    subst hp5
    exact wp_cw_pow_eq_one (by decide +kernel)
  have hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.E6.rank => if i = 0 then (1 : ℤ) else 0) i *
      ((weylMat (wp Tag.E6 [0])⁻¹ - 1) *
        (weylMat ⁅wp Tag.E6 [0, 3], wp Tag.E6 [2, 4]⁆⁻¹ - 1)) i 0 := by
    subst hp5
    rw [weylMat_wp_inv, weylMat_cw_inv]
    decide +kernel
  exact (weakFrame_untw 3 (Or.inl ⟨rfl, rfl⟩) F 1 commutator_eq_top).wcOn_noncomm_one hpq hd hv
    _ 0 hj

theorem wcOn_adjoint [Fact p.Prime] (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F) :
    WCOn p (adjointGroup Tag.E6 F) := by
  have hp : p.Prime := Fact.out
  by_cases hcnt : degCount Tag.E6 (orderOf ((Nat.card F : ℕ) : ZMod p)) ≤ 1
  · exact WCOn.of_rankLE1 (rankLE1_E6 F hp hpq hcnt)
  · push Not at hcnt
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
    rw [he] at hcnt
    have hlt : e < p := CFSG.LieType.SeitzGeneration.orderOf_lt_prime hp hpq he
    have he30 : e ≤ 30 := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) (by omega)
    have hecases : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
      interval_cases e <;> first | omega | exact absurd hcnt (by decide)
    rcases eq_three_or_five_le' hp hp2 with hp3 | hp5
    · refine wcOn_three hp3 hpq ?_
      rw [he]
      omega
    · rcases hecases with rfl | h2346
      · rcases five_or_seven_le hp hp5 with h5 | h7
        · exact wcOn_five h5 hpq he
        · exact wcOn_one_toral h7 hpq he
      · exact wcOn_toral hp5 hpq he h2346

end E6

theorem wcOn_e6_model {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (h : UntwistedChevalleyModel K Tag.E6 (ℓ ^ f)) : WCOn p K :=
  wcOn_of_untwisted_model hℓ hpℓ h fun F _ _ _ hpq => E6.wcOn_adjoint hp2 hpq

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
