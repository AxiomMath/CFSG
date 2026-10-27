module

public import CFSG.Certificates.Kernel.LceSP.Main
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Certificates.LceP

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop Finset

theorem lceOk_reps {blk WT RT ST LVs : ℕ → ℕ}
    {INV INV8 L nC nCl mLV a m Hs nR nS nf : ℕ} {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}
    (h : CFSG.Certificates.LCE.lceOk blk WT RT ST LVs INV INV8 L nC nCl mLV a m Hs nR nS nf Cs CCs
      S0 S1 X0 X1 = true)
    {G : Type*} [Group G] (gen : ℕ → G) (H K : Subgroup G)
    (hH : H = Subgroup.closure ((fun j => bv gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS}))
    (hK : K = Subgroup.closure (gen '' {g | 2 * g < L}))
    (hrels : ∀ r < nR, bv gen (wWord (RT r)) (wLen (RT r)) = 1) :
    ∃ rep : ℕ → G, rep 0 = 1 ∧ (∀ x < nC, rep x ∈ K) ∧
      (∀ e < nf, fx (fct blk e) < nC ∧ fy (fct blk e) < nC ∧
        rep (fx (fct blk e)) * lv gen (fc (fct blk e)) * (rep (fy (fct blk e)))⁻¹ ∈ H ∧
        rep (fy (fct blk e)) * lv gen (fic (fct blk e)) * (rep (fx (fct blk e)))⁻¹ ∈ H) ∧
      (∀ k ∈ K, ∃ y < nC, alive LVs y = true ∧ k * (rep y)⁻¹ ∈ H) ∧
      ((range nC).filter (fun y => alive LVs y = true)).card ≤ a := by
  subst hH hK
  set H := Subgroup.closure ((fun j => bv gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})
  set K := Subgroup.closure (gen '' {g | 2 * g < L})
  unfold CFSG.Certificates.LCE.lceOk at h
  obtain ⟨hinv, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hwords, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hhints, h⟩ := (andB_iff _ _).1 h
  obtain ⟨halive, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnC, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hle, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hm, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hper, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnorm, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hrun, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS1, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hX0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hcov, hX1⟩ := (andB_iff _ _).1 h
  have hnC' : nC = nCl := Nat.eq_of_beq_eq_true hnC
  subst hnC'
  have hle' : nC ≤ 1048576 := Nat.le_of_ble_eq_true hle
  have hnf': nf < 4294967296 := blt_true hnf
  have hm' : 0 < m := blt_true hm
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hrun' := Nat.eq_of_beq_eq_true hrun
  have hS1' : S1 = mkS nf nC := Nat.eq_of_beq_eq_true hS1
  have hX0' : X0 = 1 := Nat.eq_of_beq_eq_true hX0
  have hcov' := Nat.eq_of_beq_eq_true hcov
  have hX1' : X1 = nC + 1 := Nat.eq_of_beq_eq_true hX1
  obtain ⟨hL, hL2, hinvc⟩ := invOK_spec hinv
  obtain ⟨hMLV, hnC0, halive0, hcnt⟩ := aliveOK_spec halive
  have hKl : ∀ c < L, lv gen c ∈ K := by
    intro c hc
    have hg : gen (c / 2) ∈ K :=
      Subgroup.subset_closure ⟨c / 2, by change 2 * (c / 2) < L; omega, rfl⟩
    unfold lv
    split_ifs
    · exact K.one_mem
    · exact hg
    · exact K.inv_mem hg
  have hWT : ∀ k < 65536, WOK gen H (WT k) := by
    intro k hk
    rw [wtPer_spec hper k hk]
    exact words_spec gen hinv hwords hhints hrels (relsNorm_spec hnorm) _ (Nat.mod_lt _ hm')
  have hG0 : FGood gen H K blk INV nC S0 := by
    rw [hS0']
    exact FGood_mkS gen H K (by norm_num) le_rfl (fun _ => FInv_zero gen H K blk INV nC 1)
  have hG1 := runFacts_good gen H K hinv hWT hKl Cs S0 hG0
  rw [hrun', hS1'] at hG1
  rcases hG1 with h0 | ⟨-, hF⟩
  · rw [mkS_eq nC hnf'] at h0
    omega
  rw [sI_eq, sN_eq, mkS_eq nC hnf'] at hF
  have e1 : (nf + nC * 4294967296) % 4294967296 = nf := by omega
  have e2 : (nf + nC * 4294967296) / 4294967296 = nC := by omega
  rw [e1, e2] at hF
  obtain ⟨hrecs, rep, hrep0, hrepK, hfacts⟩ := hF
  have hfact : ∀ e < nf, el gen rep (fct blk e) ∈ H := hfacts rep (fun _ _ => rfl)
  have hboth : ∀ e < nf, fx (fct blk e) < nC ∧ fy (fct blk e) < nC ∧
      rep (fx (fct blk e)) * lv gen (fc (fct blk e)) * (rep (fy (fct blk e)))⁻¹ ∈ H ∧
      rep (fy (fct blk e)) * lv gen (fic (fct blk e)) * (rep (fx (fct blk e)))⁻¹ ∈ H := by
    intro e he
    obtain ⟨hfx, hfy, -⟩ := recOK_spec (hrecs e he)
    have hf := hfact e he
    unfold el at hf
    refine ⟨hfx, hfy, hf, ?_⟩
    rw [(lv_fic gen blk hinv (hrecs e he)).1]
    have hi := H.inv_mem hf
    have ee : (rep (fx (fct blk e)) * lv gen (fc (fct blk e)) * (rep (fy (fct blk e)))⁻¹)⁻¹ =
        rep (fy (fct blk e)) * (lv gen (fc (fct blk e)))⁻¹ * (rep (fx (fct blk e)))⁻¹ := by
      group
    rwa [ee] at hi
  have hC0 : CGood blk LVs nf L X0 := by
    rw [hX0']
    exact Or.inr ⟨le_rfl, fun x hx => absurd hx (Nat.not_lt_zero x)⟩
  have hC1 := runCover_good CCs X0 hC0
  rw [hcov', hX1'] at hC1
  rcases hC1 with h0 | ⟨-, hC⟩
  · omega
  have hcover : ∀ x < nC, alive LVs x = true → ∀ c < L,
      ∃ y, y < nC ∧ alive LVs y = true ∧ rep x * lv gen c * (rep y)⁻¹ ∈ H := by
    intro x hx hal c hc
    obtain ⟨e, he⟩ := hC x (by omega) hal c hc
    obtain ⟨hh, hdir⟩ := slotOK_spec he
    set R := fct blk (Nat.shiftRight e 1)
    obtain ⟨-, -, hfw, hbw⟩ := hboth _ hh
    rw [lor20 c (show x < 1048576 by omega)] at hdir
    rcases hdir with ⟨hk, hy⟩ | ⟨hk, hy⟩
    · rw [fxc_eq] at hk
      have := fx_lt R
      have := fc_lt R
      have h1 : fx R = x := by omega
      have h2 : fc R = c := by omega
      refine ⟨fy R, (recOK_spec (hrecs _ hh)).2.1, hy, ?_⟩
      rw [h1, h2] at hfw
      exact hfw
    · rw [fyic_eq] at hk
      have := fy_lt R
      have := fic_lt blk (Nat.shiftRight e 1)
      have h1 : fy R = x := by omega
      have h2 : fic R = c := by omega
      refine ⟨fx R, (recOK_spec (hrecs _ hh)).1, hy, ?_⟩
      rw [h1, h2] at hbw
      exact hbw
  have hmove : ∀ k ∈ K, ∀ x < nC, alive LVs x = true →
      ∃ y, y < nC ∧ alive LVs y = true ∧ rep x * k * (rep y)⁻¹ ∈ H := by
    intro k hk
    induction hk using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨g', hg', rfl⟩ := hg
      intro x hx hal
      have h2 : 2 * g' < L := hg'
      have h255 : 2 * g' < 255 := by omega
      have := hcover x hx hal (2 * g') h2
      rwa [lv_even' gen h255] at this
    | inv_mem g hg =>
      obtain ⟨g', hg', rfl⟩ := hg
      intro x hx hal
      have h2 : 2 * g' < L := hg'
      have h255 : 2 * g' + 1 < 255 := by omega
      have := hcover x hx hal (2 * g' + 1) (by omega)
      rwa [lv_odd' gen h255] at this
    | one =>
      intro x hx hal
      exact ⟨x, hx, hal, by rw [mul_one, mul_inv_cancel]; exact H.one_mem⟩
    | mul k1 k2 _ _ ih1 ih2 =>
      intro x hx hal
      obtain ⟨y1, hy1, hal1, hm1⟩ := ih1 x hx hal
      obtain ⟨y2, hy2, hal2, hm2⟩ := ih2 y1 hy1 hal1
      refine ⟨y2, hy2, hal2, ?_⟩
      have := H.mul_mem hm1 hm2
      have e : rep x * k1 * (rep y1)⁻¹ * (rep y1 * k2 * (rep y2)⁻¹) =
          rep x * (k1 * k2) * (rep y2)⁻¹ := by group
      rwa [e] at this
  refine ⟨rep, hrep0, hrepK, hboth, fun k hk => ?_, ?_⟩
  · obtain ⟨y, hy, hal, hmem⟩ := hmove k hk 0 hnC0 halive0
    rw [hrep0, one_mul] at hmem
    exact ⟨y, hy, hal, hmem⟩
  · rw [← hcnt, card_filter]
    calc ∑ y ∈ range nC, (if alive LVs y = true then 1 else 0)
        ≤ ∑ y ∈ range (4096 * mLV), (if alive LVs y = true then 1 else 0) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro y hy
            rw [mem_range] at hy ⊢
            omega
          · intros
            exact Nat.zero_le _
      _ ≤ cntRec LVs mLV := count_le LVs mLV

end CFSG.Certificates.LceP

end
