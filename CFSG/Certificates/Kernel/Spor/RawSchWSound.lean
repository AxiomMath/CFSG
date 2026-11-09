module

public import CFSG.Certificates.Kernel.Spor.RawSchOSound
public import Certificates.Data.Kernel.Spor.RawSchW
import all CFSG.Certificates.Kernel.Spor.RawSch3GSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native

theorem stw_facts {n w kS T TJ : Nat} {S SI : Nat → Nat} (hn24 : n < 16777216)
    (hw : n + 1 < 2 ^ w)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hT : ∀ j < stCnt T, stAt T j < kS + kS) :
    ∀ (W : List (List Nat)) (j : Nat), stwK n w (mask w) (pidn n w) S SI kS T TJ W j = true →
      ∀ j', j ≤ j' → j' < Nat.shiftRight (stCnt T) (nat_lit 1) →
        lp n w S kS (stAt T j') ∈ Submonoid.closure (LJ n w S kS TJ)
  | [], j, h, j', h1, h2 => by
    have : j = Nat.shiftRight (stCnt T) (nat_lit 1) := Nat.eq_of_beq_eq_true h
    omega
  | wd :: W, j, h, j', h1, h2 => by
    have e : stwK n w (mask w) (pidn n w) S SI kS T TJ (wd :: W) j = bAnd(wlK kS TJ wd,
        bAnd(Nat.beq (letterK S SI kS (stAt T j)) (wvK n w (mask w) (pidn n w) S SI kS TJ wd),
          stwK n w (mask w) (pidn n w) S SI kS T TJ W (Nat.succ j))) := rfl
    rw [e] at h
    simp only [bAnd_iff] at h
    obtain ⟨h1', h2', h3'⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · obtain ⟨g, hg, hm⟩ := wv_facts hn24 hw hp wd h1'
      have hjT : j < stCnt T := by
        rw [shr_eq] at h2
        exact Nat.lt_of_lt_of_le h2 (Nat.div_le_self _ _)
      have hg' : PRep n w (letterK S SI kS (stAt T j)) g := by
        rw [Nat.eq_of_beq_eq_true h2']
        exact hg
      rw [prep_unique (prep_lp hp (hT j hjT)) hg']
      exact hm
    · exact stw_facts hn24 hw hp hT W (Nat.succ j) h3' j' hlt h2

theorem steps_mem_stw {n w kS T TJ TS : Nat} {S SI : Nat → Nat} {WS : List (List Nat)}
    (hn24 : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hinv : invTabK kS T = true)
    (hW : stwK n w (mask w) (pidn n w) S SI kS T TJ WS 0 = true) (hJ : incK TJ TS = true) :
    ∀ j < stCnt T, lp n w S kS (stAt T j) ∈ Submonoid.closure (LT n w S kS TS) := by
  have hsub : LJ n w S kS TJ ⊆ LT n w S kS TS := by
    rintro g ⟨a, ha, -, rfl⟩
    have ha' : a < stCnt TJ := by
      rw [shr_eq] at ha
      exact Nat.lt_of_lt_of_le ha (Nat.div_le_self _ _)
    exact inc_sub (n := n) (w := w) (kS := kS) (S := S) hJ ⟨a, ha', rfl⟩
  have hT := letter_lt hinv
  obtain ⟨q, hq, hf⟩ := invTab_facts hinv
  have hq' : Nat.shiftRight (stCnt T) (nat_lit 1) = q := by
    rw [shr_eq, hq, Nat.pow_one]
    omega
  have hF : ∀ j' < q, lp n w S kS (stAt T j') ∈ Submonoid.closure (LT n w S kS TS) :=
    fun j' hj' => Submonoid.closure_mono hsub
      (stw_facts hn24 hw hp hT WS 0 hW j' (Nat.zero_le _) (by rw [hq']; exact hj'))
  intro j hj
  rcases Nat.lt_or_ge j q with h1 | h1
  · exact hF j h1
  · obtain ⟨j', rfl⟩ : ∃ j', j = q + j' := ⟨j - q, by omega⟩
    have hj' : j' < q := by omega
    obtain ⟨hlt, he⟩ := hf j' hj'
    have hn : ¬ (kS + stAt T j' < kS) := by omega
    have e : lp n w S kS (stAt T (q + j')) = (lp n w S kS (stAt T j'))⁻¹ := by
      unfold lp
      rw [he, if_neg hn, if_pos hlt, Nat.add_sub_cancel_left]
    rw [e]
    exact inv_mem_closure (hF j' hj')

theorem schK_of_schOL_stw {n w kS kO BP E i TS TJ NSi CH : Nat} {S SI LR TR TRI : Nat → Nat}
    {W : List (List Int)} {WS : List (List Nat)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W E BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS E BP) (hE : i + 3 ≤ E)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (hlv : ∀ k < E - i - 2, lv12K w (mask w) S SI kS BP (i + k) (stepsAt n w S kS BP (i + k + 1))
      (stepsAt n w S kS BP (i + k + 1 + 1)) = true)
    (hTS : allN (stCnt TS) (fun a => Nat.blt (stAt TS a) kS) = true)
    (hW : stwK n w (mask w) (pidn n w) S SI kS (stepsAt n w S kS BP i) TJ WS 0 = true)
    (hJ : incK TJ TS = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E i TS
      (s * CH) CH = true)
    (hsl : ∀ k < E - i - 1, ∃ N, rcnt (LR (i + 1 + k)) ≤ N * CH ∧ ∀ s < N,
      schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E (i + 1 + k)
        (stepsAt n w S kS BP (i + 1 + k)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  obtain ⟨hsz, -, -, -, -, -⟩ := levelK_facts (hl i (by omega))
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hp := (head_facts hh).1
  exact schK_of_schOM hp hl hE hinv hlv
    (fun a ha => by have := Nat.blt_eq.mp (allN_iff.1 hTS a ha); omega)
    (steps_mem_stw hn24 hw hp hinv hW hJ) hc hs hsl h₀ cnt

end CFSG.KS.Raw.Orb

end
