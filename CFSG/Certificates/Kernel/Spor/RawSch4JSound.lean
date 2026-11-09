module

public import Certificates.Data.Kernel.Spor.RawSch4J
public import CFSG.Certificates.Kernel.Spor.RawSch4FSound
public import CFSG.Certificates.Kernel.Spor.RawSchWSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem dupTab_facts {T : Nat} (h : dupTabK T = true) :
    ∀ j < stCnt T, ∃ j' < Nat.shiftRight (stCnt T) (nat_lit 1), stAt T j = stAt T j' := by
  unfold dupTabK at h
  simp only [strictB_eq] at h
  generalize Nat.shiftRight (stCnt T) (nat_lit 1) = q at h ⊢
  simp only [bAnd_iff, Nat.beq_eq, allN_iff, Nat.add_eq] at h
  obtain ⟨hq, hf⟩ := h
  intro j hj
  rcases Nat.lt_or_ge j q with h1 | h1
  · exact ⟨j, h1, rfl⟩
  · obtain ⟨j', rfl⟩ : ∃ j', j = q + j' := ⟨j - q, by omega⟩
    exact ⟨j', by omega, hf j' (by omega)⟩

theorem schK_of_t4KD {n w kS BP i T E D : Nat} {S SI LR TR TRI U : Nat → Nat}
    (hsz : szOK n w = true)
    (hb1 : Nat.blt (pg w (mask w) BP (i + 1)) n = true)
    (hb2 : Nat.blt (pg w (mask w) BP (i + 1 + 1)) n = true)
    (hb3 : Nat.blt (pg w (mask w) BP (i + 1 + 1 + 1)) n = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 4) BP)
    (hd : dupTabK T = true)
    (hU : utab4F n w (mask w) (n * w) LR TR U i E D = true)
    (hF : ∀ h < rcnt (LR i), ∀ j < Nat.shiftRight (stCnt T) (nat_lit 1),
      t4K n w (mask w) (n * w) S SI LR TR TRI U kS BP i T E D h j = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4) i T h₀ cnt = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hb1' := Nat.blt_eq.mp hb1
  have hb2' := Nat.blt_eq.mp hb2
  have hb3' := Nat.blt_eq.mp hb3
  obtain ⟨-, -, -, -, -, hp0⟩ := levelK_facts (hl i (by omega))
  obtain ⟨-, -, -, -, -, hp1⟩ := levelK_facts (hl (i + 1) (by omega))
  obtain ⟨-, -, -, -, -, hp2⟩ := levelK_facts (hl (i + 1 + 1) (by omega))
  obtain ⟨-, -, -, -, -, hp3⟩ := levelK_facts (hl (i + 1 + 1 + 1) (by omega))
  have hU' := utab4F_facts hU
  have hD := dupTab_facts hd
  have e3 : Nat.sub (i + 4) (Nat.succ i) = 0 + 1 + 1 + 1 := by
    simp only [Nat.sub_eq, Nat.succ_eq_add_one]
    omega
  unfold schK
  rw [e3]
  simp only [strictB_eq, allN_iff, bIf_eq, Nat.blt_eq, Nat.add_eq, Nat.succ_eq_add_one]
  intro dh _
  split
  case isFalse => rfl
  rename_i hc
  rw [allN_iff]
  intro j hj
  obtain ⟨j', hj', hst⟩ := hD j hj
  obtain ⟨hk, hk1, hk2, hk3, hE⟩ := t4K_facts (hF _ hc j' hj')
    (s := letterK S SI kS (stAt T j)) (by rw [hst]) rfl rfl rfl rfl rfl
  rw [if_pos hk]
  refine sift3_of_fields hsz hb2' hb3' (by rw [PF.pg_pcomp hn hb1', PF.pg_pcomp hn hb1']) hk1
    (by rw [PF.pg_pcomp hn hb2', PF.pg_pcomp hn hb2']) hk2
    (by rw [PF.pg_pcomp hn hb3', PF.pg_pcomp hn hb3']) hk3 (hp1 _ hk1) (hp2 _ hk2) (hp3 _ hk3)
    (fun x hx => ?_)
  rw [PF.pg_pcomp hn hx, hE, PF.pg_pcomp hn hx, hU' _ hk2 _ hk3 _ hk1, PF.pg_pcomp hn hx,
    PF.pg_pcomp hn hx]
  obtain ⟨-, -, f0⟩ := permOK_facts (hp0 _ hk)
  obtain ⟨-, -, f1⟩ := permOK_facts (hp1 _ hk1)
  obtain ⟨-, -, f2⟩ := permOK_facts (hp2 _ hk2)
  obtain ⟨-, -, f3⟩ := permOK_facts (hp3 _ hk3)
  exact (f0 _ (f1 _ (f2 _ (f3 x hx).1).1).1).2

theorem schK_of_sch4JL {n w kS kO BP i E D TJ NSi N1 N2 N3 CH : Nat}
    {S SI LR TR TRI U : Nat → Nat} {W : List (List Int)} {WS : List (List Nat)}
    (hb1 : Nat.blt (pg w (mask w) BP (i + 1)) n = true)
    (hb2 : Nat.blt (pg w (mask w) BP (i + 1 + 1)) n = true)
    (hb3 : Nat.blt (pg w (mask w) BP (i + 1 + 1 + 1)) n = true)
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W (i + 4) BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 4) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (h12 : lv12K w (mask w) S SI kS BP i (stepsAt n w S kS BP (i + 1))
      (stepsAt n w S kS BP (i + 1 + 1)) = true)
    (h23 : lv12K w (mask w) S SI kS BP (i + 1) (stepsAt n w S kS BP (i + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1)) = true)
    (hTS : allN (stCnt TJ) (fun a => Nat.blt (stAt TJ a) kS) = true)
    (hd : dupTabK TJ = true) (hJ : incK TJ TJ = true)
    (hW : stwK n w (mask w) (pidn n w) S SI kS (stepsAt n w S kS BP i) TJ WS 0 = true)
    (hU : utab4F n w (mask w) (n * w) LR TR U i E D = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, sch4F n w (mask w) (n * w) S SI LR TR TRI U kS BP i TJ E D (s * CH) CH = true)
    (hc1 : rcnt (LR (i + 1)) ≤ N1 * CH)
    (hs1 : ∀ s < N1, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4) (i + 1)
      (stepsAt n w S kS BP (i + 1)) (s * CH) CH = true)
    (hc2 : rcnt (LR (i + 1 + 1)) ≤ N2 * CH)
    (hs2 : ∀ s < N2, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4)
      (i + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1)) (s * CH) CH = true)
    (hc3 : rcnt (LR (i + 1 + 1 + 1)) ≤ N3 * CH)
    (hs3 : ∀ s < N3, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4)
      (i + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4) i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  have hF := t4K_of_sch4F hc hs
  have hsz := (levelK_facts (hl i (by omega))).1
  refine schK_of_schOL_stw hh hl (by omega) hinv (fun k hk => ?_) hTS hW hJ hc
    (fun _ _ => schK_of_t4KD hsz hb1 hb2 hb3 hl hd hU hF _ _) (fun k hk => ?_) h₀ cnt
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact h12
    · exact h23
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact ⟨N1, hc1, hs1⟩
    · exact ⟨N2, hc2, hs2⟩
    · exact ⟨N3, hc3, hs3⟩

end CFSG.KS.Raw.Orb

end
