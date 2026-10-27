module

public import Certificates.Data.Kernel.Spor.RawSch3F
public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem permOK_right {n w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    ∀ z < n, pg w (mask w) Q z < n ∧ pg w (mask w) P (pg w (mask w) Q z) = z := by
  obtain ⟨-, -, f⟩ := permOK_facts h
  intro z hz
  let g : Fin n → Fin n := fun i => ⟨pg w (mask w) P i, (f i i.2).1⟩
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : pg w (mask w) P a = pg w (mask w) P b := congrArg Fin.val hab
    have h2 := congrArg (pg w (mask w) Q) h1
    rw [(f a a.2).2, (f b b.2).2] at h2
    exact Fin.ext h2
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hinj ⟨z, hz⟩
  have hiz : pg w (mask w) P i = z := congrArg Fin.val hi
  rw [← hiz, (f i i.2).2]
  exact ⟨i.2, rfl⟩

theorem siftK_congr {n w : Nat} {LR TRI : Nat → Nat} {BP d l G G' : Nat} (hn : n < 2 ^ 32)
    (hw : 0 < w) (hb : pg w (mask w) BP l < n)
    (h : ∀ x < n, pg w (mask w) G x = pg w (mask w) G' x) :
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP (d + 1) l G =
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP (d + 1) l G' := by
  rw [siftK_succ, siftK_succ, h _ hb]
  have e : ∀ T, pcomp n w (mask w) T G = pcomp n w (mask w) T G' := fun T =>
    PF.eq_of_fields hw (PF.pcomp_shr _ _ hn hw) (PF.pcomp_shr _ _ hn hw) (fun x hx => by
      rw [PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, h x hx])
  simp only [e]

theorem sift2_of_fields {n w i : Nat} {LR TR TRI : Nat → Nat} {BP G k1 k2 : Nat}
    (hsz : szOK n w = true)
    (hb2 : pg w (mask w) BP (i + 1 + 1) < n)
    (e1 : rpos w (mask w) (n * w) (LR (i + 1)) (pg w (mask w) G (pg w (mask w) BP (i + 1))) = k1)
    (hk1 : k1 < rcnt (LR (i + 1)))
    (e2 : rpos w (mask w) (n * w) (LR (i + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
        (pg w (mask w) G (pg w (mask w) BP (i + 1 + 1)))) = k2)
    (hk2 : k2 < rcnt (LR (i + 1 + 1)))
    (hp1 : permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR (i + 1)) + k1))
      (TRI (roff n (n * w) (LR (i + 1)) + k1)) = true)
    (hp2 : permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR (i + 1 + 1)) + k2))
      (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2)) = true)
    (hE : ∀ x < n, pg w (mask w) G x = pg w (mask w) (TR (roff n (n * w) (LR (i + 1)) + k1))
      (pg w (mask w) (TR (roff n (n * w) (LR (i + 1 + 1)) + k2)) x)) :
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP (0 + 1 + 1) (i + 1) G = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hw0 : 0 < w := PF.w_pos hw
  simp only [siftK_succ, siftK_zero, strictB_eq, bIf_eq, Nat.blt_eq, Nat.add_eq,
    Nat.succ_eq_add_one]
  rw [e1, if_pos hk1, PF.pg_pcomp hn hb2, e2, if_pos hk2]
  simp only [hsz, Bool.true_and, ↓reduceIte, Nat.beq_eq]
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn hw0) (PF.pidn_shr hn24 hw) (fun x hx => ?_)
  rw [PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, PF.pg_pidn hn24 hw hx, hE x hx]
  obtain ⟨-, -, f1⟩ := permOK_facts hp1
  obtain ⟨-, -, f2⟩ := permOK_facts hp2
  rw [(f1 _ (f2 x hx).1).2, (f2 x hx).2]

theorem t3K_facts {n w kS BP i T D h j : Nat} {S SI LR TR TRI U : Nat → Nat}
    (ht : t3K n w (mask w) (n * w) S SI LR TR TRI U kS BP i T D h j = true) {s th k k1 k2 : Nat}
    (es : letterK S SI kS (stAt T j) = s) (eth : TR (roff n (n * w) (LR i) + h) = th)
    (ek : rpos w (mask w) (n * w) (LR i) (pg w (mask w) s (rpt w (mask w) (LR i) h)) = k)
    (ek1 : rpos w (mask w) (n * w) (LR (i + 1)) (pg w (mask w) (TRI (roff n (n * w) (LR i) + k))
      (pg w (mask w) s (pg w (mask w) th (pg w (mask w) BP (i + 1))))) = k1)
    (ek2 : rpos w (mask w) (n * w) (LR (i + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
        (pg w (mask w) (TRI (roff n (n * w) (LR i) + k))
          (pg w (mask w) s (pg w (mask w) th (pg w (mask w) BP (i + 1 + 1)))))) = k2) :
    k < rcnt (LR i) ∧ k1 < rcnt (LR (i + 1)) ∧ k2 < rcnt (LR (i + 1 + 1)) ∧
      pcomp n w (mask w) s th = pcomp n w (mask w) (TR (roff n (n * w) (LR i) + k)) (U (k1 * D + k2)) := by
  unfold t3K at ht
  simp only [strictB_eq, bAnd_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq,
    Nat.succ_eq_add_one] at ht
  subst es eth
  rw [ek] at ht
  rw [ek1] at ht
  rw [ek2] at ht
  exact ht

theorem schK_of_t3K {n w kS BP i D : Nat} {S SI LR TR TRI U : Nat → Nat}
    (hsz : szOK n w = true)
    (hb1 : Nat.blt (pg w (mask w) BP (i + 1)) n = true)
    (hb2 : Nat.blt (pg w (mask w) BP (i + 1 + 1)) n = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 3) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (hU : utabF n w (mask w) (n * w) LR TR U i D = true)
    (hV : vtabK n w (mask w) (n * w) (pidn n w) LR TRI BP i = true)
    (hF : ∀ h < rcnt (LR i), ∀ j < Nat.shiftRight (stCnt (stepsAt n w S kS BP i)) (nat_lit 1),
      t3K n w (mask w) (n * w) S SI LR TR TRI U kS BP i (stepsAt n w S kS BP i) D h j = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 3) i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hw0 : 0 < w := PF.w_pos hw
  have hb1' := Nat.blt_eq.mp hb1
  have hb2' := Nat.blt_eq.mp hb2
  have hpS := allN_iff.1 hp
  obtain ⟨-, -, hR, -, -, hp0⟩ := levelK_facts (hl i (by omega))
  obtain ⟨-, -, -, -, -, hp1⟩ := levelK_facts (hl (i + 1) (by omega))
  obtain ⟨-, -, -, -, -, hp2⟩ := levelK_facts (hl (i + 1 + 1) (by omega))
  generalize stepsAt n w S kS BP i = T at hinv hF hR ⊢
  unfold invTabK at hinv
  simp only [strictB_eq] at hinv
  generalize Nat.shiftRight (stCnt T) (nat_lit 1) = q at hinv hF
  simp only [bAnd_iff, Nat.beq_eq, allN_iff, Nat.blt_eq, Nat.add_eq, strictB_eq] at hinv
  obtain ⟨hr, hq⟩ := hinv
  unfold utabF at hU
  simp only [strictB_eq, allN_iff, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at hU
  unfold vtabK at hV
  simp only [strictB_eq, allN_iff, Nat.add_eq, Nat.succ_eq_add_one] at hV
  have e2 : Nat.sub (i + 3) (Nat.succ i) = 0 + 1 + 1 := by
    simp only [Nat.sub_eq, Nat.succ_eq_add_one]
    omega
  unfold schK
  rw [e2]
  simp only [strictB_eq, allN_iff, bIf_eq, Nat.blt_eq, Nat.add_eq, Nat.succ_eq_add_one]
  intro dh _
  split
  case isFalse => rfl
  rename_i hc
  rw [allN_iff]
  intro j hj
  by_cases hjq : j < q
  · obtain ⟨hk, hk1, hk2, hE⟩ := t3K_facts (hF _ hc j hjq) rfl rfl rfl rfl rfl
    rw [if_pos hk]
    refine sift2_of_fields hsz hb2' (by rw [PF.pg_pcomp hn hb1', PF.pg_pcomp hn hb1']) hk1
      (by rw [PF.pg_pcomp hn hb2', PF.pg_pcomp hn hb2']) hk2 (hp1 _ hk1) (hp2 _ hk2)
      (fun x hx => ?_)
    rw [PF.pg_pcomp hn hx, hE, PF.pg_pcomp hn hx, hU _ hk1 _ hk2, PF.pg_pcomp hn hx]
    obtain ⟨-, -, f0⟩ := permOK_facts (hp0 _ hk)
    obtain ⟨-, -, f1⟩ := permOK_facts (hp1 _ hk1)
    obtain ⟨-, -, f2⟩ := permOK_facts (hp2 _ hk2)
    exact (f0 _ (f1 _ (f2 x hx).1).1).2
  · obtain ⟨j', hj', rfl⟩ : ∃ j', j' < q ∧ j = q + j' := ⟨j - q, by omega, by omega⟩
    obtain ⟨hL, hLj⟩ := hq j' hj'
    have hsf : letterK S SI kS (stAt T j') = S (stAt T j') := by
      simp only [letterK, nIf_eq, Nat.blt_eq]
      rw [if_pos hL]
    have hsj : letterK S SI kS (stAt T (q + j')) = SI (stAt T j') := by
      simp only [letterK, nIf_eq, Nat.blt_eq]
      rw [hLj, if_neg (by omega), Nat.sub_eq, Nat.add_sub_cancel_left]
    have hpL := hpS _ hL
    have hpt := hR.pt _ hc
    have hz := (permOK_right hpL _ hpt.1).1
    have hk := (hR.closed _ hc _ hj).1
    simp only [hsj] at hk
    rw [hsj, if_pos hk]
    have hpk := hR.pos _ hz hk
    obtain ⟨k1, k2, hk1, hk2, hE⟩ : ∃ k1 k2, k1 < rcnt (LR (i + 1)) ∧ k2 < rcnt (LR (i + 1 + 1)) ∧
        pcomp n w (mask w) (S (stAt T j')) (TR (roff n (n * w) (LR i) +
          rpos w (mask w) (n * w) (LR i) (pg w (mask w) (SI (stAt T j'))
            (rpt w (mask w) (LR i) (h₀ + dh))))) =
        pcomp n w (mask w) (TR (roff n (n * w) (LR i) + (h₀ + dh))) (U (k1 * D + k2)) :=
      ⟨_, _, (t3K_facts (hF _ hk j' hj') hsf rfl (k := h₀ + dh)
        (by rw [hpk, (permOK_right hpL _ hpt.1).2, hpt.2]) rfl rfl).2⟩
    refine Eq.trans (siftK_congr hn hw0 hb1' (fun x hx => ?_)) (hV _ hk1 _ hk2)
    rw [PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, PF.pg_pcomp hn hx]
    obtain ⟨-, -, f0⟩ := permOK_facts (hp0 _ hk)
    obtain ⟨-, -, fS⟩ := permOK_facts hpL
    have hy1 := permOK_right (hp1 _ hk1) x hx
    have hy2 := permOK_right (hp2 _ hk2) _ hy1.1
    have hUy := congrArg (fun P => pg w (mask w) P
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1)) x))) (hU _ hk1 _ hk2)
    simp only [PF.pg_pcomp hn hy2.1, hy2.2, hy1.2] at hUy
    have hEy := congrArg (fun P => pg w (mask w) P
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1)) x))) hE
    simp only [PF.pg_pcomp hn hy2.1, hUy] at hEy
    rw [← hEy, (fS _ (f0 _ hy2.1).1).2, (f0 _ hy2.1).2]

theorem t3K_of_sch3F {n w kS BP i T D NSi CH : Nat} {S SI LR TR TRI U : Nat → Nat}
    (hc : rcnt (LR i) ≤ NSi * CH)
    (h : ∀ s < NSi, sch3F n w (mask w) (n * w) S SI LR TR TRI U kS BP i T D (s * CH) CH = true) :
    ∀ hh < rcnt (LR i), ∀ j < Nat.shiftRight (stCnt T) (nat_lit 1),
      t3K n w (mask w) (n * w) S SI LR TR TRI U kS BP i T D hh j = true := by
  intro hh hhc j hj
  have hCH : 0 < CH := by
    rcases Nat.eq_zero_or_pos CH with h0 | h0
    · rw [h0, Nat.mul_zero] at hc
      omega
    · exact h0
  have hs := h (hh / CH) ((Nat.div_lt_iff_lt_mul hCH).2 (by omega))
  unfold sch3F at hs
  simp only [strictB_eq] at hs
  have h1 := allN_iff.1 hs (hh % CH) (Nat.mod_lt _ hCH)
  have e : Nat.add (hh / CH * CH) (hh % CH) = hh := by
    have := Nat.div_add_mod hh CH
    rw [Nat.mul_comm] at this
    exact this
  simp only [e, bIf_eq] at h1
  rw [if_pos (Nat.blt_eq.mpr hhc)] at h1
  exact allN_iff.1 h1 j hj

theorem schK_of_sch3FL {n w kS kO BP i D NSi CH : Nat} {S SI LR TR TRI U : Nat → Nat}
    {W : List (List Int)}
    (hb1 : Nat.blt (pg w (mask w) BP (i + 1)) n = true)
    (hb2 : Nat.blt (pg w (mask w) BP (i + 1 + 1)) n = true)
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W (i + 3) BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 3) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (hU : utabF n w (mask w) (n * w) LR TR U i D = true)
    (hV : vtabK n w (mask w) (n * w) (pidn n w) LR TRI BP i = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, sch3F n w (mask w) (n * w) S SI LR TR TRI U kS BP i (stepsAt n w S kS BP i) D
      (s * CH) CH = true) (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 3) i
      (stepsAt n w S kS BP i) h₀ cnt = true :=
  schK_of_t3K (levelK_facts (hl i (by omega))).1 hb1 hb2 (head_facts hh).1 hl hinv hU hV
    (t3K_of_sch3F hc hs) h₀ cnt

end CFSG.KS.Raw.Orb

end
