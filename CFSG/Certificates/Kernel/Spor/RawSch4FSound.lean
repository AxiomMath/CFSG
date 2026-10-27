module

public import Certificates.Data.Kernel.Spor.RawSch4F
public import CFSG.Certificates.Kernel.Spor.RawSch3FSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem sift3_of_fields {n w i : Nat} {LR TR TRI : Nat → Nat} {BP G k1 k2 k3 : Nat}
    (hsz : szOK n w = true)
    (hb2 : pg w (mask w) BP (i + 1 + 1) < n)
    (hb3 : pg w (mask w) BP (i + 1 + 1 + 1) < n)
    (e1 : rpos w (mask w) (n * w) (LR (i + 1)) (pg w (mask w) G (pg w (mask w) BP (i + 1))) = k1)
    (hk1 : k1 < rcnt (LR (i + 1)))
    (e2 : rpos w (mask w) (n * w) (LR (i + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
        (pg w (mask w) G (pg w (mask w) BP (i + 1 + 1)))) = k2)
    (hk2 : k2 < rcnt (LR (i + 1 + 1)))
    (e3 : rpos w (mask w) (n * w) (LR (i + 1 + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
          (pg w (mask w) G (pg w (mask w) BP (i + 1 + 1 + 1))))) = k3)
    (hk3 : k3 < rcnt (LR (i + 1 + 1 + 1)))
    (hp1 : permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR (i + 1)) + k1))
      (TRI (roff n (n * w) (LR (i + 1)) + k1)) = true)
    (hp2 : permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR (i + 1 + 1)) + k2))
      (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2)) = true)
    (hp3 : permOK n w (mask w) (n * w) (TR (roff n (n * w) (LR (i + 1 + 1 + 1)) + k3))
      (TRI (roff n (n * w) (LR (i + 1 + 1 + 1)) + k3)) = true)
    (hE : ∀ x < n, pg w (mask w) G x = pg w (mask w) (TR (roff n (n * w) (LR (i + 1)) + k1))
      (pg w (mask w) (TR (roff n (n * w) (LR (i + 1 + 1)) + k2))
        (pg w (mask w) (TR (roff n (n * w) (LR (i + 1 + 1 + 1)) + k3)) x))) :
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP (0 + 1 + 1 + 1) (i + 1) G = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hw0 : 0 < w := PF.w_pos hw
  simp only [siftK_succ, siftK_zero, strictB_eq, bIf_eq, Nat.blt_eq, Nat.add_eq,
    Nat.succ_eq_add_one]
  rw [e1, if_pos hk1, PF.pg_pcomp hn hb2, e2, if_pos hk2, PF.pg_pcomp hn hb3,
    PF.pg_pcomp hn hb3, e3, if_pos hk3]
  simp only [hsz, Bool.true_and, ↓reduceIte, Nat.beq_eq]
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn hw0) (PF.pidn_shr hn24 hw) (fun x hx => ?_)
  rw [PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, PF.pg_pcomp hn hx, PF.pg_pidn hn24 hw hx, hE x hx]
  obtain ⟨-, -, f1⟩ := permOK_facts hp1
  obtain ⟨-, -, f2⟩ := permOK_facts hp2
  obtain ⟨-, -, f3⟩ := permOK_facts hp3
  rw [(f1 _ (f2 _ (f3 x hx).1).1).2, (f2 _ (f3 x hx).1).2, (f3 x hx).2]

theorem perm3_cancel {n w P1 Q1 P2 Q2 P3 Q3 : Nat}
    (h1 : permOK n w (mask w) (n * w) P1 Q1 = true) (h2 : permOK n w (mask w) (n * w) P2 Q2 = true)
    (h3 : permOK n w (mask w) (n * w) P3 Q3 = true) {y : Nat} (hy : y < n) :
    pg w (mask w) Q3 (pg w (mask w) Q2 (pg w (mask w) Q1
      (pg w (mask w) P1 (pg w (mask w) P2 (pg w (mask w) P3 y))))) = y := by
  obtain ⟨-, -, f1⟩ := permOK_facts h1
  obtain ⟨-, -, f2⟩ := permOK_facts h2
  obtain ⟨-, -, f3⟩ := permOK_facts h3
  rw [(f1 _ (f2 _ (f3 y hy).1).1).2, (f2 _ (f3 y hy).1).2, (f3 y hy).2]

theorem utab4F_facts {n w i E D : Nat} {LR TR U : Nat → Nat}
    (hU : utab4F n w (mask w) (n * w) LR TR U i E D = true) :
    ∀ b < rcnt (LR (i + 1 + 1)), ∀ c < rcnt (LR (i + 1 + 1 + 1)), ∀ a < rcnt (LR (i + 1)),
      U (ix4 E D a b c) = pcomp n w (mask w) (TR (roff n (n * w) (LR (i + 1)) + a))
        (pcomp n w (mask w) (TR (roff n (n * w) (LR (i + 1 + 1)) + b))
          (TR (roff n (n * w) (LR (i + 1 + 1 + 1)) + c))) := by
  unfold utab4F at hU
  simp only [strictB_eq, allN_iff, Nat.beq_eq, Nat.add_eq, Nat.succ_eq_add_one] at hU
  exact hU

theorem vtab4K_facts {n w i E D : Nat} {LR TRI U : Nat → Nat} {BP a b c k1 k2 k3 : Nat}
    (hV : vtab4K n w (mask w) (n * w) (pidn n w) LR TRI U BP i E D = true)
    (ha : a < rcnt (LR (i + 1))) (hb : b < rcnt (LR (i + 1 + 1)))
    (hc : c < rcnt (LR (i + 1 + 1 + 1)))
    (ek1 : rpos w (mask w) (n * w) (LR (i + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1 + 1)) + c))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + b))
          (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + a)) (pg w (mask w) BP (i + 1))))) = k1)
    (ek2 : rpos w (mask w) (n * w) (LR (i + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1 + 1)) + c))
          (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + b))
            (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + a))
              (pg w (mask w) BP (i + 1 + 1)))))) = k2)
    (ek3 : rpos w (mask w) (n * w) (LR (i + 1 + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
          (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1 + 1)) + c))
            (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + b))
              (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + a))
                (pg w (mask w) BP (i + 1 + 1 + 1))))))) = k3) :
    k1 < rcnt (LR (i + 1)) ∧ k2 < rcnt (LR (i + 1 + 1)) ∧ k3 < rcnt (LR (i + 1 + 1 + 1)) ∧
      pcomp n w (mask w) (U (ix4 E D a b c)) (U (ix4 E D k1 k2 k3)) = pidn n w := by
  unfold vtab4K at hV
  simp only [strictB_eq, allN_iff, bAnd_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq,
    Nat.succ_eq_add_one] at hV
  have h := hV a ha b hb c hc
  rw [ek1] at h
  rw [ek2] at h
  rw [ek3] at h
  exact h

theorem sift_of_vtab4 {n w i E D : Nat} {LR TR TRI U : Nat → Nat} {BP G a b c : Nat}
    (hsz : szOK n w = true)
    (hb1 : pg w (mask w) BP (i + 1) < n) (hb2 : pg w (mask w) BP (i + 1 + 1) < n)
    (hb3 : pg w (mask w) BP (i + 1 + 1 + 1) < n)
    (hp1 : ∀ k < rcnt (LR (i + 1)), permOK n w (mask w) (n * w)
      (TR (roff n (n * w) (LR (i + 1)) + k)) (TRI (roff n (n * w) (LR (i + 1)) + k)) = true)
    (hp2 : ∀ k < rcnt (LR (i + 1 + 1)), permOK n w (mask w) (n * w)
      (TR (roff n (n * w) (LR (i + 1 + 1)) + k)) (TRI (roff n (n * w) (LR (i + 1 + 1)) + k)) = true)
    (hp3 : ∀ k < rcnt (LR (i + 1 + 1 + 1)), permOK n w (mask w) (n * w)
      (TR (roff n (n * w) (LR (i + 1 + 1 + 1)) + k))
      (TRI (roff n (n * w) (LR (i + 1 + 1 + 1)) + k)) = true)
    (hU : utab4F n w (mask w) (n * w) LR TR U i E D = true)
    (hV : vtab4K n w (mask w) (n * w) (pidn n w) LR TRI U BP i E D = true)
    (ha : a < rcnt (LR (i + 1))) (hb : b < rcnt (LR (i + 1 + 1)))
    (hc : c < rcnt (LR (i + 1 + 1 + 1)))
    (hG : ∀ x < n, pg w (mask w) G x =
      pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1 + 1)) + c))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + b))
          (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + a)) x))) :
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP (0 + 1 + 1 + 1) (i + 1) G = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hU' := utab4F_facts hU
  obtain ⟨hk1, hk2, hk3, hI⟩ := vtab4K_facts hV ha hb hc rfl rfl rfl
  refine sift3_of_fields hsz hb2 hb3 (by rw [hG _ hb1]) hk1 (by rw [hG _ hb2]) hk2
    (by rw [hG _ hb3]) hk3 (hp1 _ hk1) (hp2 _ hk2) (hp3 _ hk3) (fun x hx => ?_)
  obtain ⟨-, -, f1⟩ := permOK_facts (hp1 _ hk1)
  obtain ⟨-, -, f2⟩ := permOK_facts (hp2 _ hk2)
  obtain ⟨-, -, f3⟩ := permOK_facts (hp3 _ hk3)
  have hy := (f1 _ (f2 _ (f3 x hx).1).1).1
  have hId := congrArg (fun P => pg w (mask w) P x) hI
  simp only [PF.pg_pcomp hn hx, PF.pg_pidn hn24 hw hx, hU' _ hk2 _ hk3 _ hk1,
    hU' _ hb _ hc _ ha, PF.pg_pcomp hn hy] at hId
  have key := perm3_cancel (hp1 _ ha) (hp2 _ hb) (hp3 _ hc) hy
  rw [hId] at key
  rw [hG x hx]
  exact key

theorem t4K_facts {n w kS BP i T E D h j : Nat} {S SI LR TR TRI U : Nat → Nat}
    (ht : t4K n w (mask w) (n * w) S SI LR TR TRI U kS BP i T E D h j = true)
    {s th k k1 k2 k3 : Nat}
    (es : letterK S SI kS (stAt T j) = s) (eth : TR (roff n (n * w) (LR i) + h) = th)
    (ek : rpos w (mask w) (n * w) (LR i) (pg w (mask w) s (rpt w (mask w) (LR i) h)) = k)
    (ek1 : rpos w (mask w) (n * w) (LR (i + 1)) (pg w (mask w) (TRI (roff n (n * w) (LR i) + k))
      (pg w (mask w) s (pg w (mask w) th (pg w (mask w) BP (i + 1))))) = k1)
    (ek2 : rpos w (mask w) (n * w) (LR (i + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
        (pg w (mask w) (TRI (roff n (n * w) (LR i) + k))
          (pg w (mask w) s (pg w (mask w) th (pg w (mask w) BP (i + 1 + 1)))))) = k2)
    (ek3 : rpos w (mask w) (n * w) (LR (i + 1 + 1 + 1))
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1))
          (pg w (mask w) (TRI (roff n (n * w) (LR i) + k))
            (pg w (mask w) s (pg w (mask w) th (pg w (mask w) BP (i + 1 + 1 + 1))))))) = k3) :
    k < rcnt (LR i) ∧ k1 < rcnt (LR (i + 1)) ∧ k2 < rcnt (LR (i + 1 + 1)) ∧
      k3 < rcnt (LR (i + 1 + 1 + 1)) ∧
      pcomp n w (mask w) s th =
        pcomp n w (mask w) (TR (roff n (n * w) (LR i) + k)) (U (ix4 E D k1 k2 k3)) := by
  unfold t4K at ht
  simp only [strictB_eq, bAnd_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq,
    Nat.succ_eq_add_one] at ht
  subst es eth
  rw [ek] at ht
  rw [ek1] at ht
  rw [ek2] at ht
  rw [ek3] at ht
  exact ht

theorem schK_of_t4K {n w kS BP i E D : Nat} {S SI LR TR TRI U : Nat → Nat}
    (hsz : szOK n w = true)
    (hb1 : Nat.blt (pg w (mask w) BP (i + 1)) n = true)
    (hb2 : Nat.blt (pg w (mask w) BP (i + 1 + 1)) n = true)
    (hb3 : Nat.blt (pg w (mask w) BP (i + 1 + 1 + 1)) n = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 4) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (hU : utab4F n w (mask w) (n * w) LR TR U i E D = true)
    (hV : vtab4K n w (mask w) (n * w) (pidn n w) LR TRI U BP i E D = true)
    (hF : ∀ h < rcnt (LR i), ∀ j < Nat.shiftRight (stCnt (stepsAt n w S kS BP i)) (nat_lit 1),
      t4K n w (mask w) (n * w) S SI LR TR TRI U kS BP i (stepsAt n w S kS BP i) E D h j = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4) i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hb1' := Nat.blt_eq.mp hb1
  have hb2' := Nat.blt_eq.mp hb2
  have hb3' := Nat.blt_eq.mp hb3
  have hpS := allN_iff.1 hp
  obtain ⟨-, -, hR, -, -, hp0⟩ := levelK_facts (hl i (by omega))
  obtain ⟨-, -, -, -, -, hp1⟩ := levelK_facts (hl (i + 1) (by omega))
  obtain ⟨-, -, -, -, -, hp2⟩ := levelK_facts (hl (i + 1 + 1) (by omega))
  obtain ⟨-, -, -, -, -, hp3⟩ := levelK_facts (hl (i + 1 + 1 + 1) (by omega))
  have hU' := utab4F_facts hU
  generalize stepsAt n w S kS BP i = T at hinv hF hR ⊢
  unfold invTabK at hinv
  simp only [strictB_eq] at hinv
  generalize Nat.shiftRight (stCnt T) (nat_lit 1) = q at hinv hF
  simp only [bAnd_iff, Nat.beq_eq, allN_iff, Nat.blt_eq, Nat.add_eq, strictB_eq] at hinv
  obtain ⟨hr, hq⟩ := hinv
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
  by_cases hjq : j < q
  · obtain ⟨hk, hk1, hk2, hk3, hE⟩ := t4K_facts (hF _ hc j hjq) rfl rfl rfl rfl rfl rfl
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
    obtain ⟨k1, k2, k3, hk1, hk2, hk3, hE⟩ : ∃ k1 k2 k3, k1 < rcnt (LR (i + 1)) ∧
        k2 < rcnt (LR (i + 1 + 1)) ∧ k3 < rcnt (LR (i + 1 + 1 + 1)) ∧
        pcomp n w (mask w) (S (stAt T j')) (TR (roff n (n * w) (LR i) +
          rpos w (mask w) (n * w) (LR i) (pg w (mask w) (SI (stAt T j'))
            (rpt w (mask w) (LR i) (h₀ + dh))))) =
        pcomp n w (mask w) (TR (roff n (n * w) (LR i) + (h₀ + dh))) (U (ix4 E D k1 k2 k3)) :=
      ⟨_, _, _, (t4K_facts (hF _ hk j' hj') hsf rfl (k := h₀ + dh)
        (by rw [hpk, (permOK_right hpL _ hpt.1).2, hpt.2]) rfl rfl rfl).2⟩
    refine sift_of_vtab4 hsz hb1' hb2' hb3' hp1 hp2 hp3 hU hV hk1 hk2 hk3 (fun x hx => ?_)
    rw [PF.pg_pcomp hn hx, PF.pg_pcomp hn hx]
    obtain ⟨-, -, f0⟩ := permOK_facts (hp0 _ hk)
    obtain ⟨-, -, fS⟩ := permOK_facts hpL
    have hy1 := permOK_right (hp1 _ hk1) x hx
    have hy2 := permOK_right (hp2 _ hk2) _ hy1.1
    have hy3 := permOK_right (hp3 _ hk3) _ hy2.1
    have hUy := congrArg (fun P => pg w (mask w) P
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1 + 1)) + k3))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2))
          (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1)) x)))) (hU' _ hk2 _ hk3 _ hk1)
    simp only [PF.pg_pcomp hn hy3.1, hy3.2, hy2.2, hy1.2] at hUy
    have hEy := congrArg (fun P => pg w (mask w) P
      (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1 + 1)) + k3))
        (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1 + 1)) + k2))
          (pg w (mask w) (TRI (roff n (n * w) (LR (i + 1)) + k1)) x)))) hE
    simp only [PF.pg_pcomp hn hy3.1, hUy] at hEy
    rw [← hEy, (fS _ (f0 _ hy3.1).1).2, (f0 _ hy3.1).2]

theorem t4K_of_sch4F {n w kS BP i T E D NSi CH : Nat} {S SI LR TR TRI U : Nat → Nat}
    (hc : rcnt (LR i) ≤ NSi * CH)
    (h : ∀ s < NSi, sch4F n w (mask w) (n * w) S SI LR TR TRI U kS BP i T E D (s * CH) CH = true) :
    ∀ hh < rcnt (LR i), ∀ j < Nat.shiftRight (stCnt T) (nat_lit 1),
      t4K n w (mask w) (n * w) S SI LR TR TRI U kS BP i T E D hh j = true := by
  intro hh hhc j hj
  have hCH : 0 < CH := by
    rcases Nat.eq_zero_or_pos CH with h0 | h0
    · rw [h0, Nat.mul_zero] at hc
      omega
    · exact h0
  have hs := h (hh / CH) ((Nat.div_lt_iff_lt_mul hCH).2 (by omega))
  unfold sch4F at hs
  simp only [strictB_eq] at hs
  have h1 := allN_iff.1 hs (hh % CH) (Nat.mod_lt _ hCH)
  have e : Nat.add (hh / CH * CH) (hh % CH) = hh := by
    have := Nat.div_add_mod hh CH
    rw [Nat.mul_comm] at this
    exact this
  simp only [e, bIf_eq] at h1
  rw [if_pos (Nat.blt_eq.mpr hhc)] at h1
  exact allN_iff.1 h1 j hj

theorem schK_of_sch4FL {n w kS kO BP i E D NSi CH : Nat} {S SI LR TR TRI U : Nat → Nat}
    {W : List (List Int)}
    (hb1 : Nat.blt (pg w (mask w) BP (i + 1)) n = true)
    (hb2 : Nat.blt (pg w (mask w) BP (i + 1 + 1)) n = true)
    (hb3 : Nat.blt (pg w (mask w) BP (i + 1 + 1 + 1)) n = true)
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W (i + 4) BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 4) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (hU : utab4F n w (mask w) (n * w) LR TR U i E D = true)
    (hV : vtab4K n w (mask w) (n * w) (pidn n w) LR TRI U BP i E D = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, sch4F n w (mask w) (n * w) S SI LR TR TRI U kS BP i
      (stepsAt n w S kS BP i) E D (s * CH) CH = true) (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4) i
      (stepsAt n w S kS BP i) h₀ cnt = true :=
  schK_of_t4K (levelK_facts (hl i (by omega))).1 hb1 hb2 hb3 (head_facts hh).1 hl hinv hU hV
    (t4K_of_sch4F hc hs) h₀ cnt

end CFSG.KS.Raw.Orb

end
