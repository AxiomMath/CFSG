module

public import Certificates.Data.Kernel.Spor.RawSchU
public import Certificates.Data.Kernel.Spor.RawSch3F
public import CFSG.Certificates.Kernel.Spor.RawSchPSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF

theorem pcomp_assoc3 {n w Q A B : Nat} (hn : n < 2 ^ 32) (hw0 : 0 < w)
    (hB : ∀ x < n, pg w (mask w) B x < n) :
    pcomp n w (mask w) (pcomp n w (mask w) Q A) B = pcomp n w (mask w) Q (pcomp n w (mask w) A B) :=
  eq_of_fields hw0 (pcomp_shr _ _ hn hw0) (pcomp_shr _ _ hn hw0) fun x hx => by
    rw [pg_pcomp hn hx, pg_pcomp hn (hB x hx), pg_pcomp hn hx, pg_pcomp hn hx]

theorem schWalkU_zero (n w m nw : Nat) (LR TR TRI U : Nat → Nat) (BP D P l : Nat)
    (ev : Nat → Nat) (Q : Nat) : schWalkU n w m nw LR TR TRI U BP D P 0 l ev Q =
    strictB (LR l) (fun R => strictB (pg w m BP l) (fun b =>
      bAnd(Nat.blt b n, strictB (rpos w m nw R (ev (pg w m P b))) (fun k =>
      bAnd(Nat.blt k (rcnt R), strictB (TRI (Nat.add (roff n nw R) k)) (fun ti =>
      strictB (LR (Nat.succ l)) (fun R2 => strictB (pg w m BP (Nat.succ l)) (fun b2 =>
      bAnd(Nat.blt b2 n, strictB (rpos w m nw R2 (pg w m ti (ev (pg w m P b2)))) (fun k2 =>
      bAnd(Nat.blt k2 (rcnt R2), bAnd(szOK n w,
        Nat.beq P (pcomp n w m Q (U (Nat.add (Nat.mul k D) k2))))))))))))))) := rfl

theorem schWalkU_succ (n w m nw : Nat) (LR TR TRI U : Nat → Nat) (BP D P f l : Nat)
    (ev : Nat → Nat) (Q : Nat) : schWalkU n w m nw LR TR TRI U BP D P (f + 1) l ev Q =
    strictB (LR l) (fun R => strictB (pg w m BP l) (fun b =>
      bAnd(Nat.blt b n, strictB (rpos w m nw R (ev (pg w m P b))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (Nat.add (roff n nw R) k) (fun t => strictB (TRI t) (fun ti =>
          strictB (pcomp n w m Q (TR t)) (fun Q' =>
            schWalkU n w m nw LR TR TRI U BP D P f (Nat.succ l) (fun x => pg w m ti (ev x)) Q'))),
        false))))) := rfl

theorem schWalkK_two (n w m nw : Nat) (LR TR TRI : Nat → Nat) (BP P l : Nat) (ev : Nat → Nat)
    (Q : Nat) : schWalkK n w m nw LR TR TRI BP P (0 + 1 + 1) l ev Q =
    strictB (LR l) (fun R => strictB (pg w m BP l) (fun b =>
      bAnd(Nat.blt b n, strictB (rpos w m nw R (ev (pg w m P b))) (fun k =>
      Bool.rec (motive := fun _ => Bool) false
        (strictB (Nat.add (roff n nw R) k) (fun t => strictB (TRI t) (fun ti =>
          strictB (pcomp n w m Q (TR t)) (fun Q' =>
          strictB (LR (Nat.succ l)) (fun R2 => strictB (pg w m BP (Nat.succ l)) (fun b2 =>
            bAnd(Nat.blt b2 n, strictB (rpos w m nw R2 (pg w m ti (ev (pg w m P b2)))) (fun k2 =>
            Bool.rec (motive := fun _ => Bool) false
              (strictB (Nat.add (roff n nw R2) k2) (fun t2 => strictB (TRI t2) (fun _ =>
                strictB (pcomp n w m Q' (TR t2)) (fun Q'' => bAnd(szOK n w, Nat.beq P Q'')))))
              (Nat.blt k2 (rcnt R2))))))))))
        (Nat.blt k (rcnt R)))))) := rfl

theorem bIf_true_of {c x : Bool} (hc : c = true) (hx : x = true) :
    Bool.rec (motive := fun _ => Bool) false x c = true := by
  subst hc
  exact hx

theorem bIf_false_mono {c x y : Bool} (h : x = true → y = true)
    (hx : Bool.rec (motive := fun _ => Bool) false x c = true) :
    Bool.rec (motive := fun _ => Bool) false y c = true := by
  cases c
  · exact absurd hx Bool.false_ne_true
  · exact h hx

theorem schWalkK_of_U {n w BP D P L : Nat} {LR TR TRI U : Nat → Nat} (hn : n < 2 ^ 32)
    (hw0 : 0 < w)
    (hT : ∀ k < rcnt (LR (L + 1)), ∀ y < n,
      pg w (mask w) (TR (Nat.add (roff n (n * w) (LR (L + 1))) k)) y < n)
    (hU : ∀ a < rcnt (LR L), ∀ b < rcnt (LR (L + 1)), U (a * D + b) =
      pcomp n w (mask w) (TR (roff n (n * w) (LR L) + a)) (TR (roff n (n * w) (LR (L + 1)) + b))) :
    ∀ f l (ev : Nat → Nat) (Q : Nat), l + f = L →
      schWalkU n w (mask w) (n * w) LR TR TRI U BP D P f l ev Q = true →
      schWalkK n w (mask w) (n * w) LR TR TRI BP P (f + 1 + 1) l ev Q = true := by
  intro f
  induction f with
  | zero =>
    intro l ev Q hl h
    have el : l = L := by omega
    subst el
    rw [schWalkU_zero] at h
    simp only [strictB_eq] at h
    obtain ⟨hb, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hk, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hb2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hk2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hsz, hP⟩ := (bAnd_iff _ _).1 h
    rw [schWalkK_two]
    simp only [strictB_eq]
    have hk' := schP_ofBlt hk
    have hk2' := schP_ofBlt hk2
    refine (bAnd_iff _ _).2 ⟨hb, bIf_true_of hk ((bAnd_iff _ _).2 ⟨hb2, bIf_true_of hk2
      ((bAnd_iff _ _).2 ⟨hsz, schP_beq ?_⟩)⟩)⟩
    simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at hP hk2' ⊢
    refine (Nat.eq_of_beq_eq_true hP).trans ?_
    rw [hU _ hk' _ hk2']
    refine (pcomp_assoc3 hn hw0 ?_).symm
    intro x hx
    exact hT _ hk2' x hx
  | succ f ih =>
    intro l ev Q hl h
    rw [schWalkU_succ] at h
    rw [schWalkK_succ]
    simp only [strictB_eq] at h ⊢
    obtain ⟨hb, h⟩ := (bAnd_iff _ _).1 h
    refine (bAnd_iff _ _).2 ⟨hb, ?_⟩
    exact bIf_false_mono (fun h' => ih _ _ _ (by omega) h') h

theorem schK2_of_schK2U {n w kS BP D L nb i T h₀ cnt : Nat} {S SI LR TR TRI U : Nat → Nat}
    (hl : LevelsOK n w S SI LR TR TRI kS nb BP) (hL : nb = L + 3) (hi : i + 3 ≤ nb)
    (hU : utabF n w (mask w) (n * w) LR TR U L D = true)
    (h : schK2U n w (mask w) (n * w) S SI LR TR TRI U kS BP D nb i T h₀ cnt = true) :
    schK2 n w (mask w) (n * w) S SI LR TR TRI kS BP nb i T h₀ cnt = true := by
  subst hL
  obtain ⟨hn, hw⟩ := schP_sz (schP_levels_sz hl (i := i) (by omega))
  have hn32 := schP_lt32 hn
  have hw0 : 0 < w := w_pos hw
  have hT := schP_levels_perm hl
  unfold utabF at hU
  simp only [strictB_eq, Orb.allN_iff, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at hU
  unfold schK2U at h
  unfold schK2
  simp only [strictB_eq] at h ⊢
  apply allN_of_forall
  intro dh hdh
  have h1 := allN_spec h dh hdh
  cases hb : Nat.blt (Nat.add h₀ dh) (rcnt (LR i))
  · rfl
  · rw [hb] at h1
    have h1' : allN (stCnt T) _ = true := h1
    refine (allN_of_forall ?_ : allN _ _ = true)
    intro j hj
    have h2 := allN_spec h1' j hj
    obtain ⟨hk, h2⟩ := (bAnd_iff _ _).1 h2
    refine (bAnd_iff _ _).2 ⟨hk, ?_⟩
    have e : Nat.sub (L + 3) (Nat.succ i) =
        Nat.sub (L + 3) (Nat.succ (Nat.succ (Nat.succ i))) + 1 + 1 := by
      simp only [Nat.sub_eq, Nat.succ_eq_add_one]
      omega
    rw [e]
    exact schWalkK_of_U (L := L + 1) hn32 hw0
      (fun k hk y hy => (hT (L + 1 + 1) (by omega) k hk y hy).1) hU _ _ _ _
      (by simp only [Nat.sub_eq, Nat.succ_eq_add_one]; omega) h2

end CFSG.KS.Raw

end
