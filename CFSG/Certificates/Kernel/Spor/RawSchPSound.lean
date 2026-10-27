module

public import Certificates.Data.Kernel.Spor.RawSchP
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF

theorem schP_sz {n w : Nat} (h : szOK n w = true) : n < 16777216 ∧ n + 1 < 2 ^ w := by
  unfold szOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨by simpa [Nat.blt_eq] using h1, ?_⟩
  simpa [Nat.blt_eq, Nat.shiftLeft_eq] using h2

theorem schP_ofBlt {a b : Nat} (h : Nat.blt a b = true) : a < b := Eq.mp Nat.blt_eq h

theorem schP_lt32 {n : Nat} (h : n < 16777216) : n < 2 ^ 32 :=
  Nat.lt_trans h (by decide)

theorem schP_beq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [h]
  exact Nat.beq_refl b

theorem schWalkK_zero (n w m nw : Nat) (LR TR TRI : Nat → Nat) (BP P l : Nat) (ev : Nat → Nat)
    (Q : Nat) : schWalkK n w m nw LR TR TRI BP P 0 l ev Q = bAnd(szOK n w, Nat.beq P Q) := rfl

theorem schWalkK_succ (n w m nw : Nat) (LR TR TRI : Nat → Nat) (BP P f l : Nat)
    (ev : Nat → Nat) (Q : Nat) : schWalkK n w m nw LR TR TRI BP P (f + 1) l ev Q =
    strictB (LR l) (fun R => strictB (pg w m BP l) (fun b =>
      bAnd(Nat.blt b n, strictB (rpos w m nw R (ev (pg w m P b))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (Nat.add (roff n nw R) k) (fun t => strictB (TRI t) (fun ti =>
          strictB (pcomp n w m Q (TR t)) (fun Q' =>
            schWalkK n w m nw LR TR TRI BP P f (Nat.succ l) (fun x => pg w m ti (ev x)) Q'))),
        false))))) := rfl

theorem schP_siftK_zero (n w m nw idn : Nat) (LR TRI : Nat → Nat) (BP l g : Nat) :
    siftK n w m nw idn LR TRI BP 0 l g = bAnd(szOK n w, Nat.beq g idn) := rfl

theorem schP_siftK_succ (n w m nw idn : Nat) (LR TRI : Nat → Nat) (BP f l g : Nat) :
    siftK n w m nw idn LR TRI BP (f + 1) l g =
    strictB (LR l) (fun R =>
      strictB (rpos w m nw R (pg w m g (pg w m BP l))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (pcomp n w m (TRI (Nat.add (roff n nw R) k)) g)
          (siftK n w m nw idn LR TRI BP f (Nat.succ l)),
        false))) := rfl

theorem schP_walk_sift {n w nb BP P : Nat} {LR TR TRI : Nat → Nat} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w)
    (hT : ∀ l < nb, ∀ k < rcnt (LR l), ∀ y < n,
      pg w (mask w) (TR (Nat.add (roff n (n * w) (LR l)) k)) y < n ∧
      pg w (mask w) (TRI (Nat.add (roff n (n * w) (LR l)) k))
        (pg w (mask w) (TR (Nat.add (roff n (n * w) (LR l)) k)) y) = y) :
    ∀ f l (ev : Nat → Nat) (Q g : Nat), l + f ≤ nb →
      (∀ x < n, pg w (mask w) g x = ev (pg w (mask w) P x)) →
      (∀ y < n, ev (pg w (mask w) Q y) = y) →
      g >>> (n * w) = 0 →
      schWalkK n w (mask w) (n * w) LR TR TRI BP P f l ev Q = true →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP f l g = true := by
  have hn32 := schP_lt32 hn
  have hw0 : 0 < w := w_pos hw
  intro f
  induction f with
  | zero =>
    intro l ev Q g _ hg hQ hsh h
    rw [schWalkK_zero] at h
    obtain ⟨hsz, hPQ⟩ := (bAnd_iff _ _).1 h
    have ePQ := Nat.eq_of_beq_eq_true hPQ
    rw [schP_siftK_zero]
    refine (bAnd_iff _ _).2 ⟨hsz, schP_beq ?_⟩
    refine eq_of_fields hw0 hsh (pidn_shr hn hw) fun x hx => ?_
    rw [hg x hx, ePQ, hQ x hx, pg_pidn hn hw hx]
  | succ f ih =>
    intro l ev Q g hl hg hQ hsh h
    rw [schWalkK_succ] at h
    simp only [strictB_eq] at h
    obtain ⟨hb, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hk, h⟩ := (bAnd_iff _ _).1 h
    have hbn := schP_ofBlt hb
    have hkc := schP_ofBlt hk
    rw [schP_siftK_succ]
    simp only [strictB_eq]
    rw [hg _ hbn]
    refine (bAnd_iff _ _).2 ⟨hk, ?_⟩
    refine ih _ _ _ _ (by omega) (fun x hx => ?_) (fun y hy => ?_) (pcomp_shr _ _ hn32 hw0) h
    · rw [pg_pcomp hn32 hx, hg x hx]
    · have hT' := hT l (by omega) _ hkc y hy
      rw [pg_pcomp hn32 hy, hQ _ hT'.1, hT'.2]

theorem schP_levels_perm {n w kS nb BP : Nat} {S SI LR TR TRI : Nat → Nat}
    (hl : LevelsOK n w S SI LR TR TRI kS nb BP) :
    ∀ l < nb, ∀ k < rcnt (LR l), ∀ y < n,
      pg w (mask w) (TR (Nat.add (roff n (n * w) (LR l)) k)) y < n ∧
      pg w (mask w) (TRI (Nat.add (roff n (n * w) (LR l)) k))
        (pg w (mask w) (TR (Nat.add (roff n (n * w) (LR l)) k)) y) = y := by
  intro l hl' k hk y hy
  have h := hl l hl'
  unfold levelK at h
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  simp only [bAnd_iff] at h
  have hp := allN_spec h.2.2.2.2.2.2.2.2.2.2.2.2.2 k hk
  unfold permOK at hp
  obtain ⟨_, hp⟩ := (bAnd_iff _ _).1 hp
  obtain ⟨_, hp⟩ := (bAnd_iff _ _).1 hp
  have hq := allN_spec hp y hy
  rw [strictB_eq] at hq
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 hq
  exact ⟨schP_ofBlt a, Nat.eq_of_beq_eq_true b⟩

theorem schP_levels_sz {n w kS nb BP : Nat} {S SI LR TR TRI : Nat → Nat}
    (hl : LevelsOK n w S SI LR TR TRI kS nb BP) {i : Nat} (hi : i < nb) : szOK n w = true := by
  have h := hl i hi
  unfold levelK at h
  exact ((bAnd_iff _ _).1 h).1

theorem schK_of_schK2 {n w kS BP nb i T h₀ cnt : Nat} {S SI LR TR TRI : Nat → Nat}
    (hl : LevelsOK n w S SI LR TR TRI kS nb BP) (hi : i < nb)
    (h : schK2 n w (mask w) (n * w) S SI LR TR TRI kS BP nb i T h₀ cnt = true) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP nb i T h₀ cnt = true := by
  obtain ⟨hn, hw⟩ := schP_sz (schP_levels_sz hl hi)
  have hn32 := schP_lt32 hn
  have hw0 : 0 < w := w_pos hw
  have hT := schP_levels_perm hl
  unfold schK2 at h
  unfold schK
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
    have hkc := schP_ofBlt hk
    refine schP_walk_sift hn hw hT _ _ _ _ _ (by rw [Nat.sub_eq]; omega) (fun x hx => ?_)
      (fun y hy => ?_) (pcomp_shr _ _ hn32 hw0) h2
    · rw [pg_pcomp hn32 hx]
    · exact (hT i hi _ hkc y hy).2

end CFSG.KS.Raw

end
