module

public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
import CFSG.Certificates.Kernel.Spor.RawSiftB

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.Raw

@[expose] def Agr (w k X Y : Nat) : Prop := ∀ t < k, pg w (mask w) X t = pg w (mask w) Y t

theorem agr_mapB {w k nb1 nb2 l s X Y : Nat} (h1 : k ≤ nb1) (h2 : k ≤ nb2) (h : Agr w k X Y) :
    Agr w k (mapB w (mask w) nb1 l s X) (mapB w (mask w) nb2 l s Y) := by
  intro t ht
  rw [pg_mapB (by omega), pg_mapB (by omega), h t ht]

theorem agr_walkT {n w k nb1 nb2 kS T R l : Nat} {S SI : Nat → Nat} (h1 : k ≤ nb1) (h2 : k ≤ nb2) :
    ∀ f h X Y, Agr w k X Y →
      Agr w k (walkT n w (mask w) (n * w) nb1 S SI kS T R l f h X)
        (walkT n w (mask w) (n * w) nb2 S SI kS T R l f h Y) := by
  intro f
  induction f with
  | zero => exact fun _ _ _ hXY => hXY
  | succ f ih =>
    intro h X Y hXY
    rcases Nat.eq_zero_or_pos h with rfl | h0
    · exact hXY
    · rw [walkT_succ_pos f h0, walkT_succ_pos f h0]
      exact agr_mapB h1 h2 (ih _ X Y hXY)

theorem agr_walkIT {n w k nb1 nb2 kS T R l : Nat} {S SI : Nat → Nat} (h1 : k ≤ nb1)
    (h2 : k ≤ nb2) :
    ∀ f h X Y, Agr w k X Y →
      Agr w k (walkIT n w (mask w) (n * w) nb1 S SI kS T R l f h X)
        (walkIT n w (mask w) (n * w) nb2 S SI kS T R l f h Y) := by
  intro f
  induction f with
  | zero => exact fun _ _ _ hXY => hXY
  | succ f ih =>
    intro h X Y hXY
    rcases Nat.eq_zero_or_pos h with rfl | h0
    · exact hXY
    · rw [walkIT_succ_pos f h0, walkIT_succ_pos f h0]
      exact ih _ _ _ (agr_mapB h1 h2 hXY)

theorem siftBK_trunc {n w nb1 nb2 kS : Nat} {S SI LR ST LR' ST' : Nat → Nat} (h12 : nb2 ≤ nb1)
    (hLR : ∀ l < nb2, LR' l = LR l) (hST : ∀ l < nb2, ST' l = ST l) (e : Nat) :
    ∀ f l X Y, Agr w nb2 X Y → l + f ≤ nb2 →
      siftBK n w (mask w) (n * w) nb1 S SI LR ST kS (f + e) l X = true →
      siftBK n w (mask w) (n * w) nb2 S SI LR' ST' kS f l Y = true := by
  intro f
  induction f with
  | zero => exact fun _ _ _ _ _ _ => rfl
  | succ f ih =>
    intro l X Y hXY hl h
    have hf : f + 1 + e = (f + e) + 1 := by omega
    rw [hf, siftBK_succ] at h
    rw [siftBK_succ, hLR l (by omega), hST l (by omega), ← hXY l (by omega)]
    simp only [strictB_eq] at h ⊢
    obtain ⟨hc, h'⟩ := (bAnd_iff _ _).1 h
    refine (bAnd_iff _ _).2 ⟨hc, ih (l + 1) _ _ ?_ (by omega) h'⟩
    exact agr_walkIT h12 le_rfl _ _ _ _ hXY

theorem schBPt_trunc {n w nb1 nb2 kS BP BP' i h : Nat} {S SI LR ST LR' ST' : Nat → Nat}
    (h12 : nb2 ≤ nb1) (hi : i < nb2) (hLR : ∀ l < nb2, LR' l = LR l)
    (hST : ∀ l < nb2, ST' l = ST l) (hBP : Agr w nb2 BP BP')
    (hs : schBPt n w (mask w) (n * w) nb1 S SI LR ST kS BP i h = true) :
    schBPt n w (mask w) (n * w) nb2 S SI LR' ST' kS BP' i h = true := by
  unfold schBPt at hs ⊢
  rw [hLR i hi, hST i hi]
  simp only [strictB_eq] at hs ⊢
  refine allN_of_forall fun j hj => ?_
  obtain ⟨hk, h2⟩ := (bAnd_iff _ _).1 (allN_spec hs j hj)
  refine (bAnd_iff _ _).2 ⟨hk, ?_⟩
  have ef : Nat.sub nb1 (Nat.succ i) = Nat.sub nb2 (Nat.succ i) + (nb1 - nb2) := by
    simp only [Nat.sub_eq]
    omega
  rw [ef] at h2
  refine siftBK_trunc h12 hLR hST (nb1 - nb2) _ _ _ _ ?_ (by simp only [Nat.sub_eq]; omega) h2
  exact agr_walkIT h12 le_rfl _ _ _ _ (agr_mapB h12 le_rfl (agr_walkT h12 le_rfl _ _ _ _ hBP))

theorem schBOK_trunc {n w nb nb' kS BP BP' : Nat} {S SI S' SI' LR ST LR' ST' : Nat → Nat}
    (hnb : nb' ≤ nb) (hs : SchBOK n w nb S SI LR ST kS BP) (hS : S' = S) (hSI : SI' = SI)
    (hLR : ∀ l < nb', LR' l = LR l) (hST : ∀ l < nb', ST' l = ST l)
    (hBP : ∀ t < nb', pg w (mask w) BP t = pg w (mask w) BP' t) :
    SchBOK n w nb' S' SI' LR' ST' kS BP' := by
  subst hS hSI
  intro i hi h hh
  rw [hLR i hi] at hh
  exact schBPt_trunc hnb hi hLR hST hBP (hs i (by omega) h hh)

end CFSG.KS.Raw.Orb

end
