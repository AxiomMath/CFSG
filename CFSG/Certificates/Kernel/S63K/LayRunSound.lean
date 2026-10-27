module

public import Certificates.Data.D4HexGeoCheck
public import CFSG.Certificates.Kernel.S63K.OrbRunSound

public section

namespace CFSG.KC.S63K

open CFSG.D4Hex CFSG.KC.Enum CFSG.KS.SporSch.M24

abbrev LSt := Array ℕ × Array ℕ × Array ℕ

@[expose] def lY (x : ℕ) (s : LSt) (y : ℕ) : LSt :=
  if (decide (y < 3276) && s.1[y]! == 255) = true then
    (s.1.set! y (s.1[x]! + 1), s.2.1.set! y x, s.2.2.push y)
  else s

@[expose] def lH (pts ptL : Array ℕ) (s : LSt) (h : ℕ) : LSt :=
  if h < s.2.2.size then (hexNbr pts ptL s.2.2[h]!).foldl (lY s.2.2[h]!) s else s

theorem forIn_yieldL {β : Type} (g : β → ℕ → β) (f : ℕ → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) :
    ∀ (l : List ℕ) (init : β), forIn (m := Id) l init f = l.foldl g init :=
  forIn_yield g f hf

theorem hexLayBFS_eq (pts ptL : Array ℕ) (b : ℕ) :
    hexLayBFS pts ptL b = (fun s : LSt => (s.1, s.2.1))
      ((List.range' 0 3276).foldl (lH pts ptL)
        ((Array.replicate 3276 255).set! b 0, Array.replicate 3276 0, #[b])) := by
  unfold hexLayBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (lH pts ptL)]
  · rfl
  · intro h s
    obtain ⟨lay, par, q⟩ := s
    unfold lH
    dsimp only
    split
    · rw [forIn_yieldL (lY q[h]!)]
      · rfl
      · intro y t
        obtain ⟨a, b, c⟩ := t
        unfold lY
        dsimp only
        split <;> rfl
    · rfl

variable {Q QI Lay Par : ℕ → ℕ}

structure LInv (Q QI Lay Par : ℕ → ℕ) (c : ℕ) (s : LSt) : Prop where
  qsz : s.2.2.size = c
  q : ∀ i < c, s.2.2[i]! = Q i
  lsz : s.1.size = 3276
  lay : ∀ y < 3276, s.1[y]! = if QI y < c then Lay y else 255
  psz : s.2.1.size = 3276
  par : ∀ y < 3276, s.2.1[y]! = if QI y < c then Par y else 0

structure LCons (Q QI Lay Par : ℕ → ℕ) : Prop where
  q : ∀ i < 3276, Q i < 3276 ∧ QI (Q i) = i
  qi : ∀ y < 3276, QI y < 3276 ∧ Q (QI y) = y ∧ Lay y < 255
  l0 : Lay (Q 0) = 0
  p0 : Par (Q 0) = 0

theorem lCons_of (h : layConsK 3276 Q QI Lay Par = true) : LCons Q QI Lay Par := by
  unfold layConsK at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true, MatL.allN_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem layRowK_cons (x y : ℕ) (ys : List ℕ) (c : ℕ) :
    layRowK 3276 QI Lay Par x (y :: ys) c =
      if y < 3276 then
        (if QI y < c then layRowK 3276 QI Lay Par x ys c
         else if QI y = c ∧ Par y = x ∧ Lay y = Lay x + 1 then
           layRowK 3276 QI Lay Par x ys (c + 1)
         else 0)
      else 0 := by
  change strictN (QI y) (fun w =>
      nIf(Nat.blt y 3276, nIf(Nat.blt w c, layRowK 3276 QI Lay Par x ys c,
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (Par y) x, Nat.beq (Lay y) (Nat.succ (Lay x)))),
          layRowK 3276 QI Lay Par x ys (Nat.succ c), nat_lit 0)), nat_lit 0)) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq,
    Bool.and_eq_true]

theorem layRowK_mono (x : ℕ) :
    ∀ ys c, layRowK 3276 QI Lay Par x ys c ≠ 0 → c ≤ layRowK 3276 QI Lay Par x ys c := by
  intro ys
  induction ys with
  | nil => intro c _; exact Nat.le_refl c
  | cons y ys ih =>
    intro c hne
    rw [layRowK_cons] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact ih _ hne
      · rw [if_neg ‹_›]
        split at hne
        · rw [if_pos ‹_›]; exact Nat.le_of_succ_le (ih _ hne)
        · exact absurd rfl hne
    · exact absurd rfl hne

theorem layRunK_succ (nb : ℕ → List ℕ) (fuel h c : ℕ) :
    layRunK 3276 Q QI Lay Par nb (fuel + 1) h c =
      if h < c then
        (if layRowK 3276 QI Lay Par (Q h) (nb (Q h)) c = 0 then 0
         else layRunK 3276 Q QI Lay Par nb fuel (h + 1) (layRowK 3276 QI Lay Par (Q h) (nb (Q h)) c))
      else c := by
  change nIf(Nat.blt h c,
      strictN (layRowK 3276 QI Lay Par (Q h) (nb (Q h)) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, layRunK 3276 Q QI Lay Par nb fuel (Nat.succ h) c'),
      c) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, Nat.blt_eq, Nat.beq_eq]

theorem layRunK_mono (nb : ℕ → List ℕ) :
    ∀ fuel h c, layRunK 3276 Q QI Lay Par nb fuel h c ≠ 0 →
      c ≤ layRunK 3276 Q QI Lay Par nb fuel h c := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne
    rw [layRunK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · exact absurd rfl hne
      · rw [if_neg ‹_›]
        exact Nat.le_trans (layRowK_mono _ _ c ‹_›) (ih _ _ hne)
    · rw [if_neg ‹_›]

theorem inv_pushL {c : ℕ} {s : LSt} (hC : LCons Q QI Lay Par) (hs : LInv Q QI Lay Par c s)
    {x y : ℕ} (hy : y < 3276) (hw : QI y = c) (hpar : Par y = x) (hlay : Lay y = Lay x + 1)
    (hx : x < 3276) (hxc : QI x < c) :
    LInv Q QI Lay Par (c + 1) (s.1.set! y (s.1[x]! + 1), s.2.1.set! y x, s.2.2.push y) := by
  obtain ⟨hqsz, hq, hlsz, hlay', hpsz, hpar'⟩ := hs
  have hyc : Q c = y := by rw [← hw]; exact (hC.qi y hy).2.1
  have hlx : s.1[x]! = Lay x := by rw [hlay' x hx, if_pos hxc]
  have huniq : ∀ y' < 3276, QI y' = c → y' = y := fun y' hy' e => by
    rw [← (hC.qi y' hy').2.1, e, hyc]
  refine ⟨by simp [hqsz], fun i hi => ?_, by simp [hlsz], fun y' hy' => ?_, by simp [hpsz],
    fun y' hy' => ?_⟩
  · rw [push_get _ _ hqsz hi]
    split
    · exact hq i ‹_›
    · rw [← hyc]
      congr 1
      omega
  · rw [get_set _ _ (by rw [hlsz]; exact hy'), hlx]
    by_cases e : y' = y
    · subst e
      rw [if_pos rfl, hw, if_pos (Nat.lt_succ_self c), hlay]
    · rw [if_neg e, hlay' y' hy']
      by_cases h3 : QI y' < c
      · rw [if_pos h3, if_pos (by omega)]
      · have h4 : QI y' ≠ c := fun h5 => e (huniq y' hy' h5)
        rw [if_neg h3, if_neg (by omega)]
  · rw [get_set _ _ (by rw [hpsz]; exact hy')]
    by_cases e : y' = y
    · subst e
      rw [if_pos rfl, hw, if_pos (Nat.lt_succ_self c), hpar]
    · rw [if_neg e, hpar' y' hy']
      by_cases h3 : QI y' < c
      · rw [if_pos h3, if_pos (by omega)]
      · have h4 : QI y' ≠ c := fun h5 => e (huniq y' hy' h5)
        rw [if_neg h3, if_neg (by omega)]

theorem layRow_replay (hC : LCons Q QI Lay Par) {x : ℕ} (hx : x < 3276) :
    ∀ ys c (s : LSt), QI x < c → LInv Q QI Lay Par c s →
      layRowK 3276 QI Lay Par x ys c ≠ 0 →
      LInv Q QI Lay Par (layRowK 3276 QI Lay Par x ys c) (ys.foldl (lY x) s) := by
  intro ys
  induction ys with
  | nil => intro c s _ hs _; exact hs
  | cons y ys ih =>
    intro c s hxc hs hne
    rw [List.foldl_cons]
    rw [layRowK_cons] at hne ⊢
    by_cases hy : y < 3276
    · rw [if_pos hy] at hne ⊢
      have hlayy := hs.lay y hy
      unfold lY
      by_cases hw : QI y < c
      · rw [if_pos hw] at hne ⊢
        rw [if_pos hw] at hlayy
        have hcond : (decide (y < 3276) && s.1[y]! == 255) = false := by
          rw [hlayy]
          have := (hC.qi y hy).2.2
          simp [show Lay y ≠ 255 by omega]
        rw [hcond]
        exact ih c s hxc hs hne
      · rw [if_neg hw] at hne ⊢ hlayy
        by_cases hn : QI y = c ∧ Par y = x ∧ Lay y = Lay x + 1
        · rw [if_pos hn] at hne ⊢
          obtain ⟨hwc, hpc, hlc⟩ := hn
          have hcond : (decide (y < 3276) && s.1[y]! == 255) = true := by
            rw [hlayy]
            simp [hy]
          rw [if_pos hcond]
          exact ih (c + 1) _ (by omega) (inv_pushL hC hs hy hwc hpc hlc hx hxc) hne
        · rw [if_neg hn] at hne
          exact absurd rfl hne
    · rw [if_neg hy] at hne
      exact absurd rfl hne

theorem fold_idleL (pts ptL : Array ℕ) :
    ∀ m h (s : LSt), s.2.2.size ≤ h → (List.range' h m).foldl (lH pts ptL) s = s
  | 0, _, _, _ => rfl
  | m + 1, h, s, hs => by
    rw [List.range'_succ, List.foldl_cons]
    have e : lH pts ptL s h = s := by
      unfold lH
      rw [if_neg (by omega)]
    rw [e]
    exact fold_idleL pts ptL m (h + 1) s (by omega)

theorem layRun_replay {pts ptL : Array ℕ} {nb : ℕ → List ℕ} (hC : LCons Q QI Lay Par)
    (hnb : ∀ x < 3276, hexNbr pts ptL x = nb x) :
    ∀ fuel h c (s : LSt) m, h + m = 3276 → c ≤ 3276 → h ≤ c →
      LInv Q QI Lay Par c s →
      layRunK 3276 Q QI Lay Par nb fuel h c = 3276 →
      LInv Q QI Lay Par 3276 ((List.range' h m).foldl (lH pts ptL) s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s m _ _ _ _ hr
    have : layRunK 3276 Q QI Lay Par nb 0 h c = 0 := rfl
    omega
  | succ fuel ih =>
    intro h c s m hm hcN hhc hs hr
    have hmono := layRunK_mono (Q := Q) (QI := QI) (Lay := Lay) (Par := Par) nb (fuel + 1) h c
      (by omega)
    rw [layRunK_succ] at hr hmono
    by_cases hc : h < c
    · rw [if_pos hc] at hr hmono
      by_cases h0 : layRowK 3276 QI Lay Par (Q h) (nb (Q h)) c = 0
      · rw [if_pos h0] at hr
        omega
      · rw [if_neg h0] at hr hmono
        have hle : layRowK 3276 QI Lay Par (Q h) (nb (Q h)) c ≤ 3276 := by
          have := layRunK_mono (Q := Q) (QI := QI) (Lay := Lay) (Par := Par) nb fuel (h + 1)
            (layRowK 3276 QI Lay Par (Q h) (nb (Q h)) c) (by rw [hr]; omega)
          rw [hr] at this
          exact this
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [List.range'_succ, List.foldl_cons]
        have hQh := hC.q h (by omega)
        have e : lH pts ptL s h = (nb (Q h)).foldl (lY (Q h)) s := by
          unfold lH
          rw [if_pos (by rw [hs.qsz]; exact hc), hs.q h hc, hnb _ hQh.1]
        rw [e]
        have hs' := layRow_replay hC hQh.1 (nb (Q h)) c s (by rw [hQh.2]; exact hc) hs h0
        exact ih (h + 1) _ _ m' (by omega) hle
          (Nat.le_trans (Nat.succ_le_of_lt hc) (layRowK_mono _ _ c h0)) hs' hr
    · rw [if_neg hc] at hr
      subst hr
      rw [fold_idleL pts ptL m h s (by rw [hs.qsz]; omega)]
      exact hs

theorem lInv_init {b : ℕ} (hb : Q 0 = b) (hC : LCons Q QI Lay Par) :
    LInv Q QI Lay Par 1 ((Array.replicate 3276 255).set! b 0, Array.replicate 3276 0, #[b]) := by
  have hb0 := hC.q 0 (by norm_num)
  rw [hb] at hb0
  have huniq : ∀ y < 3276, QI y < 1 → y = b := fun y hy e => by
    rw [← (hC.qi y hy).2.1, show QI y = 0 by omega, hb]
  refine ⟨rfl, fun i hi => ?_, by simp, fun y hy => ?_, by simp, fun y hy => ?_⟩
  · obtain rfl : i = 0 := by omega
    rw [hb]; rfl
  · rw [get_set _ _ (by simpa using hy)]
    by_cases e : y = b
    · subst e
      rw [if_pos rfl, hb0.2, if_pos Nat.one_pos, ← hb, hC.l0]
    · rw [if_neg e, getElem!_pos _ y (by simpa using hy), Array.getElem_replicate]
      rw [if_neg (fun h1 => e (huniq y hy h1))]
  · rw [getElem!_pos _ y (by simpa using hy), Array.getElem_replicate]
    by_cases h1 : QI y < 1
    · rw [if_pos h1, huniq y hy h1, ← hb, hC.p0]
    · rw [if_neg h1]

theorem lay_final (hC : LCons Q QI Lay Par) {F : LSt} (hs : LInv Q QI Lay Par 3276 F) :
    ((fun s : LSt => (s.1, s.2.1)) F).1.size = 3276 ∧
      (∀ y < 3276, ((fun s : LSt => (s.1, s.2.1)) F).1[y]! = Lay y) ∧
      ((fun s : LSt => (s.1, s.2.1)) F).2.size = 3276 ∧
      ∀ y < 3276, ((fun s : LSt => (s.1, s.2.1)) F).2[y]! = Par y := by
  dsimp only
  refine ⟨hs.lsz, fun y hy => ?_, hs.psz, fun y hy => ?_⟩
  · rw [hs.lay y hy, if_pos (hC.qi y hy).1]
  · rw [hs.par y hy, if_pos (hC.qi y hy).1]

theorem hexLayBFS_of_K {pts ptL : Array ℕ} {nb : ℕ → List ℕ} {b : ℕ} (hb : Q 0 = b)
    (hC : LCons Q QI Lay Par) (hnb : ∀ x < 3276, hexNbr pts ptL x = nb x)
    (hrun : layRunK 3276 Q QI Lay Par nb 3277 0 1 = 3276) :
    (hexLayBFS pts ptL b).1.size = 3276 ∧ (∀ y < 3276, (hexLayBFS pts ptL b).1[y]! = Lay y) ∧
      (hexLayBFS pts ptL b).2.size = 3276 ∧ ∀ y < 3276, (hexLayBFS pts ptL b).2[y]! = Par y := by
  rw [hexLayBFS_eq]
  exact lay_final hC (layRun_replay hC hnb 3277 0 1 _ 3276 (by omega) (by omega) (by omega)
    (lInv_init hb hC) hrun)

end CFSG.KC.S63K

end
