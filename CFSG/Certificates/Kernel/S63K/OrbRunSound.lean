module

public import Certificates.Data.Kernel.S63K.OrbRun
public import Certificates.Data.D4HexOrb
public import CFSG.Certificates.Kernel.S63K.BfsSound

public section

namespace CFSG.KC.S63K

open CFSG.D4Hex CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.Monster.B.Co2.Native

abbrev OSt := Array ℕ × Array ℕ × Array ℕ × Array ℕ

@[expose] def oJ (N : ℕ) (actF : ℕ → ℕ → ℕ) (x h : ℕ) (s : OSt) (j : ℕ) : OSt :=
  if (decide (actF j x < N) && s.1[actF j x]! == N) = true then
    (s.1.set! (actF j x) s.2.1.size, s.2.1.push (actF j x), s.2.2.1.push h, s.2.2.2.push j)
  else s

@[expose] def oH (N k : ℕ) (actF : ℕ → ℕ → ℕ) (s : OSt) (h : ℕ) : OSt :=
  if h < s.2.1.size then (List.range' 0 k).foldl (oJ N actF s.2.1[h]! h) s else s

theorem orbBFS_eq (N k : ℕ) (actF : ℕ → ℕ → ℕ) (root : ℕ) :
    orbBFS N k actF root = (fun s : OSt => (⟨s.2.1, s.2.2.1, s.2.2.2, s.1⟩ : OrbRec))
      ((List.range' 0 N).foldl (oH N k actF)
        ((Array.replicate N N).set! root 0, #[root], #[0], #[0])) := by
  unfold orbBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (oH N k actF)]
  · rfl
  · intro h s
    obtain ⟨pos, ord, par, lab⟩ := s
    unfold oH
    dsimp only
    split
    · rw [forIn_yield (oJ N actF ord[h]! h)]
      · rfl
      · intro j t
        obtain ⟨a, b, c, d⟩ := t
        unfold oJ
        dsimp only
        split <;> rfl
    · rfl

theorem get_set (a : Array ℕ) {i j : ℕ} (v : ℕ) (hj : j < a.size) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  rw [getElem!_pos _ j (by simp [hj]), getElem!_pos a j hj]
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds hj]
  by_cases h : j = i
  · simp [h]
  · simp [h, Ne.symm h]

variable {N k cnt : ℕ} {actF : ℕ → ℕ → ℕ} {O Pa La Ps W : ℕ → ℕ}

structure OInv (O Pa La Ps : ℕ → ℕ) (N c : ℕ) (s : OSt) : Prop where
  osz : s.2.1.size = c
  ord : ∀ i < c, s.2.1[i]! = O i
  psz : s.2.2.1.size = c
  par : ∀ i < c, s.2.2.1[i]! = Pa i
  lsz : s.2.2.2.size = c
  lab : ∀ i < c, s.2.2.2[i]! = La i
  posz : s.1.size = N
  pos : ∀ y < N, s.1[y]! = if Ps y < c then Ps y else N

structure OCons (O Ps : ℕ → ℕ) (N cnt : ℕ) : Prop where
  cN : cnt ≤ N
  o : ∀ i < cnt, O i < N ∧ Ps (O i) = i
  p : ∀ y < N, Ps y = N ∨ (Ps y < cnt ∧ O (Ps y) = y)

theorem push_get {β : Type} [Inhabited β] (a : Array β) (x : β) {c j : ℕ} (hc : a.size = c)
    (hj : j < c + 1) : (a.push x)[j]! = if j < c then a[j]! else x := by
  rw [getElem!_pos (a.push x) j (by rw [Array.size_push]; omega)]
  by_cases h : j < c
  · rw [if_pos h, getElem!_pos a j (by omega), Array.getElem_push_lt]
  · rw [if_neg h]
    have : j = a.size := by omega
    subst this
    rw [Array.getElem_push_eq]

theorem inv_push {c : ℕ} {s : OSt} (hC : OCons O Ps N cnt) (hs : OInv O Pa La Ps N c s)
    (hc : c < cnt) {h j : ℕ} (hPa : Pa c = h) (hLa : La c = j) :
    OInv O Pa La Ps N (c + 1)
      (s.1.set! (O c) s.2.1.size, s.2.1.push (O c), s.2.2.1.push h, s.2.2.2.push j) := by
  obtain ⟨hosz, hord, hpsz, hpar, hlsz, hlab, hposz, hpos⟩ := hs
  have hOc := hC.o c hc
  refine ⟨by simp [hosz], fun i hi => ?_, by simp [hpsz], fun i hi => ?_, by simp [hlsz],
    fun i hi => ?_, by simp [hposz], fun y hy => ?_⟩
  · rw [push_get _ _ hosz hi]
    split
    · exact hord i ‹_›
    · congr 1
      omega
  · rw [push_get _ _ hpsz hi]
    split
    · exact hpar i ‹_›
    · rw [← hPa]
      congr 1
      omega
  · rw [push_get _ _ hlsz hi]
    split
    · exact hlab i ‹_›
    · rw [← hLa]
      congr 1
      omega
  · rw [get_set _ _ (by rw [hposz]; exact hy), hosz]
    by_cases e : y = O c
    · subst e
      rw [if_pos rfl, hOc.2, if_pos (Nat.lt_succ_self c)]
    · rw [if_neg e, hpos y hy]
      rcases hC.p y hy with h1 | ⟨h1, h2⟩
      · have := hC.cN
        rw [h1, if_neg (by omega), if_neg (by omega)]
      · by_cases h3 : Ps y < c
        · rw [if_pos h3, if_pos (by omega)]
        · rw [if_neg h3]
          by_cases h5 : Ps y = c
          · rw [h5] at h2
            exact absurd h2.symm e
          · rw [if_neg (by omega)]

@[expose] def OTree (actF : ℕ → ℕ → ℕ) (O Pa La : ℕ → ℕ) (k c : ℕ) : Prop :=
  ∀ i, 0 < i → i < c → Pa i < i ∧ La i < k ∧ actF (La i) (O (Pa i)) = O i

theorem orbRowK_succ (h n j c : ℕ) :
    orbRowK W Pa La k h (n + 1) j c =
      if W (k * h + j) < c then orbRowK W Pa La k h n (j + 1) c
      else if W (k * h + j) = c ∧ Pa c = h ∧ La c = j then orbRowK W Pa La k h n (j + 1) (c + 1)
      else 0 := by
  change strictN (W (Nat.add (Nat.mul k h) j)) (fun w =>
      nIf(Nat.blt w c, orbRowK W Pa La k h n (Nat.succ j) c,
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (Pa c) h, Nat.beq (La c) j)),
          orbRowK W Pa La k h n (Nat.succ j) (Nat.succ c), nat_lit 0))) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq,
    Bool.and_eq_true]
  rfl

theorem orbRowK_mono (h : ℕ) :
    ∀ n j c, orbRowK W Pa La k h n j c ≠ 0 → c ≤ orbRowK W Pa La k h n j c := by
  intro n
  induction n with
  | zero => intro j c _; exact Nat.le_refl c
  | succ n ih =>
    intro j c hne
    rw [orbRowK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]; exact ih _ _ hne
    · rw [if_neg ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact Nat.le_of_succ_le (ih _ _ hne)
      · exact absurd rfl hne

theorem orbRunK_succ (fuel h c : ℕ) :
    orbRunK W Pa La k (fuel + 1) h c =
      if h < c then
        (if orbRowK W Pa La k h k 0 c = 0 then 0
         else orbRunK W Pa La k fuel (h + 1) (orbRowK W Pa La k h k 0 c))
      else c := by
  change nIf(Nat.blt h c,
      strictN (orbRowK W Pa La k h k (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, orbRunK W Pa La k fuel (Nat.succ h) c'), c) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, Nat.blt_eq, Nat.beq_eq]

theorem orbRunK_mono :
    ∀ fuel h c, orbRunK W Pa La k fuel h c ≠ 0 → c ≤ orbRunK W Pa La k fuel h c := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne
    rw [orbRunK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · exact absurd rfl hne
      · rw [if_neg ‹_›]
        exact Nat.le_trans (orbRowK_mono h k 0 c ‹_›) (ih _ _ hne)
    · rw [if_neg ‹_›]

theorem orbRow_replay (hC : OCons O Ps N cnt)
    (hact : ∀ h < cnt, ∀ j < k, actF j (O h) = O (W (k * h + j))) {h : ℕ} :
    ∀ n j c (s : OSt), j + n ≤ k → h < c →
      OInv O Pa La Ps N c s → OTree actF O Pa La k c →
      orbRowK W Pa La k h n j c ≠ 0 → orbRowK W Pa La k h n j c ≤ cnt →
      OInv O Pa La Ps N (orbRowK W Pa La k h n j c)
          ((List.range' j n).foldl (oJ N actF (O h) h) s) ∧
        OTree actF O Pa La k (orbRowK W Pa La k h n j c) := by
  intro n
  induction n with
  | zero =>
    intro j c s _ _ hs ht _ _
    exact ⟨hs, ht⟩
  | succ n ih =>
    intro j c s hjn hhc hs ht hne hle
    have hmono := orbRowK_mono (W := W) (Pa := Pa) (La := La) (k := k) h (n + 1) j c hne
    have hcc : c ≤ cnt := Nat.le_trans hmono hle
    rw [List.range'_succ, List.foldl_cons]
    rw [orbRowK_succ] at hne hle hmono ⊢
    have hy := hact h (by omega) j (by omega)
    unfold oJ
    rw [hy]
    by_cases hw : W (k * h + j) < c
    · rw [if_pos hw] at hne hle hmono ⊢
      have hO := hC.o _ (by omega : W (k * h + j) < cnt)
      have hp := hs.pos _ hO.1
      rw [hO.2, if_pos hw] at hp
      have hcond : (decide (O (W (k * h + j)) < N) && s.1[O (W (k * h + j))]! == N) = false := by
        rw [hp]
        have : W (k * h + j) ≠ N := by have := hC.cN; omega
        simp [this]
      rw [hcond]
      exact ih (j + 1) c s (by omega) hhc hs ht hne hle
    · rw [if_neg hw] at hne hle hmono ⊢
      by_cases hn : W (k * h + j) = c ∧ Pa c = h ∧ La c = j
      · rw [if_pos hn] at hne hle hmono ⊢
        obtain ⟨hwc, hpc, hlc⟩ := hn
        have hcN : c < cnt := Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
          (Nat.le_trans (orbRowK_mono h n (j + 1) (c + 1) hne) hle)
        have hO := hC.o c hcN
        have hp := hs.pos _ hO.1
        rw [hO.2, if_neg (Nat.lt_irrefl c)] at hp
        rw [hwc]
        have hcond : (decide (O c < N) && s.1[O c]! == N) = true := by
          rw [hp]
          simp [hO.1]
        rw [if_pos hcond]
        refine ih (j + 1) (c + 1) _ (by omega) (by omega) (inv_push hC hs hcN hpc hlc)
          (fun i h0 hi => ?_) hne hle
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ht i h0 hi
        · refine ⟨by omega, by omega, ?_⟩
          rw [hpc, hlc, hy, hwc]
      · rw [if_neg hn] at hne
        exact absurd rfl hne

theorem fold_idle (actF : ℕ → ℕ → ℕ) :
    ∀ m h (s : OSt), s.2.1.size ≤ h → (List.range' h m).foldl (oH N k actF) s = s
  | 0, _, _, _ => rfl
  | m + 1, h, s, hs => by
    rw [List.range'_succ, List.foldl_cons]
    have e : oH N k actF s h = s := by
      unfold oH
      rw [if_neg (by omega)]
    rw [e]
    exact fold_idle actF m (h + 1) s (by omega)

theorem orbRun_replay (hC : OCons O Ps N cnt)
    (hact : ∀ h < cnt, ∀ j < k, actF j (O h) = O (W (k * h + j))) (hcnt : 0 < cnt) :
    ∀ fuel h c (s : OSt) m, h + m = N → c ≤ cnt →
      OInv O Pa La Ps N c s → OTree actF O Pa La k c →
      orbRunK W Pa La k fuel h c = cnt →
      OInv O Pa La Ps N cnt ((List.range' h m).foldl (oH N k actF) s) ∧
        OTree actF O Pa La k cnt := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s m _ _ _ _ hr
    have : orbRunK W Pa La k 0 h c = 0 := rfl
    omega
  | succ fuel ih =>
    intro h c s m hm hcN hs ht hr
    have hmono := orbRunK_mono (W := W) (Pa := Pa) (La := La) (k := k) (fuel + 1) h c (by omega)
    rw [orbRunK_succ] at hr hmono
    by_cases hc : h < c
    · rw [if_pos hc] at hr hmono
      by_cases h0 : orbRowK W Pa La k h k 0 c = 0
      · rw [if_pos h0] at hr
        omega
      · rw [if_neg h0] at hr hmono
        have hle : orbRowK W Pa La k h k 0 c ≤ cnt :=
          hr ▸ orbRunK_mono fuel (h + 1) _ (by omega)
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hC.cN; omega⟩
        rw [List.range'_succ, List.foldl_cons]
        have e : oH N k actF s h = (List.range' 0 k).foldl (oJ N actF (O h) h) s := by
          unfold oH
          rw [if_pos (by rw [hs.osz]; exact hc), hs.ord h hc]
        rw [e]
        obtain ⟨hs', ht'⟩ := orbRow_replay (W := W) hC hact k 0 c s (by omega) hc hs ht h0 hle
        exact ih (h + 1) _ _ m' (by omega) hle hs' ht' hr
    · rw [if_neg hc] at hr
      subst hr
      rw [fold_idle actF m h s (by rw [hs.osz]; omega)]
      exact ⟨hs, ht⟩

theorem orbBFS_of_K {root : ℕ} (hcnt : 0 < cnt) (h0 : O 0 = root) (hp0 : Pa 0 = 0)
    (hl0 : La 0 = 0) (hC : OCons O Ps N cnt)
    (hact : ∀ h < cnt, ∀ j < k, actF j (O h) = O (W (k * h + j)))
    (hrun : orbRunK W Pa La k (cnt + 1) 0 1 = cnt) :
    (orbBFS N k actF root).ord.size = cnt ∧ (∀ i < cnt, (orbBFS N k actF root).ord[i]! = O i) ∧
      (orbBFS N k actF root).par.size = cnt ∧
      (∀ i < cnt, (orbBFS N k actF root).par[i]! = Pa i) ∧
      (orbBFS N k actF root).lab.size = cnt ∧
      (∀ i < cnt, (orbBFS N k actF root).lab[i]! = La i) ∧
      (orbBFS N k actF root).pos.size = N ∧
      (∀ y < N, (orbBFS N k actF root).pos[y]! = if Ps y < cnt then Ps y else N) ∧
      OTree actF O Pa La k cnt := by
  have hr0 := hC.o 0 hcnt
  rw [h0] at hr0
  have hs0 : OInv O Pa La Ps N 1 ((Array.replicate N N).set! root 0, #[root], #[0], #[0]) := by
    refine ⟨rfl, fun i hi => ?_, rfl, fun i hi => ?_, rfl, fun i hi => ?_, by simp, fun y hy => ?_⟩
    · obtain rfl : i = 0 := by omega
      rw [h0]; rfl
    · obtain rfl : i = 0 := by omega
      rw [hp0]; rfl
    · obtain rfl : i = 0 := by omega
      rw [hl0]; rfl
    · rw [get_set _ _ (by simpa using hy)]
      by_cases e : y = root
      · subst e
        rw [if_pos rfl, hr0.2, if_pos Nat.one_pos]
      · rw [if_neg e, getElem!_pos _ y (by simpa using hy), Array.getElem_replicate]
        rcases hC.p y hy with h1 | ⟨h1, h2⟩
        · rw [h1, if_neg (by have := hC.cN; omega)]
        · by_cases h3 : Ps y < 1
          · exfalso
            have : Ps y = 0 := by omega
            rw [this, h0] at h2
            exact e h2.symm
          · rw [if_neg h3]
  have ht0 : OTree actF O Pa La k 1 := fun i h1 h2 => by omega
  obtain ⟨hs, ht⟩ := orbRun_replay (W := W) hC hact hcnt (cnt + 1) 0 1 _ N (by omega)
    (by omega) hs0 ht0 hrun
  rw [orbBFS_eq]
  exact ⟨hs.osz, hs.ord, hs.psz, hs.par, hs.lsz, hs.lab, hs.posz, hs.pos, ht⟩

end CFSG.KC.S63K

end
