module

public import CFSG.Certificates.Kernel.BabyMonster.DySound
public import CFSG.Certificates.Kernel.BabyMonster.Native.DyLane

public section

namespace CFSG.KC.BM.Ln

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat

@[expose] noncomputable def dyRun (m M k : ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) dyFin
    (fun b _ ih v out j bad => Bool.rec (motive := fun _ => Nat) (ih v out (Nat.succ j) bad)
      (dyStep m M b ih v out j bad) (Nat.ble k j))

theorem dyStep_congr (m M b : ℕ) {K K' : ℕ → ℕ → ℕ → ℕ → ℕ} {j : ℕ}
    (h : ∀ v out bad, K v out (j + 1) bad = K' v out (j + 1) bad) (v out bad : ℕ) :
    dyStep m M b K v out j bad = dyStep m M b K' v out j bad := by
  cases hx : Nat.beq (Nat.land v (nat_lit 65535)) (nat_lit 0)
  · rw [dyStep_ne _ _ _ _ _ _ _ _ hx, dyStep_ne _ _ _ _ _ _ _ _ hx]
    exact h _ _ _
  · rw [dyStep_zero _ _ _ _ _ _ _ _ hx, dyStep_zero _ _ _ _ _ _ _ _ hx]
    exact h _ _ _

theorem inSkip_run (m M k : ℕ) (rest : List ℕ) {K : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hK : ∀ v out j bad, K v out j bad = dyRun m M k rest v out j bad) :
    ∀ (blk : List ℕ) v out j bad, dyInSkip m M k K blk v out j bad = dyRun m M k (blk ++ rest) v out j bad
  | [], v, out, j, bad => hK v out j bad
  | b :: blk, v, out, j, bad => by
    change Bool.rec (motive := fun _ => Nat) (dyInSkip m M k K blk v out (Nat.succ j) bad)
        (dyStep m M b (dyInSkip m M k K blk) v out j bad) (Nat.ble k j) =
      Bool.rec (motive := fun _ => Nat) (dyRun m M k (blk ++ rest) v out (Nat.succ j) bad)
        (dyStep m M b (dyRun m M k (blk ++ rest)) v out j bad) (Nat.ble k j)
    rw [inSkip_run m M k rest hK blk,
      dyStep_congr m M b (fun v out bad => inSkip_run m M k rest hK blk v out (j + 1) bad)]

theorem inNo_run (m M k : ℕ) (rest : List ℕ) {K : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hK : ∀ v out j bad, k ≤ j → K v out j bad = dyRun m M k rest v out j bad) :
    ∀ (blk : List ℕ) v out j bad, k ≤ j →
      dyInNo m M K blk v out j bad = dyRun m M k (blk ++ rest) v out j bad
  | [], v, out, j, bad, hj => hK v out j bad hj
  | b :: blk, v, out, j, bad, hj => by
    change dyStep m M b (dyInNo m M K blk) v out j bad =
      Bool.rec (motive := fun _ => Nat) (dyRun m M k (blk ++ rest) v out (Nat.succ j) bad)
        (dyStep m M b (dyRun m M k (blk ++ rest)) v out j bad) (Nat.ble k j)
    rw [Nat.ble_eq_true_of_le hj]
    exact dyStep_congr m M b (fun v out bad => inNo_run m M k rest hK blk v out (j + 1) bad (by omega))
      v out bad

theorem outer_run (m M k : ℕ) :
    ∀ (Bs : List (List ℕ)) v out j bad, dyOuter m M k Bs v out j bad = dyRun m M k Bs.flatten v out j bad
  | [], v, out, j, bad => rfl
  | blk :: Bs, v, out, j, bad => by
    change Bool.rec (motive := fun _ => Nat) (dyInSkip m M k (dyOuter m M k Bs) blk v out j bad)
        (dyInNo m M (dyOuter m M k Bs) blk v out j bad) (Nat.ble k j) = _
    rw [List.flatten_cons]
    cases h : Nat.ble k j
    · exact inSkip_run m M k _ (outer_run m M k Bs) blk v out j bad
    · exact inNo_run m M k _ (fun v out j bad _ => outer_run m M k Bs v out j bad) blk v out j bad
        (Nat.le_of_ble_eq_true h)

theorem run_skip (m M k : ℕ) : ∀ (n : ℕ) (L : List ℕ) v out j bad, j + n ≤ k → n ≤ L.length →
    dyRun m M k L v out j bad = dyRun m M k (L.drop n) v out (j + n) bad
  | 0, L, v, out, j, bad, _, _ => rfl
  | n + 1, [], v, out, j, bad, _, hL => absurd hL (by simp)
  | n + 1, b :: L, v, out, j, bad, hk, hL => by
    change Bool.rec (motive := fun _ => Nat) (dyRun m M k L v out (Nat.succ j) bad)
        (dyStep m M b (dyRun m M k L) v out j bad) (Nat.ble k j) = _
    have hb : Nat.ble k j = false := by
      cases h : Nat.ble k j
      · rfl
      · have := Nat.le_of_ble_eq_true h
        omega
    rw [hb]
    change dyRun m M k L v out (j + 1) bad = _
    rw [run_skip m M k n L v out (j + 1) bad (by omega) (by simp at hL; omega), List.drop_succ_cons,
      Nat.add_assoc, Nat.add_comm 1 n]

@[expose] noncomputable def rowsFrom (Bs : List (List ℕ)) (j : ℕ) : List ℕ := Bs.flatten.drop j

theorem rowsFrom_cons {Bs : List (List ℕ)} (hB : blocksOK Bs = true) {j : ℕ} (hj : j < 4371) :
    rowsFrom Bs j = recOf Bs j :: rowsFrom Bs (j + 1) := by
  obtain ⟨hlen, hget⟩ := blocks_flatten hB
  unfold rowsFrom
  rw [List.drop_eq_getElem_cons (by omega), hget]

theorem rowsFrom_end {Bs : List (List ℕ)} (hB : blocksOK Bs = true) : rowsFrom Bs 4371 = [] := by
  obtain ⟨hlen, -⟩ := blocks_flatten hB
  unfold rowsFrom
  rw [List.drop_eq_nil_of_le (by omega)]

theorem dyElim_run {Bs : List (List ℕ)} (hB : blocksOK Bs = true) (m : ℕ) {k : ℕ} (hk : k ≤ 4371)
    (v : ℕ) : dyElim m Bs k v = dyRun m (dyMask m) k (rowsFrom Bs k) v 0 k 0 := by
  obtain ⟨hlen, -⟩ := blocks_flatten hB
  rw [dyElim_eq, outer_run, run_skip m _ k k _ v 0 0 0 (by omega) (by omega), Nat.zero_add]
  rfl

@[expose] noncomputable def lnIn (ONE MQ SM0 MASK LMr S : ℕ) (K : ℕ → ℕ → ℕ → ℕ) :
    List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun _ Y CE bad => K Y CE bad)
    (fun p _ ih2 sh Y CE bad =>
      (fun x => (fun Q =>
        forceB (Nat.shiftRight (Nat.land (Nat.add Y (Nat.mul (Nat.sub MQ Q)
            (Nat.land (Nat.shiftRight S sh) SM0))) MASK) (nat_lit 256)) (fun Y' =>
          forceB (Nat.lor (Nat.lor bad (Nat.land x (Nat.mul (Nat.sub p (nat_lit 1)) ONE)))
              (Nat.xor (Nat.land Q ONE) (Nat.land CE LMr))) (fun bad' =>
            forceB (Nat.shiftRight CE (nat_lit 256)) (fun CE' =>
              ih2 (Nat.add sh (nat_lit 272)) Y' CE' bad'))))
        (Nat.div x p)) (Nat.land Y LMr))

@[expose] noncomputable def lnOut (ONE MQ SM0 MASK LMr : ℕ) (SS : List (List ℕ)) : ℕ → ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun Y CE bad => Nat.lor (Nat.lor bad Y) CE)
    (fun blk _ ih Y CE bad => List.rec (motive := fun _ => Nat) (nat_lit 1)
      (fun S ps _ => lnIn ONE MQ SM0 MASK LMr S ih ps (nat_lit 0) Y CE bad) blk) SS

theorem lnElimK_eq (ONE MQ SM0 MASK LMr : ℕ) (SS : List (List ℕ)) (Y CE : ℕ) :
    lnElimK ONE MQ SM0 MASK LMr SS Y CE = lnOut ONE MQ SM0 MASK LMr SS Y CE 0 := rfl

theorem lnElim_eq (m : ℕ) (SS : List (List ℕ)) (Y CE : ℕ) :
    lnElim m SS Y CE = lnOut lnOne (Nat.mul m lnOne) lnSM0 (lnMask m) lnLM SS Y CE 0 := by
  unfold lnElim
  rw [forceB_apply, forceB_apply, forceB_apply, forceB_apply, forceB_apply]
  exact lnElimK_eq _ _ _ _ _ SS Y CE

theorem lnIn_nil (ONE MQ SM0 MASK LMr S : ℕ) (K : ℕ → ℕ → ℕ → ℕ) (sh Y CE bad : ℕ) :
    lnIn ONE MQ SM0 MASK LMr S K [] sh Y CE bad = K Y CE bad := rfl

theorem lnIn_cons (ONE MQ SM0 MASK LMr S : ℕ) (K : ℕ → ℕ → ℕ → ℕ) (p : ℕ) (ps : List ℕ)
    (sh Y CE bad : ℕ) :
    lnIn ONE MQ SM0 MASK LMr S K (p :: ps) sh Y CE bad =
      lnIn ONE MQ SM0 MASK LMr S K ps (Nat.add sh (nat_lit 272))
        (Nat.shiftRight (Nat.land (Nat.add Y (Nat.mul (Nat.sub MQ (Nat.div (Nat.land Y LMr) p))
            (Nat.land (Nat.shiftRight S sh) SM0))) MASK) (nat_lit 256))
        (Nat.shiftRight CE (nat_lit 256))
        (Nat.lor (Nat.lor bad (Nat.land (Nat.land Y LMr) (Nat.mul (Nat.sub p (nat_lit 1)) ONE)))
          (Nat.xor (Nat.land (Nat.div (Nat.land Y LMr) p) ONE) (Nat.land CE LMr))) := by
  show forceB (Nat.shiftRight (Nat.land (Nat.add Y (Nat.mul (Nat.sub MQ (Nat.div (Nat.land Y LMr) p))
      (Nat.land (Nat.shiftRight S sh) SM0))) MASK) (nat_lit 256)) (fun Y' =>
    forceB (Nat.lor (Nat.lor bad (Nat.land (Nat.land Y LMr) (Nat.mul (Nat.sub p (nat_lit 1)) ONE)))
      (Nat.xor (Nat.land (Nat.div (Nat.land Y LMr) p) ONE) (Nat.land CE LMr))) (fun bad' =>
    forceB (Nat.shiftRight CE (nat_lit 256)) (fun CE' =>
      lnIn ONE MQ SM0 MASK LMr S K ps (Nat.add sh (nat_lit 272)) Y' CE' bad'))) = _
  rw [forceB_apply, forceB_apply, forceB_apply]

theorem lnOut_nil (ONE MQ SM0 MASK LMr Y CE bad : ℕ) :
    lnOut ONE MQ SM0 MASK LMr [] Y CE bad = (bad ||| Y) ||| CE := rfl

theorem lnOut_cons (ONE MQ SM0 MASK LMr S : ℕ) (ps : List ℕ) (SS : List (List ℕ)) (Y CE bad : ℕ) :
    lnOut ONE MQ SM0 MASK LMr ((S :: ps) :: SS) Y CE bad =
      lnIn ONE MQ SM0 MASK LMr S (lnOut ONE MQ SM0 MASK LMr SS) ps 0 Y CE bad := rfl

@[expose] def LnMono (K : ℕ → ℕ → ℕ → ℕ) : Prop := ∀ Y CE bad, K Y CE bad = 0 → bad = 0

theorem lnIn_mono (ONE MQ SM0 MASK LMr S : ℕ) {K : ℕ → ℕ → ℕ → ℕ} (hK : LnMono K) :
    ∀ (ps : List ℕ) (sh : ℕ), LnMono (lnIn ONE MQ SM0 MASK LMr S K ps sh)
  | [], sh => fun Y CE bad h => hK Y CE bad h
  | p :: ps, sh => fun Y CE bad h => by
    rw [lnIn_cons] at h
    have := lnIn_mono ONE MQ SM0 MASK LMr S hK ps _ _ _ _ h
    exact (Nat.or_eq_zero_iff.1 (Nat.or_eq_zero_iff.1 this).1).1

theorem lnOut_mono (ONE MQ SM0 MASK LMr : ℕ) :
    ∀ SS : List (List ℕ), LnMono (lnOut ONE MQ SM0 MASK LMr SS)
  | [] => fun Y CE bad h => by
    rw [lnOut_nil, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff] at h
    exact h.1.1
  | [] :: SS => fun Y CE bad h => absurd h (by
    change ¬ (1 : ℕ) = 0
    decide)
  | (S :: ps) :: SS => fun Y CE bad h => by
    rw [lnOut_cons] at h
    exact lnIn_mono ONE MQ SM0 MASK LMr S (lnOut_mono ONE MQ SM0 MASK LMr SS) ps 0 Y CE bad h

theorem lnDrop_eq : ∀ (k : ℕ) (L : List (List ℕ)), lnDrop k L = L.drop k
  | 0, L => rfl
  | k + 1, [] => by
    change lnDrop k [] = _
    rw [lnDrop_eq k []]
    simp
  | k + 1, x :: L => by
    change lnDrop k L = _
    rw [lnDrop_eq k L, List.drop_succ_cons]

end CFSG.KC.BM.Ln

end
