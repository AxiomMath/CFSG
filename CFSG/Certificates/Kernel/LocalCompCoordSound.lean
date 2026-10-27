module

public import Certificates.Data.Kernel.WeylE8.Coord
public import CFSG.Certificates.Kernel.LocalCompD8Sound
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.SiftEq

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def frameRootL (L : List (List ℤ)) (i : Fin 8) : ℕ :=
  L.idxOf (vecD (2 * (i / 2)) (2 * (i / 2) + 1) 2 (if (i : ℕ) % 2 = 0 then -2 else 2))

@[expose] def frameArrL (L : List (List ℤ)) (v : FrameVec) : Array ℕ :=
  Array.ofFn (n := 240) fun i =>
    L.idxOf ((List.finRange 8).foldl (fun x k => if v k = 1 then
      reflVec (L.getD (frameRootL L k) []) x else x) (L.getD i.val []))

@[expose] def frameArrsL (L : List (List ℤ)) : Array (Array ℕ) :=
  ((List.range 256).map fun m => frameArrL L (frameDecode m)).toArray

@[expose] def wSL (L : List (List ℤ)) (G : List ℕ) : Array (Array ℕ) := (G.map (reflArrL L)).toArray

@[expose] def siftWL (L : List (List ℤ)) (G : List ℕ) (B : List (Fin 240)) (x : Array ℕ) : Bool :=
  siftA 240 (rawLevels 240 (wSL L G) (B.map Fin.val).toArray) (B.map Fin.val).toArray 0 x

@[expose] def tableOKL (L : List (List ℤ)) (G : List ℕ) (B : List (Fin 240)) (A : Array (Array ℕ))
    (p : ℕ → Bool) (sgn : ℕ → ℕ) : Bool :=
  (List.range 256).all (fun a => !p a || (isInvA 240 A[a]! A[a]! && siftWL L G B A[a]! &&
    ((240 - fixCount 240 A[a]!) / 2) % 2 == sgn a)) &&
  (List.range 256).all (fun a => !p a || (List.range 256).all fun b => !p b ||
    (eqA 240 (compA 240 A[a]! A[b]!) A[a ^^^ b]! && (a == b || !eqA 240 A[a]! A[b]!)))

@[expose] def coordCheckWithL (L : List (List ℤ)) (G : List ℕ) (B : List (Fin 240)) (K : List ℕ)
    (SA FA : Array (Array ℕ)) : Bool :=
  tableOKL L G B FA (fun _ => true) (fun a => framePop a % 2) &&
    tableOKL L G B SA (fun a => framePop a % 2 == 0) (fun _ => 0) &&
    allLt 8 (fun i => eqA 240 FA[2 ^ i]! (reflArrL L (K.getD i 0))) &&
    eqA 240 FA[255]! (negArrL L) && eqA 240 SA[255]! (negArrL L) &&
    [0, 2, 4, 6].all (fun i => eqA 240 SA[2 ^ i + 2 ^ (i + 1)]! FA[2 ^ i + 2 ^ (i + 1)]!) &&
    eqA 240 (permArrL L (Equiv.swap 0 1)) (reflArrL L 1)

theorem coordCheck_eq :
    coordCheck = coordCheckWithL rootList sgsRoots wBase keyPts (signArrsL rootList)
      (frameArrsL rootList) := rfl

end CFSG.KLC.E8

end

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

public theorem bindList_go8 {n P : Nat} : ∀ (l : List Nat) (j : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j n)
      (fun p _ ih j => bAnd(Nat.blt p (nat_lit 240),
        bAnd(Nat.beq p (pg (nat_lit 8) (nat_lit 255) P j), ih (Nat.succ j)))) l j = true →
    j + l.length = n ∧ ∀ i (hi : i < l.length), l[i] < 240 ∧ l[i] = pg 8 (mask 8) P (j + i)
  | [], j, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun i hi => absurd hi (by simp)⟩
  | p :: l, j, h => by
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨h2, h3⟩ := band_true h2
    obtain ⟨ih1, ih2⟩ := bindList_go8 l (Nat.succ j) h3
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    rcases i with _ | i
    · exact ⟨blt_true h1, Nat.eq_of_beq_eq_true h2⟩
    · have := ih2 i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      exact ⟨this.1, by rw [this.2]; congr 1; omega⟩

public theorem bindList_get {l : List Nat} {n P : Nat} (h : bindList l n P = true) {i : ℕ} (hi : i < n) :
    l.getD i 0 = pg 8 (mask 8) P i ∧ pg 8 (mask 8) P i < 240 := by
  obtain ⟨h1, h2⟩ := bindList_go8 (n := n) (P := P) l 0 h
  have hi' : i < l.length := by omega
  have := h2 i hi'
  simp only [Nat.zero_add] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some, ← this.2]
  exact ⟨rfl, this.1⟩

theorem frameKey_vec : ∀ k : Fin 8, vecOf (frameKey k) =
    vecD (2 * (k / 2)) (2 * (k / 2) + 1) 2 (if (k : ℕ) % 2 = 0 then -2 else 2) := by
  decide +kernel

theorem frameRoots_facts {L : List (List ℤ)} {RK : ℕ → ℕ} {SO FR : ℕ} (hb : bindRoots RK L = true)
    (hs : sortedOK RK SO = true) (hfr : frameRootsOK RK FR = true) (k : Fin 8) :
    pg 8 (mask 8) FR k < 240 ∧ frameRootL L k = pg 8 (mask 8) FR k := by
  obtain ⟨-, hf⟩ := bind_facts hb
  unfold frameRootsOK at hfr
  rw [Orb.allN_iff] at hfr
  have h := hfr k k.isLt
  rw [Orb.strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_true h
  have hlt : pg 8 (mask 8) FR k < 240 := blt_true h1
  have h2' : RK (pg 8 (mask 8) FR k) = frameKey k := Nat.eq_of_beq_eq_true h2
  refine ⟨hlt, ?_⟩
  have hv : L.getD (pg 8 (mask 8) FR k) [] =
      vecD (2 * (k / 2)) (2 * (k / 2) + 1) 2 (if (k : ℕ) % 2 = 0 then -2 else 2) := by
    rw [(hf _ hlt).2.2, h2', frameKey_vec k]
  unfold frameRootL
  rw [← hv, idxOf_root hb hs hlt]

theorem frameImg_zero (RK : ℕ → ℕ) (FR x : ℕ) : frameImg RK FR 0 x = x := rfl

noncomputable def fs (RK : ℕ → ℕ) (FR a k y : ℕ) : ℕ :=
  nIf(Nat.beq (Nat.land (Nat.shiftRight a k) (nat_lit 1)) (nat_lit 1),
    reflKey y (RK (pg (nat_lit 8) (nat_lit 255) FR k)), y)

theorem frameImg_eq (RK : ℕ → ℕ) (FR a x : ℕ) : frameImg RK FR a x =
    fs RK FR a 7 (fs RK FR a 6 (fs RK FR a 5 (fs RK FR a 4 (fs RK FR a 3 (fs RK FR a 2
      (fs RK FR a 1 (fs RK FR a 0 x))))))) := rfl

theorem fs_eq (RK : ℕ → ℕ) (FR a k y : ℕ) :
    fs RK FR a k y = if a.testBit k = true then reflKey y (RK (pg (nat_lit 8) (nat_lit 255) FR k))
      else y := by
  unfold fs
  rw [Orb.nIf_eq]
  have : (Nat.beq (Nat.land (Nat.shiftRight a k) (nat_lit 1)) (nat_lit 1) = true) =
      (a.testBit k = true) := by
    rw [Nat.beq_eq, eq_iff_iff]
    exact bit_testBit a k
  simp only [this]

theorem frameImg_single (RK : ℕ → ℕ) (FR x : ℕ) :
    ∀ k < 8, frameImg RK FR (1 <<< k) x = reflKey x (RK (pg (nat_lit 8) (nat_lit 255) FR k)) := by
  intro k hk
  rw [frameImg_eq]
  simp only [fs_eq, Nat.one_shiftLeft, Nat.testBit_two_pow]
  interval_cases k <;> simp

noncomputable def tk (FT : ℕ → ℕ) (k : ℕ) (j : ℕ) : ℕ := pg 8 (mask 8) (FT (1 <<< k)) j

theorem single_facts {L : List (List ℤ)} {RK FT : ℕ → ℕ} {SO FR : ℕ} (hb : bindRoots RK L = true)
    (hs : sortedOK RK SO = true) (hfr : frameRootsOK RK FR = true)
    (hft : ∀ k < 8, frameRowOK RK FR (1 <<< k) (FT (1 <<< k)) = true) (k : Fin 8) {i : ℕ}
    (hi : i < 240) :
    tk FT k i < 240 ∧ L.getD (tk FT k i) [] = reflVec (L.getD (frameRootL L k) []) (L.getD i []) := by
  obtain ⟨-, hf⟩ := bind_facts hb
  obtain ⟨hFR, hroot⟩ := frameRoots_facts hb hs hfr k
  have h := hft k k.isLt
  unfold frameRowOK at h
  rw [Orb.allN_iff] at h
  have h1 := h i hi
  rw [Orb.strictB_eq] at h1
  obtain ⟨e1, e2⟩ := band_true h1
  have he : tk FT k i < 240 := blt_true e1
  refine ⟨he, ?_⟩
  have e2' := Nat.eq_of_beq_eq_true e2
  rw [frameImg_single RK FR (RK i) k k.isLt] at e2'
  obtain ⟨xi, si, vi⟩ := hf i hi
  obtain ⟨xr, sr, vr⟩ := hf _ hFR
  obtain ⟨xe, se, ve⟩ := hf _ he
  rw [hroot, vr, vi, ve]
  exact (refl_vec xi xr xe si sr se e2').symm

noncomputable def stp (FT : ℕ → ℕ) (v : FrameVec) (j : ℕ) (k : Fin 8) : ℕ :=
  if v k = 1 then tk FT k j else j

noncomputable def tau (FT : ℕ → ℕ) (a i : ℕ) : ℕ := (List.finRange 8).foldl (stp FT (frameDecode a)) i

theorem fold_idx {L : List (List ℤ)} {RK FT : ℕ → ℕ} {SO FR : ℕ} (hb : bindRoots RK L = true)
    (hs : sortedOK RK SO = true) (hfr : frameRootsOK RK FR = true)
    (hft : ∀ k < 8, frameRowOK RK FR (1 <<< k) (FT (1 <<< k)) = true) (v : FrameVec) :
    ∀ (ks : List (Fin 8)) (j : ℕ), j < 240 →
      ks.foldl (fun x k => if v k = 1 then reflVec (L.getD (frameRootL L k) []) x else x)
        (L.getD j []) = L.getD (ks.foldl (stp FT v) j) [] ∧ ks.foldl (stp FT v) j < 240
  | [], j, hj => ⟨rfl, hj⟩
  | k :: ks, j, hj => by
    have hs1 := single_facts hb hs hfr hft k hj
    have e : (if v k = 1 then reflVec (L.getD (frameRootL L k) []) (L.getD j []) else L.getD j []) =
        L.getD (stp FT v j k) [] := by
      unfold stp
      split_ifs
      · exact hs1.2.symm
      · rfl
    have hlt : stp FT v j k < 240 := by
      unfold stp
      split_ifs
      · exact hs1.1
      · exact hj
    simp only [List.foldl_cons]
    rw [e]
    exact fold_idx hb hs hfr hft v ks _ hlt

theorem tau_lt {FT : ℕ → ℕ} (hT : ∀ k < 8, ∀ j < 240, tk FT k j < 240) (a : ℕ) :
    ∀ (ks : List (Fin 8)) (j : ℕ), j < 240 → ks.foldl (stp FT (frameDecode a)) j < 240
  | [], j, hj => hj
  | k :: ks, j, hj => by
    simp only [List.foldl_cons]
    apply tau_lt hT a ks
    unfold stp
    split_ifs
    · exact hT k k.isLt j hj
    · exact hj

theorem fold_pull {FT : ℕ → ℕ} (hT : ∀ k < 8, ∀ j < 240, tk FT k j < 240) (t : Fin 8)
    (hc : ∀ k < 8, ∀ j < 240, tk FT t (tk FT k j) = tk FT k (tk FT t j)) (w w' : FrameVec)
    (hw : w t = 1) (hw' : w' t = 0) (hww : ∀ k, k ≠ t → w k = w' k) :
    ∀ (ks : List (Fin 8)), t ∈ ks → ks.Nodup → ∀ j < 240,
      ks.foldl (stp FT w) j = ks.foldl (stp FT w') (tk FT t j)
  | [], h, _, _, _ => absurd h (by simp)
  | k :: ks, h, hnd, j, hj => by
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    by_cases hkt : k = t
    · subst hkt
      have e1 : stp FT w j k = tk FT k j := by unfold stp; rw [ite_eq_left hw]
      have e2 : stp FT w' (tk FT k j) k = tk FT k j := by
        unfold stp
        rw [ite_eq_right (by rw [hw']; decide)]
      rw [e1, e2]
      have hcong : ∀ (ks : List (Fin 8)), k ∉ ks → ∀ j, ks.foldl (stp FT w) j =
          ks.foldl (stp FT w') j := by
        intro ks
        induction ks with
        | nil => intro _ _; rfl
        | cons c cs ih =>
          intro hn j
          simp only [List.mem_cons, not_or] at hn
          simp only [List.foldl_cons]
          have : stp FT w j c = stp FT w' j c := by
            unfold stp
            rw [hww c (Ne.symm hn.1)]
          rw [this]
          exact ih hn.2 _
      exact hcong ks hnd.1 _
    · have ht : t ∈ ks := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hkt
        · exact h
      have hlt : stp FT w j k < 240 := by
        unfold stp
        split_ifs
        · exact hT k k.isLt j hj
        · exact hj
      rw [fold_pull hT t hc w w' hw hw' hww ks ht hnd.2 _ hlt]
      congr 1
      unfold stp
      rw [hww k hkt]
      split_ifs
      · exact hc k k.isLt j hj
      · rfl

theorem frameDecode_pow (t k : Fin 8) : frameDecode (2 ^ (t : ℕ)) k = if k = t then 1 else 0 := by
  unfold frameDecode
  rw [Nat.testBit_two_pow]
  by_cases h : k = t
  · simp [h]
  · have : ¬ (t : ℕ) = k := fun e => h (Fin.ext e.symm)
    simp [h, this]

theorem tau_xor {FT : ℕ → ℕ} (hT : ∀ k < 8, ∀ j < 240, tk FT k j < 240)
    (hc : ∀ t < 8, ∀ k < 8, ∀ j < 240, tk FT t (tk FT k j) = tk FT k (tk FT t j))
    (hinv : ∀ t < 8, ∀ j < 240, tk FT t (tk FT t j) = j) (a : ℕ) (t : Fin 8) {j : ℕ}
    (hj : j < 240) : tau FT (a ^^^ 2 ^ (t : ℕ)) j = tau FT a (tk FT t j) := by
  have hdec : frameDecode (a ^^^ 2 ^ (t : ℕ)) = frameDecode a + frameDecode (2 ^ (t : ℕ)) :=
    frameDecode_xor _ _
  have hoth : ∀ k, k ≠ t → frameDecode (a ^^^ 2 ^ (t : ℕ)) k = frameDecode a k := fun k hk => by
    rw [hdec, Pi.add_apply, frameDecode_pow, ite_eq_right hk, add_zero]
  have hon : frameDecode (a ^^^ 2 ^ (t : ℕ)) t = frameDecode a t + 1 := by
    rw [hdec, Pi.add_apply, frameDecode_pow, ite_eq_left rfl]
  have hmem : t ∈ List.finRange 8 := List.mem_finRange t
  have hnd : (List.finRange 8).Nodup := List.nodup_finRange 8
  rcases z2 (frameDecode a t) with h0 | h1
  · exact fold_pull hT t (hc t t.isLt) _ _ (by rw [hon, h0]; decide) h0 hoth _ hmem hnd j hj
  · have := fold_pull hT t (hc t t.isLt) (frameDecode a) (frameDecode (a ^^^ 2 ^ (t : ℕ))) h1
      (by rw [hon, h1]; decide) (fun k hk => (hoth k hk).symm) _ hmem hnd (tk FT t j)
      (hT t t.isLt j hj)
    unfold tau
    rw [this, hinv t t.isLt j hj]

theorem tau_zero (FT : ℕ → ℕ) (j : ℕ) : tau FT 0 j = j := by
  have h0 : frameDecode 0 = 0 := by
    funext i
    simp [frameDecode]
  unfold tau
  rw [h0]
  have : ∀ (ks : List (Fin 8)) (j : ℕ), ks.foldl (stp FT 0) j = j := by
    intro ks
    induction ks with
    | nil => intro j; rfl
    | cons c cs ih =>
      intro j
      simp only [List.foldl_cons]
      have : stp FT 0 j c = j := by
        unfold stp
        rw [ite_eq_right (by simp)]
      rw [this]
      exact ih j
  exact this _ j

theorem top_ind (Q : ℕ → Prop) (h0 : Q 0)
    (hstep : ∀ b s, s < 8 → b < 2 ^ s → Q b → Q (b + 2 ^ s)) : ∀ a < 256, Q a := by
  have key : ∀ t ≤ 8, ∀ a < 2 ^ t, Q a := by
    intro t
    induction t with
    | zero => intro _ a ha; have : a = 0 := by omega
              rw [this]; exact h0
    | succ t ih =>
      intro ht a ha
      by_cases hlt : a < 2 ^ t
      · exact ih (by omega) a hlt
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [pow_succ]; ring
      have e : a = (a - 2 ^ t) + 2 ^ t := by omega
      rw [e]
      exact hstep _ t (by omega) (by omega) (ih (by omega) _ (by omega))
  exact fun a ha => key 8 le_rfl a ha

theorem tau_mul {FT : ℕ → ℕ} (hT : ∀ k < 8, ∀ j < 240, tk FT k j < 240)
    (hc : ∀ t < 8, ∀ k < 8, ∀ j < 240, tk FT t (tk FT k j) = tk FT k (tk FT t j))
    (hinv : ∀ t < 8, ∀ j < 240, tk FT t (tk FT t j) = j) (a : ℕ) :
    ∀ b < 256, ∀ j < 240, tau FT a (tau FT b j) = tau FT (a ^^^ b) j := by
  refine top_ind _ ?_ ?_
  · intro j hj
    rw [tau_zero, Nat.xor_zero]
  · intro b s hs hb ih j hj
    have e : b + 2 ^ s = b ^^^ 2 ^ s := (xor_pow_add hb).symm
    rw [e, tau_xor hT hc hinv b ⟨s, hs⟩ hj, ih _ (hT s hs j hj),
      ← tau_xor hT hc hinv (a ^^^ b) ⟨s, hs⟩ hj, Nat.xor_assoc]

theorem homF_facts {FT : ℕ → ℕ} (h : homF FT = true) :
    (∀ t < 8, ∀ b < 2 ^ t, ∀ i < 240,
      pg 8 (mask 8) (FT (b + 2 ^ t)) i = pg 8 (mask 8) (FT b) (tk FT t i)) ∧
    ∀ t < 8, ∀ k < t, ∀ i < 240,
      pg 8 (mask 8) (FT (1 <<< t)) (tk FT k i) = pg 8 (mask 8) (FT (1 <<< k)) (tk FT t i) := by
  obtain ⟨h1, h2⟩ := band_true h
  rw [Orb.allN_iff] at h1
  refine ⟨fun t ht b hb i hi => ?_, fun t ht k hk i hi => ?_⟩
  · have h3 := h1 t ht
    rw [Orb.strictB_eq, Orb.strictB_eq, Orb.allN_iff] at h3
    have hm : Nat.shiftLeft (nat_lit 1) t = 2 ^ t := by
      rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul]
    rw [hm] at h3
    have e := Nat.eq_of_beq_eq_true (h3 b hb)
    have e' := congrArg (fun Y => pg 8 (mask 8) Y i) e
    simp only at e'
    change pg 8 (mask 8) (pcomp 240 8 (mask 8) (FT b) (FT (2 ^ t))) i =
      pg 8 (mask 8) (Nat.land (FT (b + 2 ^ t)) (mask (nat_lit 1920))) i at e'
    rw [PF.pg_pcomp (by norm_num) hi, pg_low8 hi] at e'
    unfold tk
    rw [Nat.one_shiftLeft]
    exact e'.symm
  · unfold commT at h2
    rw [Orb.allN_iff] at h2
    have h3 := h2 t ht
    rw [Orb.strictB_eq, Orb.allN_iff] at h3
    have h4 := h3 k hk
    rw [Orb.strictB_eq] at h4
    have e := Nat.eq_of_beq_eq_true h4
    have e' := congrArg (fun Y => pg 8 (mask 8) Y i) e
    simp only at e'
    change pg 8 (mask 8) (pcomp 240 8 (mask 8) (FT (1 <<< t)) (FT (1 <<< k))) i =
      pg 8 (mask 8) (pcomp 240 8 (mask 8) (FT (1 <<< k)) (FT (1 <<< t))) i at e'
    rw [PF.pg_pcomp (by norm_num) hi, PF.pg_pcomp (by norm_num) hi] at e'
    exact e'

theorem factAt_facts {LR TRI : ℕ → ℕ} {BP T sg : ℕ} (h : factAt LR TRI BP T sg = true) :
    permOK 240 8 (mask 8) (240 * 8) T T = true ∧ Nat.shiftRight T (240 * 8) = 0 ∧
      siftK 240 8 (mask 8) (240 * 8) (pidn 240 8) LR TRI BP 8 0 T = true ∧
      (240 - fixCntK 240 8 T) / 2 % 2 = sg := by
  unfold factAt at h
  obtain ⟨h1, h2⟩ := band_true h
  obtain ⟨h2, h3⟩ := band_true h2
  obtain ⟨h3, h4⟩ := band_true h3
  refine ⟨h1, Nat.eq_of_beq_eq_true h2, h3, ?_⟩
  have := Nat.eq_of_beq_eq_true h4
  rw [← this]
  change _ = (240 - fixCntK 240 8 T) / 2 &&& 1
  rw [Nat.and_one_is_mod]

public theorem frameArrs_get {L : List (List ℤ)} {m : ℕ} (hm : m < 256) :
    (frameArrsL L)[m]! = frameArrL L (frameDecode m) := by
  unfold frameArrsL
  rw [getElem!_pos _ m (by simp [hm])]
  simp

public theorem dotZ_ofFn (x r : Fin 8 → ℤ) : dotZ (List.ofFn x) (List.ofFn r) = ∑ j, x j * r j := by
  simp only [dotZ, List.ofFn_succ, List.ofFn_zero, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.sum_cons, List.sum_nil, Fin.sum_univ_succ, Fin.sum_univ_zero]

public theorem reflVec_ofFn (r x : Fin 8 → ℤ) : reflVec (List.ofFn r) (List.ofFn x) =
    List.ofFn (fun k => x k - (∑ j, x j * r j) / 4 * r k) := by
  rw [reflVec, dotZ_ofFn]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp

theorem refl_invol (r x : Fin 8 → ℤ) (hr : ∑ j, r j * r j = 8) :
    reflVec (List.ofFn r) (reflVec (List.ofFn r) (List.ofFn x)) = List.ofFn x := by
  rw [reflVec_ofFn, reflVec_ofFn]
  congr 1
  funext k
  have e : ∑ j, (x j - (∑ i, x i * r i) / 4 * r j) * r j =
      (∑ j, x j * r j) + (-2 * ((∑ i, x i * r i) / 4)) * 4 := by
    have : ∑ j, (x j - (∑ i, x i * r i) / 4 * r j) * r j =
        ∑ j, x j * r j - (∑ i, x i * r i) / 4 * ∑ j, r j * r j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      funext j
      ring
    rw [this, hr]
    ring
  rw [e, Int.add_mul_ediv_right _ _ (by norm_num : (4 : ℤ) ≠ 0)]
  ring

theorem frameKey_norm : ∀ k : Fin 8,
    ∑ j : Fin 8, ((cf (frameKey k) j : ℤ) - 2) * ((cf (frameKey k) j : ℤ) - 2) = 8 := by
  decide +kernel

public theorem frame_tabs {L : List (List ℤ)} {RK FT : ℕ → ℕ} {SO FR : ℕ}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true) (hfr : frameRootsOK RK FR = true)
    (hf0 : frameRowOK RK FR 0 (FT 0) = true)
    (hft : ∀ k < 8, frameRowOK RK FR (1 <<< k) (FT (1 <<< k)) = true) (kHF : homF FT = true) :
    (∀ a < 256, (frameArrsL L)[a]! = unpack 240 8 (FT a)) ∧
      (∀ a < 256, ∀ i < 240, pg 8 (mask 8) (FT a) i < 240) ∧
      (∀ a < 256, ∀ b < 256, ∀ i < 240,
        pg 8 (mask 8) (FT a) (pg 8 (mask 8) (FT b) i) = pg 8 (mask 8) (FT (a ^^^ b)) i) := by
  obtain ⟨-, hf⟩ := bind_facts hb
  have hT : ∀ k < 8, ∀ j < 240, tk FT k j < 240 := fun k hk j hj =>
    (single_facts hb hs hfr hft ⟨k, hk⟩ hj).1
  have hinvT : ∀ t < 8, ∀ j < 240, tk FT t (tk FT t j) = j := fun t ht j hj => by
    obtain ⟨h1, e1⟩ := single_facts hb hs hfr hft ⟨t, ht⟩ hj
    obtain ⟨h2, e2⟩ := single_facts hb hs hfr hft ⟨t, ht⟩ h1
    obtain ⟨hFR, hroot⟩ := frameRoots_facts hb hs hfr ⟨t, ht⟩
    have hr : L.getD (frameRootL L ⟨t, ht⟩) [] = vecOf (frameKey t) := by
      rw [hroot, (hf _ hFR).2.2]
      congr 1
      unfold frameRootsOK at hfr
      rw [Orb.allN_iff] at hfr
      have h := hfr t ht
      rw [Orb.strictB_eq] at h
      exact Nat.eq_of_beq_eq_true (band_true h).2
    have hv : L.getD (tk FT t (tk FT t j)) [] = L.getD j [] := by
      rw [e2, e1, hr, (hf j hj).2.2]
      exact refl_invol _ _ (frameKey_norm ⟨t, ht⟩)
    calc tk FT t (tk FT t j) = L.idxOf (L.getD (tk FT t (tk FT t j)) []) :=
          (idxOf_root hb hs h2).symm
      _ = L.idxOf (L.getD j []) := by rw [hv]
      _ = j := idxOf_root hb hs hj
  obtain ⟨hF1, hF2⟩ := homF_facts kHF
  have hc : ∀ t < 8, ∀ k < 8, ∀ j < 240, tk FT t (tk FT k j) = tk FT k (tk FT t j) := by
    intro t ht k hk j hj
    rcases Nat.lt_trichotomy k t with h | h | h
    · exact hF2 t ht k h j hj
    · rw [h]
    · exact (hF2 k hk t h j hj).symm
  have hFT : ∀ a < 256, ∀ i < 240, pg 8 (mask 8) (FT a) i = tau FT a i := by
    refine top_ind (fun a => ∀ i < 240, pg 8 (mask 8) (FT a) i = tau FT a i) ?_ ?_
    · intro i hi
      rw [tau_zero]
      unfold frameRowOK at hf0
      rw [Orb.allN_iff] at hf0
      have h1 := hf0 i hi
      rw [Orb.strictB_eq] at h1
      obtain ⟨e1, e2⟩ := band_true h1
      have he : pg 8 (mask 8) (FT 0) i < 240 := blt_true e1
      have e2' : RK (pg 8 (mask 8) (FT 0) i) = RK i := Nat.eq_of_beq_eq_true e2
      calc pg 8 (mask 8) (FT 0) i = L.idxOf (L.getD (pg 8 (mask 8) (FT 0) i) []) :=
            (idxOf_root hb hs he).symm
        _ = L.idxOf (L.getD i []) := by rw [(hf _ he).2.2, (hf i hi).2.2, e2']
        _ = i := idxOf_root hb hs hi
    · intro b s hs8 hb' ih i hi
      rw [hF1 s hs8 b hb' i hi, ih _ (hT s hs8 i hi), (xor_pow_add hb').symm]
      exact (tau_xor hT hc hinvT b ⟨s, hs8⟩ hi).symm
  have hFTlt : ∀ a < 256, ∀ i < 240, pg 8 (mask 8) (FT a) i < 240 := fun a ha i hi => by
    rw [hFT a ha i hi]
    exact tau_lt hT a _ i hi
  refine ⟨fun a ha => ?_, hFTlt, fun a ha b hb2 i hi => ?_⟩
  · rw [frameArrs_get ha]
    apply arr_ext8 (n := 240) (by simp [frameArrL]) (by simp [unpack])
    intro i hi
    rw [Orb.unpack_get hi, hFT a ha i hi]
    unfold frameArrL
    rw [getElem!_ofFn_nat _ hi]
    dsimp only
    rw [(fold_idx hb hs hfr hft (frameDecode a) (List.finRange 8) i hi).1,
      idxOf_root hb hs (tau_lt hT a _ i hi)]
    rfl
  · rw [hFT a ha _ (hFTlt b hb2 i hi), hFT b hb2 i hi,
      hFT _ (Nat.xor_lt_two_pow (n := 8) ha hb2) i hi, tau_mul hT hc hinvT a b hb2 i hi]

public theorem low_self {X : ℕ} (h : Nat.shiftRight X (240 * 8) = 0) : low X = X := by
  have e : low X = X &&& (2 ^ 1920 - 1) := by
    rw [← PF.mask_eq]
    rfl
  have hX : X < 2 ^ 1920 := by
    have h' : X / 2 ^ 1920 = 0 := by
      rw [← Nat.shiftRight_eq_div_pow]
      exact h
    rcases Nat.div_eq_zero_iff.1 h' with h'' | h''
    · exact absurd h'' (by positivity)
    · exact h''
  rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hX]

theorem dist_facts {T : ℕ → ℕ} {p : ℕ → Bool} (h : distK T p = true) :
    ∀ a < 256, ∀ b < a, p a = true → p b = true → low (T a) ≠ low (T b) := by
  unfold distK at h
  rw [Orb.allN_iff] at h
  intro a ha b hb hpa hpb
  have h1 := h a ha
  rw [hpa] at h1
  change strictB (low (T a)) _ = true at h1
  rw [Orb.strictB_eq] at h1
  rw [Orb.allN_iff] at h1
  have h2 := h1 b hb
  rw [hpb] at h2
  change notB' _ = true at h2
  rw [notB'_eq, Bool.not_eq_true', Bool.eq_false_iff] at h2
  intro e
  exact h2 (by rw [Nat.beq_eq]; exact e)

theorem tableOK_of {L : List (List ℤ)} {G : List ℕ} {B : List (Fin 240)} {A : Array (Array ℕ)}
    {p : ℕ → Bool} {sgn : ℕ → ℕ} {T PS PSI LR TR TRI : ℕ → ℕ} {BP : ℕ}
    (hcb : Binds 240 8 PS 13 8 BP (wSL L G) (B.map Fin.val).toArray)
    (hcp : allN 13 (fun j => permOK 240 8 (mask 8) (240 * 8) (PS j) (PSI j)) = true)
    (hcl : LevelsOK 240 8 PS PSI LR TR TRI 13 8 BP)
    (hA : ∀ a < 256, p a = true → A[a]! = unpack 240 8 (T a))
    (hf : ∀ a < 256, p a = true → factAt LR TRI BP (T a) (sgn a) = true)
    (hmul : ∀ a < 256, ∀ b < 256, p a = true → p b = true → p (a ^^^ b) = true ∧
      ∀ i < 240, pg 8 (mask 8) (T a) (pg 8 (mask 8) (T b) i) = pg 8 (mask 8) (T (a ^^^ b)) i)
    (hdist : ∀ a < 256, ∀ b < a, p a = true → p b = true → low (T a) ≠ low (T b)) :
    tableOKL L G B A p sgn = true := by
  have hlt : ∀ a < 256, p a = true → ∀ i < 240, pg 8 (mask 8) (T a) i < 240 :=
    fun a ha hp i hi => ((Orb.permOK_facts (n := 240) (w := 8) (factAt_facts (hf a ha hp)).1).2.2
      i hi).1
  have hne : ∀ a < 256, ∀ b < 256, p a = true → p b = true → a ≠ b →
      eqA 240 A[a]! A[b]! = false := by
    intro a ha b hb hpa hpb hab
    obtain ⟨-, fa2, -, -⟩ := factAt_facts (hf a ha hpa)
    obtain ⟨-, fb2, -, -⟩ := factAt_facts (hf b hb hpb)
    rw [hA a ha hpa, hA b hb hpb, eqA_low fa2, Bool.eq_false_iff]
    intro h
    have e : T a = low (T b) := Nat.eq_of_beq_eq_true h
    rcases Nat.lt_or_gt_of_ne hab with h' | h'
    · exact hdist b hb a h' hpb hpa (by rw [low_self fa2, e])
    · exact hdist a ha b h' hpa hpb (by rw [low_self fa2, e])
  unfold tableOKL
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [List.mem_range] at ha
    cases hp : p a
    · simp
    obtain ⟨f1, f2, f3, f4⟩ := factAt_facts (hf a ha hp)
    rw [hA a ha hp]
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
    refine ⟨⟨Orb.isInvA_unpack f1, ?_⟩, ?_⟩
    · unfold siftWL
      rw [CFSG.KS.Raw.siftK_eq hcb hcp hcl rfl f2 ?_]
      · exact f3
      · rw [Orb.allN_iff]
        intro i hi
        rw [Nat.blt_eq]
        exact hlt a ha hp i hi
    · rw [fixCntK_sound, f4]
      exact beq_self_eq_true _
  · rw [List.mem_range] at ha
    cases hp : p a
    · simp
    simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range]
    intro b hb
    cases hpb : p b
    · simp
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true]
    obtain ⟨hpx, hm⟩ := hmul a ha b hb hp hpb
    refine ⟨?_, ?_⟩
    · rw [hA a ha hp, hA b hb hpb, hA _ (Nat.xor_lt_two_pow (n := 8) ha hb) hpx]
      apply eqA_of
      intro i hi
      rw [compA_get hi, Orb.unpack_get hi, Orb.unpack_get (hlt b hb hpb i hi), Orb.unpack_get hi]
      exact hm i hi
    · by_cases hab : a = b
      · left
        simp [hab]
      · right
        rw [hne a ha b hb hp hpb hab]
        rfl

end CFSG.KLC.E8

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem coord_sound {L : List (List ℤ)} {G : List ℕ} {B : List (Fin 240)} {K : List ℕ}
    {RK RT ST FT PT PS PSI LR TR TRI : Nat → Nat} {SO NEG FR KP BP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hst : ∀ m < 256, signRowOK RK m (ST m) = true)
    (hfr : frameRootsOK RK FR = true) (hf0 : frameRowOK RK FR 0 (FT 0) = true)
    (hft : ∀ k < 8, frameRowOK RK FR (1 <<< k) (FT (1 <<< k)) = true)
    (hpt : swapRowOK RK 0 1 (PT 0) = true) (hK : bindList K 8 KP = true)
    (hcb : Binds 240 8 PS 13 8 BP (wSL L G) (B.map Fin.val).toArray)
    (hcp : allN 13 (fun j => permOK 240 8 (mask 8) (240 * 8) (PS j) (PSI j)) = true)
    (hcl : LevelsOK 240 8 PS PSI LR TR TRI 13 8 BP)
    (kF : factsF FT LR TRI BP = true) (kS : factsS ST LR TRI BP = true)
    (kHF : homF FT = true)
    (kDF : distK FT (fun _ => true) = true) (kDS : distK ST evenB = true)
    (kL : linksOK RT ST FT PT NEG KP = true) :
    coordCheckWithL L G B K (signArrsL L) (frameArrsL L) = true := by
  obtain ⟨hl, hf⟩ := bind_facts hb
  have hrefl := refl_sound hb hs hr
  have hsign := signs_sound hb hs hst
  have hneg := (tables_sound hb hs hr hn).2
  unfold linksOK at kL
  obtain ⟨L1, L2⟩ := band_true kL
  obtain ⟨L2, L3⟩ := band_true L2
  obtain ⟨L3, L4⟩ := band_true L3
  obtain ⟨L4, L5⟩ := band_true L4
  rw [Orb.allN_iff] at L1 L4
  unfold factsF at kF
  rw [Orb.allN_iff] at kF
  unfold factsS at kS
  rw [Orb.allN_iff] at kS
  have fF : ∀ a < 256, factAt LR TRI BP (FT a) (framePop a % 2) = true := fun a ha => by
    have h := kF a ha
    have e : Nat.land (pop8 a) (nat_lit 1) = framePop a % 2 := by
      change pop8 a &&& 1 = _
      rw [Nat.and_one_is_mod, pop8_eq]
    rwa [e] at h
  have fS : ∀ a < 256, framePop a % 2 = 0 → factAt LR TRI BP (ST a) 0 = true := fun a ha he => by
    have h := kS a ha
    have hev : evenB a = true := by
      rw [evenB_eq]
      simp [he]
    rw [hev] at h
    exact h
  obtain ⟨hFA, -, hprod⟩ := frame_tabs hb hs hfr hf0 hft kHF
  have hSA : ∀ a < 256, framePop a % 2 = 0 → (signArrsL L)[a]! = unpack 240 8 (ST a) :=
    fun a ha he => by rw [signArrs_get ha, hsign a ha he]
  have hev : ∀ a, (framePop a % 2 == 0) = true ↔ framePop a % 2 = 0 := fun a => beq_iff_eq
  unfold coordCheckWithL
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine tableOK_of (T := FT) hcb hcp hcl (fun a ha _ => hFA a ha) (fun a ha _ => fF a ha)
      (fun a ha b hb2 _ _ => ⟨rfl, hprod a ha b hb2⟩)
      (fun a ha b hb2 _ _ => dist_facts kDF a ha b hb2 rfl rfl)
  · refine tableOK_of (T := ST) hcb hcp hcl (fun a ha hp => hSA a ha ((hev a).1 hp))
      (fun a ha hp => fS a ha ((hev a).1 hp)) (fun a ha b hb2 hpa hpb => ?_)
      (fun a ha b hb2 hpa hpb => ?_)
    · obtain ⟨hx, hxe⟩ := even_xor ha hb2 ((hev a).1 hpa) ((hev b).1 hpb)
      exact ⟨(hev _).2 hxe, fun i hi =>
        (st_mul hb hs hst ha hb2 ((hev a).1 hpa) ((hev b).1 hpb) hi).symm⟩
    · have ea : evenB a = true := by rw [evenB_eq]; simpa using (hev a).1 hpa
      have eb : evenB b = true := by rw [evenB_eq]; simpa using (hev b).1 hpb
      exact dist_facts kDS a ha b hb2 ea eb
  · rw [allLt_iff]
    intro i hi
    obtain ⟨hk1, hk2⟩ := bindList_get hK hi
    have hpow : 2 ^ i < 256 := by
      calc 2 ^ i < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hi
        _ = 256 := by norm_num
    have e : FT (2 ^ i) = RT (pg 8 (mask 8) KP i) := by
      have := Nat.eq_of_beq_eq_true (L1 i hi)
      change FT (1 <<< i) = _ at this
      rwa [Nat.one_shiftLeft] at this
    rw [hFA _ hpow, hk1, hrefl _ hk2, e]
    exact eqA_of fun _ _ => rfl
  · have e : FT 255 = NEG := Nat.eq_of_beq_eq_true L2
    rw [hFA 255 (by norm_num), e, hneg]
    exact eqA_of fun _ _ => rfl
  · have e : ST 255 = NEG := Nat.eq_of_beq_eq_true L3
    rw [hSA 255 (by norm_num) (by decide), e, hneg]
    exact eqA_of fun _ _ => rfl
  · have key : ∀ j < 4, eqA 240 (signArrsL L)[3 * 2 ^ (2 * j)]! (frameArrsL L)[3 * 2 ^ (2 * j)]! =
        true := by
      intro j hj
      have hm : 3 * 2 ^ (2 * j) < 256 ∧ framePop (3 * 2 ^ (2 * j)) % 2 = 0 := by
        interval_cases j <;> decide
      have h := L4 j hj
      rw [Orb.strictB_eq] at h
      have e : ST (3 * 2 ^ (2 * j)) = FT (3 * 2 ^ (2 * j)) := by
        have := Nat.eq_of_beq_eq_true h
        change ST (3 * (1 <<< (2 * j))) = FT (3 * (1 <<< (2 * j))) at this
        rwa [Nat.one_shiftLeft] at this
      rw [hSA _ hm.1 hm.2, hFA _ hm.1, e]
      exact eqA_of fun _ _ => rfl
    rw [List.all_eq_true]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact key 0 (by norm_num)
    · exact key 1 (by norm_num)
    · exact key 2 (by norm_num)
    · exact key 3 (by norm_num)
  · have e : PT 0 = RT 1 := Nat.eq_of_beq_eq_true L5
    rw [(swap_tab hb hs hpt 0 1 rfl rfl).1, hrefl 1 (by norm_num), e]
    exact eqA_of fun _ _ => rfl

end CFSG.KLC.E8

end
