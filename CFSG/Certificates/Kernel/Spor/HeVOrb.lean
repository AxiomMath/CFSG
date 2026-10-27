module

public import Certificates.Data.CFSGNative.He.Orbit
public import Certificates.Data.Kernel.HeOrbK
public import CFSG.Certificates.Kernel.Spor.VOrbReplay
import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KS.HeVO

open CFSG.KS CFSG.KS.PEnum CFSG.KS.VO CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native
  CFSG.KS.SporSch.LyM

abbrev HSt := Array (Array Nat) × Std.HashMap (Array Nat) Nat × Table × Table × Table × Table

@[expose] def hB (p d : Nat) (B : Array (Array Nat)) (X : Array Nat) (h : Nat)
    (pts : Array (Array Nat)) (index : Std.HashMap (Array Nat) Nat) (alpha beta par lab : Table) :
    Id (ForInStep HSt) :=
  match index[mulVec p d B X]? with
  | some k => pure (ForInStep.yield (pts, index, alpha, beta.push (UInt32.ofNat k), par, lab))
  | none => pure (ForInStep.yield (pts.push (mulVec p d B X),
      index.insert (mulVec p d B X) pts.size, alpha, beta.push (UInt32.ofNat pts.size),
      par.push (UInt32.ofNat h), lab.push 2))

@[expose] def hBody (p d : Nat) (A B : Array (Array Nat)) (h : Nat) (s : HSt) :
    Id (ForInStep HSt) :=
  if h < s.1.size then
    match s.2.1[mulVec p d A s.1[h]!]? with
    | some k => hB p d B s.1[h]! h s.1 s.2.1 (s.2.2.1.push (UInt32.ofNat k)) s.2.2.2.1
        s.2.2.2.2.1 s.2.2.2.2.2
    | none => hB p d B s.1[h]! h (s.1.push (mulVec p d A s.1[h]!))
        (s.2.1.insert (mulVec p d A s.1[h]!) s.1.size)
        (s.2.2.1.push (UInt32.ofNat s.1.size)) s.2.2.2.1
        (s.2.2.2.2.1.push (UInt32.ofNat h)) (s.2.2.2.2.2.push 1)
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

theorem vecBFS_eq (p d : Nat) (A B : Array (Array Nat)) (v0 : Array Nat) (cap : Nat) :
    vecBFS p d A B v0 cap =
      let s := Id.run (forIn (List.range' 0 cap)
        ((#[v0], (∅ : Std.HashMap (Array Nat) Nat).insert v0 0, #[], #[], #[0], #[0]) : HSt)
        (hBody p d A B))
      ⟨s.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩ := by
  unfold vecBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

structure HInv (T : Nat → Array Nat) (PA LA AL BE : Nat → Nat) (c h : Nat) (s : HSt) : Prop where
  idx : VOR.HInv T id c s.2.1 s.1
  par : VOR.ArrEq s.2.2.2.2.1 c fun i => UInt32.ofNat (r32 PA i)
  lab : VOR.ArrEq s.2.2.2.2.2 c fun i => UInt32.ofNat (r32 LA i)
  al : VOR.ArrEq s.2.2.1 h fun i => UInt32.ofNat (r32 AL i)
  be : VOR.ArrEq s.2.2.2.1 h fun i => UInt32.ofNat (r32 BE i)

theorem look {T : Nat → Array Nat} {N c a : Nat} {idx : Std.HashMap (Array Nat) Nat}
    {pts : Array (Array Nat)} (hinj : ∀ i < N, ∀ j < N, T i = T j → i = j) (hcN : c ≤ N)
    (I : VOR.HInv T id c idx pts) (ha : a < N) :
    (a < c → idx[T a]? = some a) ∧
      (a = c → idx[T a]? = none ∧
        VOR.HInv T id (c + 1) (idx.insert (T a) pts.size) (pts.push (T a))) :=
  VOR.look_step (k := id) hinj hcN I ha

theorem hB_step {p d : Nat} {B : Array (Array Nat)} {T : Nat → Array Nat}
    {PA LA AL BE : Nat → Nat} {N c h : Nat} {X : Array Nat} {idx : Std.HashMap (Array Nat) Nat}
    {pts : Array (Array Nat)} {par lab al be : Table}
    (hinj : ∀ i < N, ∀ j < N, T i = T j → i = j) (hcN : c ≤ N)
    (I : VOR.HInv T id c idx pts) (hpar : VOR.ArrEq par c fun i => UInt32.ofNat (r32 PA i))
    (hlab : VOR.ArrEq lab c fun i => UInt32.ofNat (r32 LA i))
    (hal : VOR.ArrEq al (h + 1) fun i => UInt32.ofNat (r32 AL i))
    (hbe : VOR.ArrEq be h fun i => UInt32.ofNat (r32 BE i))
    (hb : mulVec p d B X = T (r32 BE h)) (hbN : r32 BE h < N)
    (hv : vstep PA LA h 2 c (r32 BE h) ≠ 0) :
    ∃ s', hB p d B X h pts idx al be par lab = pure (ForInStep.yield s') ∧
      HInv T PA LA AL BE (vstep PA LA h 2 c (r32 BE h)) (h + 1) s' := by
  have L := look hinj hcN I hbN
  unfold hB
  rw [hb]
  rcases (VOR.vstep_spec hv).2 with ⟨hlt, e⟩ | ⟨heq, hpa, hla, e⟩
  · rw [L.1 hlt, e]
    exact ⟨_, rfl, ⟨I, hpar, hlab, hal, hbe.push rfl⟩⟩
  · obtain ⟨hn, I'⟩ := L.2 heq
    rw [hn, e]
    refine ⟨_, rfl, ⟨I', hpar.push (by rw [hpa]), hlab.push (by rw [hla]; rfl), hal,
      hbe.push ?_⟩⟩
    rw [I.size, heq]

theorem hBody_step {p d N : Nat} {A B : Array (Array Nat)} {T : Nat → Array Nat}
    {AL BE PA LA : Nat → Nat}
    (hinj : ∀ i < N, ∀ j < N, T i = T j → i = j)
    (hpt : ∀ i < N, r32 AL i < N ∧ r32 BE i < N ∧
      mulVec p d A (T i) = T (r32 AL i) ∧ mulVec p d B (T i) = T (r32 BE i))
    (hcnt : vorbCnt N AL BE PA LA = N) (hN : 0 < N) {h : Nat} (hh : h < N) {s : HSt}
    (J : HInv T PA LA AL BE (vorbCnt h AL BE PA LA) h s) :
    ∃ s', hBody p d A B h s = pure (ForInStep.yield s') ∧
      HInv T PA LA AL BE (vorbCnt (h + 1) AL BE PA LA) (h + 1) s' := by
  obtain ⟨hcn, hlt⟩ := VOR.cnt_facts hN hcnt
  have hl := hlt h hh
  have h1 := (hcn (h + 1) hh).1
  obtain ⟨hc0, hcN⟩ := hcn h (by omega)
  rw [VOR.cnt_succ]
  rw [VOR.cnt_succ] at h1
  simp only [hl, ↓reduceIte] at h1 ⊢
  obtain ⟨I, hpar, hlab, hal, hbe⟩ := J
  generalize vorbCnt h AL BE PA LA = c at hl h1 hc0 hcN I hpar hlab
  obtain ⟨haN, hbN, ha, hb⟩ := hpt h hh
  have hsz : h < s.1.size := by rw [I.size]; exact hl
  have hv : s.1[h]! = T h := I.get h hl
  unfold hBody
  simp only [hsz, ↓reduceIte]
  rw [hv, ha]
  have hv1 : vstep PA LA h 1 c (r32 AL h) ≠ 0 :=
    fun e => h1 (by rw [e]; exact VOR.vstep_zero _ _ _ _ _)
  have L := look hinj hcN I haN
  rcases (VOR.vstep_spec hv1).2 with ⟨hlt1, e⟩ | ⟨heq, hpa, hla, e⟩
  · rw [L.1 hlt1]
    rw [e] at h1 ⊢
    exact hB_step hinj hcN I hpar hlab (hal.push rfl) hbe hb hbN h1
  · obtain ⟨hn, I'⟩ := L.2 heq
    rw [hn]
    rw [e] at h1 ⊢
    refine hB_step hinj (by omega) I' (hpar.push (by rw [hpa])) (hlab.push (by rw [hla]; rfl))
      (hal.push ?_) hbe hb hbN h1
    rw [I.size, heq]

@[expose] noncomputable def vRec (N : Nat) (T : Nat → Array Nat) (AL BE PA LA : Nat → Nat) :
    VOrbit :=
  ⟨Array.ofFn (n := N) fun i => T i.val,
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 AL i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 BE i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 PA i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 LA i.val)⟩

theorem vecBFS_of {p d N cap : Nat} {A B : Array (Array Nat)} {T : Nat → Array Nat}
    {AL BE PA LA : Nat → Nat} (hN : 0 < N) (hNcap : N ≤ cap)
    (hinj : ∀ i < N, ∀ j < N, T i = T j → i = j)
    (hpt : ∀ i < N, r32 AL i < N ∧ r32 BE i < N ∧
      mulVec p d A (T i) = T (r32 AL i) ∧ mulVec p d B (T i) = T (r32 BE i))
    (hcnt : vorbCnt N AL BE PA LA = N) (hpa0 : r32 PA 0 = 0) (hla0 : r32 LA 0 = 0) :
    vecBFS p d A B (T 0) cap = vRec N T AL BE PA LA := by
  have hfin : HInv T PA LA AL BE N N (Id.run (forIn (List.range' 0 cap)
      ((#[T 0], (∅ : Std.HashMap (Array Nat) Nat).insert (T 0) 0, #[], #[], #[0], #[0]) : HSt)
      (hBody p d A B))) := by
    refine TBfs.forIn_range'_done cap 0 _ _
      (fun j s => j ≤ N ∧ HInv T PA LA AL BE (vorbCnt j AL BE PA LA) j s)
      (HInv T PA LA AL BE N N) (fun j hj s hP' => ?_) (fun s hP' => ?_) ⟨Nat.zero_le _, ?_⟩
    · rw [Nat.zero_add]
      obtain ⟨hjN, J⟩ := hP'
      rcases Nat.lt_or_ge j N with hjN' | hjN'
      · left
        obtain ⟨s', e, J'⟩ := hBody_step (A := A) (B := B) hinj hpt hcnt hN hjN' J
        exact ⟨s', e, by omega, J'⟩
      · right
        have hj : j = N := by omega
        rw [hj, hcnt] at J
        refine ⟨s, ?_, J⟩
        unfold hBody
        have hn : ¬ j < s.1.size := by rw [J.idx.size]; omega
        simp only [hn, ↓reduceIte]
    · obtain ⟨hcN, J⟩ := hP'
      have : cap = N := by omega
      subst this
      rw [hcnt] at J
      exact J
    · rw [VOR.cnt_zero]
      exact ⟨VOR.hinv_init T id, VOR.arrEq_one (by rw [hpa0]; rfl),
        VOR.arrEq_one (by rw [hla0]; rfl), VOR.arrEq_nil _, VOR.arrEq_nil _⟩
  rw [vecBFS_eq]
  obtain ⟨I, hpar, hlab, hal, hbe⟩ := hfin
  unfold vRec
  simp only
  rw [VOR.ArrEq.eq_ofFn ⟨I.size, I.get⟩, hal.eq_ofFn, hbe.eq_ofFn, hpar.eq_ofFn, hlab.eq_ofFn]

@[expose] def keyOf (d w c : Nat) : Array Nat :=
  Array.ofFn (n := d) fun j => c / 2 ^ (w * j.val) % 2 ^ w

theorem div_mod_mod {x b w S : Nat} (h : b + w ≤ S) :
    x % 2 ^ S / 2 ^ b % 2 ^ w = x / 2 ^ b % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases ht : t < w
  · have : t + b < S := by omega
    simp [ht, this]
  · simp [ht]

theorem unpackL_row {d w S Y r : Nat} (hS : w * d ≤ S) (hr : r < d) :
    (unpackL d w S Y)[r]! = keyOf d w (Y / 2 ^ (S * r) % 2 ^ S) := by
  unfold unpackL keyOf
  rw [ofFn_get! _ hr]
  refine congrArg Array.ofFn (funext fun j => ?_)
  rw [land_eq, Nat.and_two_pow_sub_one_eq_mod]
  change Y >>> (S * r + w * j.val) % 2 ^ w = _
  rw [Nat.shiftRight_eq_div_pow, div_mod_mod (by have := j.isLt; nlinarith), Nat.pow_add,
    Nat.div_div_eq_div_mul]

theorem keyOf_inj {d w c c' : Nat} (hw : 0 < w) (hc : c < 2 ^ (w * d)) (hc' : c' < 2 ^ (w * d))
    (h : keyOf d w c = keyOf d w c') : c = c' := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < w * d
  · have hj : t / w < d := by
      rw [Nat.div_lt_iff_lt_mul hw]
      linarith
    have e := congrArg (fun a : Array Nat => a[t / w]!) h
    simp only [keyOf] at e
    rw [ofFn_get! _ hj, ofFn_get! _ hj] at e
    have e2 := congrArg (fun x => x.testBit (t % w)) e
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.mod_lt _ hw,
      decide_true, Bool.true_and] at e2
    have et : t % w + w * (t / w) = t := by rw [Nat.add_comm]; exact Nat.div_add_mod t w
    rwa [et] at e2
  · have h1 : c < 2 ^ t := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : c' < 2 ^ t := Nat.lt_of_lt_of_le hc' (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

theorem mulM_tr {p d : Nat} {A T X : Array (Array Nat)}
    (hT : ∀ i < d, ∀ j < d, (T[i]!)[j]! = (A[j]!)[i]!) {r : Nat} (hr : r < d) :
    (mulM p d X T)[r]! = mulVec p d A X[r]! := by
  unfold mulM mulVec
  rw [ofFn_get! _ hr]
  refine congrArg Array.ofFn (funext fun k => ?_)
  unfold dot
  rw [fold_sum, fold_sum]
  refine congrArg (· % p) (Finset.sum_congr rfl fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  unfold col
  rw [ofFn_get! _ hj', hT j hj' k k.isLt, Nat.mul_comm]

theorem trK_sound {M MT : Nat} (h : CFSG.KC.HeOrb.trK M MT = true) :
    ∀ i < 50, ∀ j < 50, ((unpackL 50 12 600 MT)[i]!)[j]! = ((unpackL 50 12 600 M)[j]!)[i]! := by
  intro i hi j hj
  have e := Nat.eq_of_beq_eq_true (allN_spec (allN_spec h i hi) j hj)
  rw [unpackL_get hi hj, unpackL_get hj hi]
  change (MT >>> (600 * i + 12 * j)) &&& (2 ^ 12 - 1) =
    (M >>> (600 * j + 12 * i)) &&& (2 ^ 12 - 1) at e
  rwa [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at e

open CFSG.KC.HeOrb CFSG.KC.Enum CFSG.KC.Ord

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem matK_spec {cA cB : List Char} {XA XB : Nat}
    (h : matK cA cB XA XB = true) :
    constsOK 7 12 600 50 8 cL cH cCM cRM cONE cLV cHV = true ∧ vldH XA = true ∧ vldH XB = true ∧
      trK (payRunP 7 50 12 600 cA 0 0 0) XA = true ∧
      trK (payRunP 7 50 12 600 cB 0 0 0) XB = true := by
  unfold matK at h
  simp only [bAnd_iff, strictB_eq'] at h
  exact h

theorem bIf_of {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem blkK_spec {PT AL BE : Nat → Nat} {XA XB s : Nat} (h : blkK PT AL BE XA XB s = true) :
    vldH (PT s) = true ∧ ∀ i, i / 32 = s → i < 8330 → r32 AL i < 8330 ∧ r32 BE i < 8330 ∧
      rowF (mulH (PT s) XA) (i % 32) = code PT (r32 AL i) ∧
      rowF (mulH (PT s) XB) (i % 32) = code PT (r32 BE i) := by
  unfold blkK at h
  rw [strictB_eq'] at h
  obtain ⟨hX, h⟩ := (bAnd_iff _ _).1 h
  rw [strictB_eq', strictB_eq'] at h
  refine ⟨hX, fun i hs hi => ?_⟩
  have h2 := allN_spec h (i % 32) (Nat.mod_lt _ (by norm_num))
  have ei : Nat.add (Nat.mul 32 s) (i % 32) = i := by
    subst hs
    change 32 * (i / 32) + i % 32 = i
    exact Nat.div_add_mod i 32
  have hi' : Nat.blt i (nat_lit 8330) = true := by rw [Nat.blt_eq]; exact hi
  rw [ei] at h2
  unfold blkRow at h2
  obtain ⟨ha, h2⟩ := (bAnd_iff _ _).1 (bIf_of h2 hi')
  obtain ⟨hb, h2⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨hA, hB⟩ := (bAnd_iff _ _).1 h2
  rw [Nat.blt_eq] at ha hb
  exact ⟨ha, hb, Nat.eq_of_beq_eq_true hA, Nat.eq_of_beq_eq_true hB⟩

theorem hdK_spec {PT AL BE PA LA : Nat → Nat} {R : List Nat} (h : hdK PT AL BE PA LA R = true) :
    r32 PA 0 = 0 ∧ r32 LA 0 = 0 ∧
      Nat.beq (vorbCnt (nat_lit 8330) AL BE PA LA) (nat_lit 8330) = true ∧
      ∀ j < 50, code PT 0 / 2 ^ (12 * j) % 2 ^ 12 = R.getD j 0 := by
  unfold hdK at h
  generalize vorbCnt (nat_lit 8330) AL BE PA LA = v at h ⊢
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  rw [strictB_eq'] at h4
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, fun j hj => ?_⟩
  have e := Nat.eq_of_beq_eq_true (allN_spec h4 j hj)
  change (code PT 0 >>> (12 * j)) &&& (2 ^ 12 - 1) = _ at e
  rwa [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] at e

theorem srtK_spec {PT SO : Nat → Nat} (h : srtK PT SO = true) :
    ∀ s < 8330, vorbSortK 8330 (code PT) SO s = true :=
  allN_spec h

theorem vRec_alpha {N : Nat} {T : Nat → Array Nat} {AL BE PA LA : Nat → Nat} {x : Nat}
    (hx : x < N) : ap (vRec N T AL BE PA LA).alpha x = r32 AL x := by
  unfold vRec
  exact TBfs.ap_ofFn hx

theorem vRec_beta {N : Nat} {T : Nat → Array Nat} {AL BE PA LA : Nat → Nat} {x : Nat}
    (hx : x < N) : ap (vRec N T AL BE PA LA).beta x = r32 BE x := by
  unfold vRec
  exact TBfs.ap_ofFn hx

theorem tabK_spec {AL : Nat → Nat} {w m P : Nat} (h : tabK AL w m P = true) :
    ∀ x < 8330, r32 AL x = pg w m P x :=
  fun x hx => Nat.eq_of_beq_eq_true (allN_spec h x hx)

end CFSG.KS.HeVO

end
