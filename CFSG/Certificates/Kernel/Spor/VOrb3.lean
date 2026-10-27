module

public import CFSG.Certificates.Kernel.Spor.F3R
public import Certificates.Data.CFSGNative.McL.VecOrbit
public import CFSG.Certificates.Kernel.Spor.VOrbReplay
import CFSG.Certificates.Kernel.Spor.VOrbSound
import CFSG.Certificates.Kernel.Spor.PChainSound

public section

namespace CFSG.KS.VO3

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.VO CFSG.KS.F3R CFSG.F3.Native
  CFSG.Sporadic.VecOrbit.Native CFSG.Sporadic.Th.Native

@[expose] def decV3 (c : Nat) : V := ⟨c &&& (2 ^ 32 - 1), c >>> 32⟩

@[expose] noncomputable def v3PtK (d N : Nat) (AT BT : Array V) (PT AL BE : Nat → Nat) (i : Nat) : Bool :=
  (decV3 (PT i)).canon d && r32 AL i < N && r32 BE i < N &&
    (combK d AT (decV3 (PT i))).beq (decV3 (PT (r32 AL i))) &&
    (combK d BT (decV3 (PT i))).beq (decV3 (PT (r32 BE i)))

@[expose] noncomputable def v3HdK (d N cap : Nat) (v0 : V) (PT AL BE PA LA : Nat → Nat) : Bool :=
  0 < N && N ≤ cap && N < 2 ^ 32 && d ≤ 32 && (decV3 (PT 0)).beq v0 && r32 PA 0 == 0 &&
    r32 LA 0 == 0 && vorbCnt N AL BE PA LA == N

@[expose] noncomputable def v3Rec (N : Nat) (PT AL BE PA LA : Nat → Nat) : VOrbit :=
  ⟨Array.ofFn (n := N) fun i => decV3 (PT i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 AL i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 BE i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 PA i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 LA i.val)⟩

abbrev VSt := Array V × Std.HashMap (Nat × Nat) Nat × Table × Table × Table × Table

@[expose] def vB (d : Nat) (BT : Array V) (X : V) (h : Nat) (pts : Array V)
    (index : Std.HashMap (Nat × Nat) Nat) (alpha beta par lab : Table) : Id (ForInStep VSt) :=
  match index[vkey (comb d BT X)]? with
  | some k => pure (ForInStep.yield (pts, index, alpha, beta.push (UInt32.ofNat k), par, lab))
  | none => pure (ForInStep.yield (pts.push (comb d BT X),
      index.insert (vkey (comb d BT X)) pts.size, alpha, beta.push (UInt32.ofNat pts.size),
      par.push (UInt32.ofNat h), lab.push 2))

@[expose] def vBody (d : Nat) (AT BT : Array V) (h : Nat) (s : VSt) : Id (ForInStep VSt) :=
  if h < s.1.size then
    match s.2.1[vkey (comb d AT s.1[h]!)]? with
    | some k => vB d BT s.1[h]! h s.1 s.2.1 (s.2.2.1.push (UInt32.ofNat k)) s.2.2.2.1
        s.2.2.2.2.1 s.2.2.2.2.2
    | none => vB d BT s.1[h]! h (s.1.push (comb d AT s.1[h]!))
        (s.2.1.insert (vkey (comb d AT s.1[h]!)) s.1.size)
        (s.2.2.1.push (UInt32.ofNat s.1.size)) s.2.2.2.1
        (s.2.2.2.2.1.push (UInt32.ofNat h)) (s.2.2.2.2.2.push 1)
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

theorem vecBFS_eq (d : Nat) (AT BT : Array V) (v0 : V) (cap : Nat) : vecBFS d AT BT v0 cap =
    let s := Id.run (forIn (List.range' 0 cap)
      ((#[v0], (∅ : Std.HashMap (Nat × Nat) Nat).insert (vkey v0) 0, #[], #[], #[0], #[0]) : VSt)
      (vBody d AT BT))
    ⟨s.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩ := by
  unfold vecBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

structure VInv (T : Nat → V) (PA LA AL BE : Nat → Nat) (c h : Nat) (s : VSt) : Prop where
  idx : VOR.HInv T vkey c s.2.1 s.1
  par : VOR.ArrEq s.2.2.2.2.1 c fun i => UInt32.ofNat (r32 PA i)
  lab : VOR.ArrEq s.2.2.2.2.2 c fun i => UInt32.ofNat (r32 LA i)
  al : VOR.ArrEq s.2.2.1 h fun i => UInt32.ofNat (r32 AL i)
  be : VOR.ArrEq s.2.2.2.1 h fun i => UInt32.ofNat (r32 BE i)

theorem vB_step {d : Nat} {BT : Array V} {T : Nat → V} {PA LA AL BE : Nat → Nat} {N c h : Nat}
    {X : V} {idx : Std.HashMap (Nat × Nat) Nat} {pts : Array V} {par lab al be : Table}
    (hinj : ∀ i < N, ∀ j < N, vkey (T i) = vkey (T j) → i = j) (hcN : c ≤ N)
    (I : VOR.HInv T vkey c idx pts) (hpar : VOR.ArrEq par c fun i => UInt32.ofNat (r32 PA i))
    (hlab : VOR.ArrEq lab c fun i => UInt32.ofNat (r32 LA i))
    (hal : VOR.ArrEq al (h + 1) fun i => UInt32.ofNat (r32 AL i))
    (hbe : VOR.ArrEq be h fun i => UInt32.ofNat (r32 BE i))
    (hb : comb d BT X = T (r32 BE h)) (hbN : r32 BE h < N)
    (hv : vstep PA LA h 2 c (r32 BE h) ≠ 0) :
    ∃ s', vB d BT X h pts idx al be par lab = pure (ForInStep.yield s') ∧
      VInv T PA LA AL BE (vstep PA LA h 2 c (r32 BE h)) (h + 1) s' := by
  have L := VOR.look_step hinj hcN I hbN
  unfold vB
  rw [hb]
  rcases (VOR.vstep_spec hv).2 with ⟨hlt, e⟩ | ⟨heq, hpa, hla, e⟩
  · rw [L.1 hlt, e]
    exact ⟨_, rfl, ⟨I, hpar, hlab, hal, hbe.push rfl⟩⟩
  · obtain ⟨hn, I'⟩ := L.2 heq
    rw [hn, e]
    refine ⟨_, rfl, ⟨I', hpar.push (by rw [hpa]), hlab.push (by rw [hla]; rfl), hal,
      hbe.push ?_⟩⟩
    rw [I.size, heq]

theorem vBody_step {d N : Nat} {AT BT : Array V} {PT AL BE PA LA : Nat → Nat}
    (hinj : ∀ i < N, ∀ j < N, vkey (decV3 (PT i)) = vkey (decV3 (PT j)) → i = j)
    (hpt : ∀ i < N, r32 AL i < N ∧ r32 BE i < N ∧
      comb d AT (decV3 (PT i)) = decV3 (PT (r32 AL i)) ∧
      comb d BT (decV3 (PT i)) = decV3 (PT (r32 BE i)))
    (hcnt : vorbCnt N AL BE PA LA = N) (hN : 0 < N) {h : Nat} (hh : h < N) {s : VSt}
    (J : VInv (fun i => decV3 (PT i)) PA LA AL BE (vorbCnt h AL BE PA LA) h s) :
    ∃ s', vBody d AT BT h s = pure (ForInStep.yield s') ∧
      VInv (fun i => decV3 (PT i)) PA LA AL BE (vorbCnt (h + 1) AL BE PA LA) (h + 1) s' := by
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
  have hv : s.1[h]! = decV3 (PT h) := I.get h hl
  unfold vBody
  simp only [hsz, ↓reduceIte]
  rw [hv, ha]
  have hv1 : vstep PA LA h 1 c (r32 AL h) ≠ 0 :=
    fun e => h1 (by rw [e]; exact VOR.vstep_zero _ _ _ _ _)
  have L := VOR.look_step hinj hcN I haN
  rcases (VOR.vstep_spec hv1).2 with ⟨hlt1, e⟩ | ⟨heq, hpa, hla, e⟩
  · rw [L.1 hlt1]
    rw [e] at h1 ⊢
    exact vB_step hinj hcN I hpar hlab (hal.push rfl) hbe hb hbN h1
  · obtain ⟨hn, I'⟩ := L.2 heq
    rw [hn]
    rw [e] at h1 ⊢
    refine vB_step hinj (by omega) I' (hpar.push (by rw [hpa])) (hlab.push (by rw [hla]; rfl))
      (hal.push ?_) hbe hb hbN h1
    rw [I.size, heq]

theorem vbeq_eq {a b : V} (h : a.beq b = true) : a = b := by
  obtain ⟨ap, am⟩ := a
  obtain ⟨bp, bm⟩ := b
  simp only [V.beq, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, h.2]

theorem vbeq_self (a : V) : a.beq a = true := by
  simp [V.beq]

theorem decV3_inj {c c' : Nat} (h : vkey (decV3 c) = vkey (decV3 c')) : c = c' := by
  simp only [vkey, decV3, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : c &&& (2 ^ 32 - 1) = c % 2 ^ 32 := Nat.and_two_pow_sub_one_eq_mod c 32
  have e2 : c' &&& (2 ^ 32 - 1) = c' % 2 ^ 32 := Nat.and_two_pow_sub_one_eq_mod c' 32
  rw [e1, e2] at h1
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h2
  rw [← Nat.div_add_mod c (2 ^ 32), ← Nat.div_add_mod c' (2 ^ 32), h1, h2]

theorem v3_sound {d N cap : Nat} {AT BT : Array V} {v0 : V} {PT AL BE PA LA SO : Nat → Nat}
    (_hAT : AT.size = d ∧ BT.size = d)
    (hh : v3HdK d N cap v0 PT AL BE PA LA = true)
    (hp : ∀ i < N, v3PtK d N AT BT PT AL BE i = true)
    (hs : ∀ s < N, vorbSortK N PT SO s = true) :
    vecBFS d AT BT v0 cap = v3Rec N PT AL BE PA LA ∧
      ∀ chunks, vecOrbitOK d AT BT (v3Rec N PT AL BE PA LA) chunks = true := by
  unfold v3HdK at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
  obtain ⟨⟨⟨⟨⟨⟨⟨hN, hNcap⟩, hN32⟩, -⟩, hroot⟩, hpa0⟩, hla0⟩, hcnt⟩ := hh
  have hroot' := vbeq_eq hroot
  have hP : ∀ i < N, (decV3 (PT i)).canon d = true ∧ r32 AL i < N ∧ r32 BE i < N ∧
      comb d AT (decV3 (PT i)) = decV3 (PT (r32 AL i)) ∧
      comb d BT (decV3 (PT i)) = decV3 (PT (r32 BE i)) := by
    intro i hi
    have h := hp i hi
    unfold v3PtK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨h1, h2, h3, by rw [F3R.comb_eq]; exact vbeq_eq h4, by rw [F3R.comb_eq]; exact vbeq_eq h5⟩
  have hinj : ∀ i < N, ∀ j < N, vkey (decV3 (PT i)) = vkey (decV3 (PT j)) → i = j :=
    fun i hi j hj e => VO.codes_inj_of_sort hs i hi j hj (decV3_inj e)
  have hfin : VInv (fun i => decV3 (PT i)) PA LA AL BE N N (Id.run (forIn (List.range' 0 cap)
      ((#[v0], (∅ : Std.HashMap (Nat × Nat) Nat).insert (vkey v0) 0, #[], #[], #[0], #[0]) : VSt)
      (vBody d AT BT))) := by
    refine TBfs.forIn_range'_done cap 0 _ _
      (fun j s => j ≤ N ∧ VInv (fun i => decV3 (PT i)) PA LA AL BE (vorbCnt j AL BE PA LA) j s)
      (VInv (fun i => decV3 (PT i)) PA LA AL BE N N) (fun j hj s hP' => ?_) (fun s hP' => ?_)
      ⟨Nat.zero_le _, ?_⟩
    · rw [Nat.zero_add]
      obtain ⟨hjN, J⟩ := hP'
      rcases Nat.lt_or_ge j N with hjN' | hjN'
      · left
        obtain ⟨s', e, J'⟩ := vBody_step (AT := AT) (BT := BT) hinj
          (fun i hi => (hP i hi).2) hcnt hN hjN' J
        exact ⟨s', e, by omega, J'⟩
      · right
        have hj : j = N := by omega
        rw [hj, hcnt] at J
        refine ⟨s, ?_, J⟩
        unfold vBody
        have hn : ¬ j < s.1.size := by rw [J.idx.size]; omega
        simp only [hn, ↓reduceIte]
    · obtain ⟨hcN, J⟩ := hP'
      have : cap = N := by omega
      subst this
      rw [hcnt] at J
      exact J
    · rw [VOR.cnt_zero]
      refine ⟨?_, VOR.arrEq_one (by rw [hpa0]; rfl), VOR.arrEq_one (by rw [hla0]; rfl),
        VOR.arrEq_nil _, VOR.arrEq_nil _⟩
      rw [← hroot']
      exact VOR.hinv_init (fun i => decV3 (PT i)) vkey
  have hrec : vecBFS d AT BT v0 cap = v3Rec N PT AL BE PA LA := by
    rw [vecBFS_eq]
    obtain ⟨I, hpar, hlab, hal, hbe⟩ := hfin
    unfold v3Rec
    simp only
    rw [VOR.ArrEq.eq_ofFn ⟨I.size, I.get⟩, hal.eq_ofFn, hbe.eq_ofFn, hpar.eq_ofFn, hlab.eq_ofFn]
  refine ⟨hrec, fun chunks => ?_⟩
  have hsz : (v3Rec N PT AL BE PA LA).pts.size = N := by simp [v3Rec]
  have hpt : ∀ i < N, (v3Rec N PT AL BE PA LA).pts[i]! = decV3 (PT i) :=
    fun i hi => TBfs.ofFn_get (f := fun i => decV3 (PT i)) hi
  have hap : ∀ i < N, ap (v3Rec N PT AL BE PA LA).alpha i = r32 AL i :=
    fun i hi => TBfs.ap_ofFn hi
  have hbp : ∀ i < N, ap (v3Rec N PT AL BE PA LA).beta i = r32 BE i :=
    fun i hi => TBfs.ap_ofFn hi
  have hpp : ∀ i < N, ap (v3Rec N PT AL BE PA LA).par i = r32 PA i :=
    fun i hi => TBfs.ap_ofFn hi
  have hlp : ∀ i < N, ap (v3Rec N PT AL BE PA LA).lab i = r32 LA i :=
    fun i hi => TBfs.ap_ofFn hi
  have hidx : ∀ i < N, (vindexOf (v3Rec N PT AL BE PA LA).pts).getD
      (vkey (v3Rec N PT AL BE PA LA).pts[i]!) (v3Rec N PT AL BE PA LA).pts.size = i := by
    intro i hi
    unfold vindexOf
    rw [Std.HashMap.getD_eq_getD_getElem?, VOR.vindex_get (fun a ha b hb e => ?_) i
      (by rw [hsz]; exact hi)]
    · rfl
    · rw [hsz] at ha hb
      rw [hpt a ha, hpt b hb] at e
      exact hinj a ha b hb e
  have htree := VOR.tree_facts hN hcnt
  unfold vecOrbitOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, hsz]
  refine ⟨⟨hN, by omega⟩, PC.parAll_of fun i hi => ?_⟩
  obtain ⟨hcan, haN, hbN, ha, hb⟩ := hP i hi
  have hix := hidx i hi
  rw [hsz] at hix
  unfold vecCheckAt
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, hsz]
  rw [hpt i hi] at hix ⊢
  rw [hap i hi, hbp i hi, hpt _ haN, hpt _ hbN, ha, hb, hix]
  refine ⟨⟨⟨⟨⟨⟨hcan, rfl⟩, haN⟩, vbeq_self _⟩, hbN⟩, vbeq_self _⟩, ?_⟩
  by_cases h0 : i = 0
  · exact Or.inl h0
  · right
    obtain ⟨hlt, ht⟩ := htree i (by omega) hi
    rw [hpp i hi, hlp i hi, hap _ (by omega), hbp _ (by omega)]
    exact ⟨hlt, ht⟩

end CFSG.KS.VO3

end
