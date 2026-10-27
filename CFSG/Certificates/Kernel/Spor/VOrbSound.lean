module

public import Mathlib.Data.Nat.Prime.Defs
public import CFSG.Certificates.Kernel.Spor.VOrbReplay
import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.GaussInvSound
import CFSG.Certificates.Kernel.Spor.PChainSound

public section

namespace CFSG.KS.VO

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.Sporadic.J1.Native CFSG.Sporadic.Th.Native
  CFSG.Perm.Native

@[expose] noncomputable def vorbRec (d N : Nat) (PT AL BE PA LA : Nat → Nat) : Orb :=
  ⟨Array.ofFn (n := N) fun i => decV d (PT i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 AL i.val),
    Array.ofFn (n := N) fun i => UInt32.ofNat (r32 BE i.val),
    Array.ofFn (n := N) fun i => r32 PA i.val,
    Array.ofFn (n := N) fun i => r32 LA i.val⟩

theorem allIn_iff0 {n : Nat} {p : Nat → Bool} : allIn 0 n p = true ↔ ∀ i < n, p i = true := by
  unfold allIn
  rw [Nat.sub_zero, Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    simpa using h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h ⟨i, hi⟩ _
    simpa using h i hi

theorem allIn_of {lo hi : Nat} {p : Nat → Bool} (h : ∀ i, lo ≤ i → i < hi → p i = true) :
    allIn lo hi p = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨k, hk⟩ _
  exact h _ (by omega) (by omega)

theorem strictB_eqV (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem decV_getD {d c k : Nat} (hk : k < d) : (decV d c).getD k 0 = (c >>> (4 * k)) &&& 15 := by
  unfold decV
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]
  rfl

theorem decV_inj {d c c' : Nat} (hc : c < 2 ^ (4 * d)) (hc' : c' < 2 ^ (4 * d))
    (h : decV d c = decV d c') : c = c' := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 4 * d
  · have hk : b / 4 < d := by omega
    have e := congrArg (fun l => l.getD (b / 4) 0) h
    simp only [decV_getD hk] at e
    have e2 := congrArg (fun x => Nat.testBit x (b % 4)) e
    simp only [Nat.testBit_and, Nat.testBit_shiftRight] at e2
    have h15 : Nat.testBit 15 (b % 4) = true := by
      have hr : b % 4 < 4 := Nat.mod_lt _ (by omega)
      generalize b % 4 = r at hr
      obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      all_goals rfl
    have hb4 : 4 * (b / 4) + b % 4 = b := Nat.div_add_mod b 4
    rw [h15, Bool.and_true, Bool.and_true, hb4] at e2
    exact e2
  · have hle : 2 ^ (4 * d) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem sort_facts {N : Nat} {PT SO : Nat → Nat} (hs : ∀ s < N, vorbSortK N PT SO s = true) :
    (∀ t < N, ∀ s < t, PT (r32 SO s) < PT (r32 SO t)) ∧ ∀ i < N, ∃ s < N, r32 SO s = i := by
  have hS : ∀ s < N, r32 SO s < N ∧ (s + 1 < N → PT (r32 SO s) < PT (r32 SO (s + 1))) := by
    intro s hs'
    have h := hs s hs'
    unfold vorbSortK at h
    rw [strictB_eqV] at h
    have hx : Nat.blt (r32 SO s) N = true := by
      cases hx : Nat.blt (r32 SO s) N
      · rw [hx] at h
        exact absurd h Bool.false_ne_true
      · rfl
    refine ⟨Nat.blt_eq.mp hx, fun h1 => ?_⟩
    rw [hx] at h
    have h1' : Nat.blt (Nat.succ s) N = true := Nat.blt_eq.mpr h1
    rw [h1'] at h
    exact Nat.blt_eq.mp h
  have hmono : ∀ t < N, ∀ s < t, PT (r32 SO s) < PT (r32 SO t) := by
    intro t
    induction t with
    | zero => intro _ s hs0; omega
    | succ t ih =>
      intro ht s hst
      have hstep := (hS t (by omega)).2 ht
      rcases Nat.lt_or_ge s t with a | a
      · exact Nat.lt_trans (ih (by omega) s a) hstep
      · have e : s = t := by omega
        rw [e]
        exact hstep
  have hσinj : ∀ s < N, ∀ t < N, r32 SO s = r32 SO t → s = t := by
    intro s hs' t ht e
    rcases Nat.lt_trichotomy s t with a | a | a
    · have := hmono t ht s a
      rw [e] at this
      omega
    · exact a
    · have := hmono s hs' t a
      rw [e] at this
      omega
  have hsurj : ∀ i < N, ∃ s < N, r32 SO s = i := by
    let F : Fin N → Fin N := fun s => ⟨r32 SO s, (hS s s.2).1⟩
    have hinj : Function.Injective F := fun a b e =>
      Fin.ext (hσinj a a.2 b b.2 (congrArg Fin.val e))
    intro i hi
    obtain ⟨s, hs'⟩ := Finite.surjective_of_injective hinj ⟨i, hi⟩
    exact ⟨s, s.2, congrArg Fin.val hs'⟩
  exact ⟨hmono, hsurj⟩

theorem codes_inj_of_sort {N : Nat} {PT SO : Nat → Nat} (hs : ∀ s < N, vorbSortK N PT SO s = true) :
    ∀ i < N, ∀ j < N, PT i = PT j → i = j := by
  obtain ⟨hmono, hsurj⟩ := sort_facts hs
  intro i hi j hj e
  obtain ⟨s, hs', rfl⟩ := hsurj i hi
  obtain ⟨t, ht, rfl⟩ := hsurj j hj
  rcases Nat.lt_trichotomy s t with a | a | a
  · have := hmono t ht s a
    omega
  · rw [a]
  · have := hmono s hs' t a
    omega

abbrev OSt := Std.HashMap (List Nat) Nat × Array (List Nat) × Array Nat × Array Nat × Table × Table

@[expose] def oB (p : Nat) (key : List Nat → List Nat) (B : List (List Nat)) (v : List Nat)
    (h : Nat) (idx : Std.HashMap (List Nat) Nat) (pts : Array (List Nat)) (par lab : Array Nat)
    (al be : Table) : Id (ForInStep OSt) :=
  match idx.get? (key (mvL p B v)) with
  | some j => pure (ForInStep.yield (idx, pts, par, lab, al, be.push (UInt32.ofNat j)))
  | none => pure (ForInStep.yield (idx.insert (key (mvL p B v)) pts.size,
      pts.push (key (mvL p B v)), par.push h, lab.push 2, al, be.push (UInt32.ofNat pts.size)))

@[expose] def oBody (p : Nat) (key : List Nat → List Nat) (A B : List (List Nat)) (h : Nat)
    (s : OSt) : Id (ForInStep OSt) :=
  if h < s.2.1.size then
    match s.1.get? (key (mvL p A s.2.1[h]!)) with
    | some j => oB p key B s.2.1[h]! h s.1 s.2.1 s.2.2.1 s.2.2.2.1
        (s.2.2.2.2.1.push (UInt32.ofNat j)) s.2.2.2.2.2
    | none => oB p key B s.2.1[h]! h (s.1.insert (key (mvL p A s.2.1[h]!)) s.2.1.size)
        (s.2.1.push (key (mvL p A s.2.1[h]!))) (s.2.2.1.push h) (s.2.2.2.1.push 1)
        (s.2.2.2.2.1.push (UInt32.ofNat s.2.1.size)) s.2.2.2.2.2
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2))

theorem orbBFS_eq (p : Nat) (key : List Nat → List Nat) (A B : List (List Nat)) (root : List Nat)
    (cap : Nat) : orbBFS p key A B root cap =
      let s := Id.run (forIn (List.range' 0 cap)
        (((∅ : Std.HashMap (List Nat) Nat).insert root 0, #[root], #[0], #[0], #[], #[]) : OSt)
        (oBody p key A B))
      ⟨s.2.1, s.2.2.2.2.1, s.2.2.2.2.2, s.2.2.1, s.2.2.2.1⟩ := by
  unfold orbBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

structure OInv (T : Nat → List Nat) (PA LA AL BE : Nat → Nat) (c h : Nat) (s : OSt) : Prop where
  idx : VOR.HInv T (fun x => x) c s.1 s.2.1
  par : VOR.ArrEq s.2.2.1 c (r32 PA)
  lab : VOR.ArrEq s.2.2.2.1 c (r32 LA)
  al : VOR.ArrEq s.2.2.2.2.1 h fun i => UInt32.ofNat (r32 AL i)
  be : VOR.ArrEq s.2.2.2.2.2 h fun i => UInt32.ofNat (r32 BE i)

theorem oB_step {p : Nat} {key : List Nat → List Nat} {B : List (List Nat)} {T : Nat → List Nat}
    {PA LA AL BE : Nat → Nat} {N c h : Nat} {v : List Nat} {idx : Std.HashMap (List Nat) Nat}
    {pts : Array (List Nat)} {par lab : Array Nat} {al be : Table}
    (hinj : ∀ i < N, ∀ j < N, T i = T j → i = j) (hcN : c ≤ N)
    (I : VOR.HInv T (fun x => x) c idx pts) (hpar : VOR.ArrEq par c (r32 PA))
    (hlab : VOR.ArrEq lab c (r32 LA)) (hal : VOR.ArrEq al (h + 1) fun i => UInt32.ofNat (r32 AL i))
    (hbe : VOR.ArrEq be h fun i => UInt32.ofNat (r32 BE i))
    (hb : key (mvL p B v) = T (r32 BE h)) (hbN : r32 BE h < N)
    (hv : vstep PA LA h 2 c (r32 BE h) ≠ 0) :
    ∃ s', oB p key B v h idx pts par lab al be = pure (ForInStep.yield s') ∧
      OInv T PA LA AL BE (vstep PA LA h 2 c (r32 BE h)) (h + 1) s' := by
  have L := VOR.look_step (k := fun x => x) hinj hcN I hbN
  beta_reduce at L
  unfold oB
  rw [Std.HashMap.get?_eq_getElem?, hb]
  rcases (VOR.vstep_spec hv).2 with ⟨hlt, e⟩ | ⟨heq, hpa, hla, e⟩
  · rw [L.1 hlt, e]
    exact ⟨_, rfl, ⟨I, hpar, hlab, hal, hbe.push rfl⟩⟩
  · obtain ⟨hn, I'⟩ := L.2 heq
    rw [hn, e]
    refine ⟨_, rfl, ⟨I', hpar.push hpa.symm, hlab.push hla.symm, hal, hbe.push ?_⟩⟩
    rw [I.size, heq]

theorem oBody_step {p d N : Nat} {key : List Nat → List Nat} {A B : List (List Nat)}
    {PT AL BE PA LA : Nat → Nat} (hinj : ∀ i < N, ∀ j < N, decV d (PT i) = decV d (PT j) → i = j)
    (hpt : ∀ i < N, r32 AL i < N ∧ r32 BE i < N ∧
      key (mvL p A (decV d (PT i))) = decV d (PT (r32 AL i)) ∧
      key (mvL p B (decV d (PT i))) = decV d (PT (r32 BE i)))
    (hcnt : vorbCnt N AL BE PA LA = N) (hN : 0 < N) {h : Nat} (hh : h < N) {s : OSt}
    (J : OInv (fun i => decV d (PT i)) PA LA AL BE (vorbCnt h AL BE PA LA) h s) :
    ∃ s', oBody p key A B h s = pure (ForInStep.yield s') ∧
      OInv (fun i => decV d (PT i)) PA LA AL BE (vorbCnt (h + 1) AL BE PA LA) (h + 1) s' := by
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
  have hsz : h < s.2.1.size := by rw [I.size]; exact hl
  have hv : s.2.1[h]! = decV d (PT h) := I.get h hl
  unfold oBody
  simp only [hsz, ↓reduceIte]
  rw [hv, Std.HashMap.get?_eq_getElem?, ha]
  have hv1 : vstep PA LA h 1 c (r32 AL h) ≠ 0 :=
    fun e => h1 (by rw [e]; exact VOR.vstep_zero _ _ _ _ _)
  have L := VOR.look_step (k := fun x => x) hinj hcN I haN
  beta_reduce at L
  rcases (VOR.vstep_spec hv1).2 with ⟨hlt1, e⟩ | ⟨heq, hpa, hla, e⟩
  · rw [L.1 hlt1]
    rw [e] at h1 ⊢
    exact oB_step hinj hcN I hpar hlab (hal.push rfl) hbe hb hbN h1
  · obtain ⟨hn, I'⟩ := L.2 heq
    rw [hn]
    rw [e] at h1 ⊢
    refine oB_step hinj (by omega) I' (hpar.push hpa.symm) (hlab.push hla.symm)
      (hal.push ?_) hbe hb hbN h1
    rw [I.size, heq]

theorem vorbHd_facts {p d N cap : Nat} {A B : List (List Nat)} {root : List Nat}
    {PT AL BE PA LA : Nat → Nat} (hh : vorbHdK p d N cap A B root PT AL BE PA LA = true) :
    p ≤ 16 ∧ d ≤ 16 ∧ 0 < N ∧ N ≤ cap ∧ N < 4294967296 ∧ A.length = d ∧ B.length = d ∧
      root = decV d (PT 0) ∧ r32 PA 0 = 0 ∧ r32 LA 0 = 0 ∧ vorbCnt N AL BE PA LA = N := by
  unfold vorbHdK at hh
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq,
    PC.listEqK_iff] at hh
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, -, -, a8, a9, a10, a11⟩ := hh
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩

theorem vorbPt_facts {p d N : Nat} {key : List Nat → List Nat} {A B : List (List Nat)}
    {PT AL BE : Nat → Nat} {i : Nat} (h : vorbPtK p d N key A B PT AL BE i = true) :
    PT i < 2 ^ (4 * d) ∧ (∀ x ∈ decV d (PT i), x < p) ∧ r32 AL i < N ∧ r32 BE i < N ∧
      key (mvL p A (decV d (PT i))) = decV d (PT (r32 AL i)) ∧
      key (mvL p B (decV d (PT i))) = decV d (PT (r32 BE i)) := by
  unfold vorbPtK at h
  simp only [strictB_eqV, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, PC.listEqK_iff,
    List.all_eq_true] at h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  refine ⟨?_, fun x hx => a2 x hx, a3, a4, a5, a6⟩
  change PT i < 1 <<< (4 * d) at a1
  rwa [Nat.one_shiftLeft] at a1

theorem vorb_sound {p d N cap : Nat} {key : List Nat → List Nat} {A B : List (List Nat)}
    {root : List Nat} {PT AL BE PA LA SO : Nat → Nat}
    (hh : vorbHdK p d N cap A B root PT AL BE PA LA = true)
    (hp : ∀ i < N, vorbPtK p d N key A B PT AL BE i = true)
    (hs : ∀ s < N, vorbSortK N PT SO s = true) :
    orbBFS p key A B root cap = vorbRec d N PT AL BE PA LA ∧
      ∀ rel : List Nat → List Nat → Bool, (∀ w : List Nat, (∀ x ∈ w, x < p) → rel w (key w) = true) →
        orbOK p d rel A B root (vorbRec d N PT AL BE PA LA) = true := by
  obtain ⟨-, -, hN, hNcap, hN32, hAl, hBl, hroot, hpa0, hla0, hcnt⟩ := vorbHd_facts hh
  have hP := fun i hi => vorbPt_facts (hp i hi)
  have hinj : ∀ i < N, ∀ j < N, decV d (PT i) = decV d (PT j) → i = j := fun i hi j hj e =>
    codes_inj_of_sort hs i hi j hj (decV_inj (hP i hi).1 (hP j hj).1 e)
  obtain ⟨hcn, -⟩ := VOR.cnt_facts hN hcnt
  have hfin : OInv (fun i => decV d (PT i)) PA LA AL BE N N (Id.run (forIn (List.range' 0 cap)
      (((∅ : Std.HashMap (List Nat) Nat).insert root 0, #[root], #[0], #[0], #[], #[]) : OSt)
      (oBody p key A B))) := by
    refine TBfs.forIn_range'_done cap 0 _ _
      (fun j s => j ≤ N ∧ OInv (fun i => decV d (PT i)) PA LA AL BE (vorbCnt j AL BE PA LA) j s)
      (OInv (fun i => decV d (PT i)) PA LA AL BE N N) (fun j hj s hP' => ?_) (fun s hP' => ?_)
      ⟨Nat.zero_le _, ?_⟩
    · rw [Nat.zero_add]
      obtain ⟨hjN, J⟩ := hP'
      rcases Nat.lt_or_ge j N with hjN' | hjN'
      · left
        obtain ⟨s', e, J'⟩ := oBody_step (key := key) (A := A) (B := B) hinj
          (fun i hi => (hP i hi).2.2) hcnt hN hjN' J
        exact ⟨s', e, by omega, J'⟩
      · right
        have hj : j = N := by omega
        rw [hj, hcnt] at J
        refine ⟨s, ?_, J⟩
        unfold oBody
        have hn : ¬ j < s.2.1.size := by rw [J.idx.size]; omega
        simp only [hn, ↓reduceIte]
    · obtain ⟨hcN, J⟩ := hP'
      have : cap = N := by omega
      subst this
      rw [hcnt] at J
      exact J
    · rw [VOR.cnt_zero]
      refine ⟨?_, VOR.arrEq_one hpa0.symm, VOR.arrEq_one hla0.symm, VOR.arrEq_nil _,
        VOR.arrEq_nil _⟩
      rw [hroot]
      exact VOR.hinv_init (fun i => decV d (PT i)) (fun x => x)
  have hrec : orbBFS p key A B root cap = vorbRec d N PT AL BE PA LA := by
    rw [orbBFS_eq]
    obtain ⟨I, hpar, hlab, hal, hbe⟩ := hfin
    unfold vorbRec
    simp only
    rw [VOR.ArrEq.eq_ofFn ⟨I.size, I.get⟩, hal.eq_ofFn, hbe.eq_ofFn, hpar.eq_ofFn, hlab.eq_ofFn]
  refine ⟨hrec, fun rel hrel => ?_⟩
  have hpt : ∀ i < N, (vorbRec d N PT AL BE PA LA).pts[i]! = decV d (PT i) :=
    fun i hi => TBfs.ofFn_get (f := fun i => decV d (PT i)) hi
  have hsz : (vorbRec d N PT AL BE PA LA).pts.size = N := by simp [vorbRec]
  have hap : ∀ i < N, ap (vorbRec d N PT AL BE PA LA).alpha i = r32 AL i := fun i hi => TBfs.ap_ofFn hi
  have hbp : ∀ i < N, ap (vorbRec d N PT AL BE PA LA).beta i = r32 BE i := fun i hi => TBfs.ap_ofFn hi
  have hpp : ∀ i < N, (vorbRec d N PT AL BE PA LA).par[i]! = r32 PA i :=
    fun i hi => TBfs.ofFn_get (f := r32 PA) hi
  have hlp : ∀ i < N, (vorbRec d N PT AL BE PA LA).lab[i]! = r32 LA i :=
    fun i hi => TBfs.ofFn_get (f := r32 LA) hi
  have hlen : ∀ c, (decV d c).length = d := fun c => by simp [decV]
  have hred : ∀ (X : List (List Nat)) (v : List Nat), X.length = d → (∀ x ∈ v, x < p) →
      ∀ x ∈ mvL p X v, x < p := by
    intro X v hX hv x hx
    unfold mvL at hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exfalso
      subst h0
      have hd : d = 0 := by
        rcases Nat.eq_zero_or_pos d with h | h
        · exact h
        · exact absurd ((hP 0 hN).2.1 _ (List.getElem_mem (l := decV d (PT 0))
            (n := 0) (by rw [hlen]; exact h))) (Nat.not_lt_zero _)
      rw [hd] at hX
      rw [List.length_eq_zero_iff.1 hX] at hx
      simp at hx
    · exact Nat.mod_lt _ h0
  have htree := VOR.tree_facts hN hcnt
  unfold orbOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz]
  refine ⟨⟨⟨⟨⟨hN, by omega⟩, by rw [hpt 0 hN, hroot]⟩, by simp [vorbRec]⟩, by simp [vorbRec]⟩,
    allIn_iff0.2 fun i hi => ?_⟩
  obtain ⟨-, hv, haN, hbN, ha, hb⟩ := hP i hi
  unfold orbCheckAt wfV
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, hsz, hpt i hi,
    hap i hi, hbp i hi, hpt _ haN, hpt _ hbN, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hlen _, hv⟩, haN⟩, hbN⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← ha]
    exact hrel _ (hred A _ hAl hv)
  · rw [← hb]
    exact hrel _ (hred B _ hBl hv)
  · by_cases h0 : i = 0
    · exact Or.inl h0
    · right
      obtain ⟨hlt, ht⟩ := htree i (by omega) hi
      rw [hpp i hi, hlp i hi, hap _ (by omega), hbp _ (by omega)]
      exact ⟨hlt, ht⟩

theorem vecSep_of_sort {d N : Nat} {PT SO : Nat → Nat}
    (hc : ∀ i < N, PT i < 2 ^ (4 * d)) (hs : ∀ s < N, vorbSortK N PT SO s = true) :
    vecSep (Array.ofFn (n := N) fun i => decV d (PT i.val)) = true := by
  have hinj := codes_inj_of_sort hs
  unfold vecSep
  rw [Array.size_ofFn, allIn_iff0]
  intro i hi
  refine allIn_of fun j hij hj => ?_
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ j (by simpa using hj),
    Array.getElem_ofFn, Array.getElem_ofFn, bne_iff_ne]
  intro e
  have := hinj i hi j hj (decV_inj (hc i hi) (hc j hj) e)
  omega

theorem firstNZ_spec : ∀ v : List Nat, (∀ k, v.getD k 0 = 0) ∨
    ∃ i < v.length, (∀ k < i, v.getD k 0 = 0) ∧ v.getD i 0 ≠ 0 ∧ firstNZ v = v.getD i 0
  | [] => Or.inl fun k => by simp
  | a :: r => by
    by_cases ha : a = 0
    · rcases firstNZ_spec r with h | ⟨i, hi, h1, h2, h3⟩
      · left
        intro k
        cases k with
        | zero => simpa using ha
        | succ k => simpa using h k
      · right
        refine ⟨i + 1, by simp; omega, fun k hk => ?_, by simpa using h2, ?_⟩
        · cases k with
          | zero => simpa using ha
          | succ k => simpa using h1 k (by omega)
        · simp [firstNZ, ha, h3]
    · right
      exact ⟨0, by simp, fun k hk => absurd hk (Nat.not_lt_zero _), by simpa using ha,
        by simp [firstNZ, ha]⟩

theorem projV_eq_of_minors {p d : Nat} (hp : p.Prime) {u w : List Nat} (hu : u.length = d)
    (hw : w.length = d) (hup : ∀ x ∈ u, x < p) (hwp : ∀ x ∈ w, x < p)
    (hu0 : ∃ k, u.getD k 0 ≠ 0) (hw0 : ∃ k, w.getD k 0 ≠ 0)
    (hm : ∀ a < d, ∀ b < d, u.getD a 0 * w.getD b 0 % p = u.getD b 0 * w.getD a 0 % p) :
    projV p u = projV p w := by
  have hF : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have castInj : ∀ x y, x < p → y < p → (x : ZMod p) = y → x = y := fun x y hx hy h => by
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  have hm' : ∀ a < d, ∀ b < d,
      (u.getD a 0 : ZMod p) * w.getD b 0 = u.getD b 0 * w.getD a 0 := fun a ha b hb => by
    have := hm a ha b hb
    rw [← ZMod.natCast_eq_natCast_iff'] at this
    push_cast at this
    exact this
  have getD_lt : ∀ v : List Nat, (∀ x ∈ v, x < p) → ∀ k, v.getD k 0 < p := fun v hv k => by
    rcases Nat.lt_or_ge k v.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact hv _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
      exact hp.pos
  have nz : ∀ x, x < p → x ≠ 0 → (x : ZMod p) ≠ 0 := fun x hx h0 e =>
    h0 (castInj x 0 hx hp.pos (by simpa using e))
  rcases firstNZ_spec u with hu' | ⟨i, hi, hu1, hu2, hu3⟩
  · obtain ⟨k, hk⟩ := hu0
    exact absurd (hu' k) hk
  rcases firstNZ_spec w with hw' | ⟨j, hj, hw1, hw2, hw3⟩
  · obtain ⟨k, hk⟩ := hw0
    exact absurd (hw' k) hk
  have hfu := nz _ (getD_lt u hup i) hu2
  have hfw := nz _ (getD_lt w hwp j) hw2
  have hij : i = j := by
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := hm' i (by omega) j (by omega)
      rw [hw1 i h, Nat.cast_zero, mul_zero] at this
      exact absurd ((mul_eq_zero.1 this).resolve_left hfu) hfw
    · exact h
    · have := hm' j (by omega) i (by omega)
      rw [hu1 j h, Nat.cast_zero, zero_mul] at this
      exact absurd ((mul_eq_zero.1 this.symm).resolve_left hfu) hfw
  subst hij
  have pu : projV p u = u.map fun x => x * (u.getD i 0 ^ (p - 2) % p) % p := by
    unfold projV
    rw [hu3]
    rfl
  have pw : projV p w = w.map fun x => x * (w.getD i 0 ^ (p - 2) % p) % p := by
    unfold projV
    rw [hw3]
    rfl
  rw [pu, pw]
  apply List.ext_getElem (by simp [hu, hw])
  intro k hk1 hk2
  have hk : k < d := by
    simp only [List.length_map] at hk1
    omega
  simp only [List.getElem_map]
  apply castInj _ _ (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos)
  rw [← List.getD_eq_getElem u 0, ← List.getD_eq_getElem w 0]
  simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_pow]
  have e := hm' k hk i (by omega)
  have hpow : ∀ f : ZMod p, f ≠ 0 → f ^ (p - 2) * f = 1 := fun f hf => by
    rw [← pow_succ, show p - 2 + 1 = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one hf
  apply mul_right_cancel₀ (mul_ne_zero hfu hfw)
  calc (u.getD k 0 : ZMod p) * (u.getD i 0 : ZMod p) ^ (p - 2) * (u.getD i 0 * w.getD i 0)
      = u.getD k 0 * w.getD i 0 * ((u.getD i 0 : ZMod p) ^ (p - 2) * u.getD i 0) := by ring
    _ = u.getD i 0 * w.getD k 0 := by rw [hpow _ hfu, mul_one, e]
    _ = w.getD k 0 * u.getD i 0 * ((w.getD i 0 : ZMod p) ^ (p - 2) * w.getD i 0) := by
        rw [hpow _ hfw, mul_one, mul_comm]
    _ = w.getD k 0 * (w.getD i 0 : ZMod p) ^ (p - 2) * (u.getD i 0 * w.getD i 0) := by ring

theorem pmSep_of_proj {p d N : Nat} {PT SP : Nat → Nat} (hp : p.Prime)
    (hc : ∀ i < N, PT i < 2 ^ (4 * d))
    (hv : ∀ i < N, List.all (decV d (PT i)) (fun x => Nat.blt x p) = true)
    (hs : ∀ s < N, projSortK p d N PT SP s = true) (chunks : Nat) :
    pmSep p d (Array.ofFn (n := N) fun i => decV d (PT i.val)) chunks = true := by
  have hs' : ∀ s < N, vorbSortK N (fun x => codeV (projV p (decV d (PT x)))) SP s = true ∧
      PT (r32 SP s) ≠ 0 := by
    intro s hs0
    have h := hs s hs0
    unfold projSortK at h
    unfold vorbSortK
    rw [strictB_eqV] at h ⊢
    cases hx : Nat.blt (r32 SP s) N
    · rw [hx] at h
      exact absurd h Bool.false_ne_true
    · rw [hx] at h
      cases hz : Nat.beq (PT (r32 SP s)) 0
      · rw [hz] at h
        exact ⟨h, fun e => by rw [e] at hz; exact absurd hz (by decide)⟩
      · rw [hz] at h
        exact absurd h Bool.false_ne_true
  have hinj := codes_inj_of_sort fun s hs0 => (hs' s hs0).1
  have hnz : ∀ i < N, PT i ≠ 0 := by
    intro i hi
    obtain ⟨s, hs0, rfl⟩ := (sort_facts fun s hs0 => (hs' s hs0).1).2 i hi
    exact (hs' s hs0).2
  have hpt : ∀ i < N, (Array.ofFn (n := N) fun i => decV d (PT i.val))[i]! = decV d (PT i) :=
    fun i hi => by rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have hlen : ∀ c, (decV d c).length = d := fun c => by simp [decV]
  have hred : ∀ i < N, ∀ x ∈ decV d (PT i), x < p := fun i hi x hx =>
    Nat.blt_eq.mp (List.all_eq_true.1 (hv i hi) x hx)
  have hne0 : ∀ i < N, ∃ k, (decV d (PT i)).getD k 0 ≠ 0 := by
    intro i hi
    refine Classical.byContradiction fun h => hnz i hi ?_
    simp only [not_exists, not_not] at h
    have e : decV d (PT i) = decV d 0 := by
      apply List.ext_getElem (by rw [hlen, hlen])
      intro k hk1 hk2
      rw [← List.getD_eq_getElem _ 0 hk1, ← List.getD_eq_getElem _ 0 hk2, h k,
        decV_getD (by rw [hlen] at hk2; exact hk2)]
      simp
    exact decV_inj (hc i hi) (Nat.two_pow_pos _) e
  unfold pmSep
  rw [Array.size_ofFn]
  refine CFSG.KS.PC.parAll_of fun i hi => allIn_of fun j hij hj => ?_
  rw [hpt i hi, hpt j hj]
  refine Classical.byContradiction fun hmn => ?_
  have hm : ∀ a < d, ∀ b < d, (decV d (PT i)).getD a 0 * (decV d (PT j)).getD b 0 % p =
      (decV d (PT i)).getD b 0 * (decV d (PT j)).getD a 0 % p := by
    intro a ha b hb
    refine Classical.byContradiction fun hne => hmn ?_
    unfold minorNZ
    rw [List.any_eq_true]
    refine ⟨a, List.mem_range.2 ha, List.any_eq_true.2 ⟨b, List.mem_range.2 hb, ?_⟩⟩
    rw [bne_iff_ne]
    exact hne
  have e := projV_eq_of_minors hp (hlen _) (hlen _) (hred i hi) (hred j hj) (hne0 i hi)
    (hne0 j hj) hm
  have := hinj i hi j hj (congrArg codeV e)
  omega

example : projSortK 2 1 2 (fun i => if i = 0 then 16 else 1) (fun _ => 1 <<< 32) 0 = true ∧
    projSortK 2 1 2 (fun i => if i = 0 then 16 else 1) (fun _ => 1 <<< 32) 1 = true ∧
    minorNZ 2 1 (decV 1 16) (decV 1 1) = false := by
  decide +kernel

example : vorbPtK 2 1 2 id [[1]] [[1]] (fun i => if i = 0 then 16 else 1) (fun _ => 0)
    (fun _ => 0) 0 = false := by
  decide +kernel

theorem invT_get {n : Nat} {t : Table} {f g : Nat → Nat} (hn : n < 2 ^ 32)
    (ht : ∀ x < n, ap t x = f x ∧ f x < n ∧ g (f x) = x) :
    invOK n t (invT n t) = true ∧ ∀ y < n, ap (invT n t) y = g y := by
  have hsurj : ∀ y < n, ∃ x < n, f x = y := by
    let F : Fin n → Fin n := fun x => ⟨f x, (ht x x.2).2.1⟩
    have hinj : Function.Injective F := by
      intro a b e
      have e' : f a = f b := congrArg Fin.val e
      apply Fin.ext
      rw [← (ht a a.2).2.2, ← (ht b b.2).2.2, e']
    intro y hy
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
    exact ⟨x, x.2, congrArg Fin.val hx⟩
  have hget : ∀ i < n, (t[i]!).toNat = f i := fun i hi => (ht i hi).1
  have hD : ∀ i < n, (t[i]!).toNat < n := fun i hi => by
    rw [hget i hi]
    exact (ht i hi).2.1
  have hd : ∀ i < n, ∀ j < i, (t[j]!).toNat ≠ (t[i]!).toNat := fun i hi j hj e => by
    rw [hget i hi, hget j (by omega)] at e
    have := congrArg g e
    rw [(ht j (by omega)).2.2, (ht i hi).2.2] at this
    omega
  have heq : invT n t = (List.range' 0 n).foldl
      (fun p i => p.set! (t[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0) := by
    unfold invT
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  have hl := CFSG.KS.TW.set_loopV (D := fun i => (t[i]!).toNat) (v := fun i => UInt32.ofNat i)
    (v0 := (0 : UInt32)) hD hd
  have hap : ∀ x < n, ap (invT n t) (f x) = x := by
    intro x hx
    unfold ap
    rw [heq, ← hget x hx, hl.2 x hx, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, fun y hy => ?_⟩
  · unfold invOK
    rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    rw [(ht i hi).1, hap i hi]
    exact beq_self_eq_true i
  · obtain ⟨x, hx, rfl⟩ := hsurj y hy
    rw [hap x hx, (ht x hx).2.2]

theorem wordT_ap {n : Nat} (hn : n < 2 ^ 32) {gens : Int → Table} {G : Int → Nat → Nat}
    (hg : ∀ z, ∀ x < n, ap (gens z) x = G z x ∧ G z x < n) :
    ∀ w : List Int, (wordT n gens w).size = n ∧
      ∀ x < n, ap (wordT n gens w) x = List.foldr G x w ∧ List.foldr G x w < n
  | [] => by
    refine ⟨by simp [wordT, idT], fun x hx => ⟨?_, hx⟩⟩
    unfold ap wordT idT
    rw [List.foldr_nil, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn,
      UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  | l :: w => by
    obtain ⟨hs, hv⟩ := wordT_ap hn hg w
    have e : wordT n gens (l :: w) = (wordT n gens w).map fun t => (gens l)[t.toNat]! := by
      unfold wordT
      rfl
    rw [e]
    refine ⟨by simp [hs], fun x hx => ?_⟩
    obtain ⟨a1, a2⟩ := hv x hx
    obtain ⟨b1, b2⟩ := hg l _ a2
    refine ⟨?_, by simpa using b2⟩
    unfold ap at a1 b1 ⊢
    rw [getElem!_pos _ x (by simp [hs]; omega), Array.getElem_map,
      ← getElem!_pos (wordT n gens w) x (by omega), a1, b1]
    rfl

theorem buildLetters_get {n : Nat} {gens : Int → Table} {words : Array (List Int)}
    {G : Int → Nat → Nat} {H : Nat → Nat → Nat} (hn : n < 2 ^ 32)
    (hg : ∀ z, ∀ x < n, ap (gens z) x = G z x ∧ G z x < n)
    (hH : ∀ j < words.size, ∀ x < n, H j (List.foldr G x words[j]!) = x) :
    (buildLetters n gens words).size = 2 * words.size ∧
      ∀ j < words.size, ∀ x < n, ap (buildLetters n gens words)[2 * j]! x = List.foldr G x words[j]! ∧
        ap (buildLetters n gens words)[2 * j + 1]! x = H j x := by
  refine ⟨by simp [buildLetters], fun j hj x hx => ?_⟩
  have hw := wordT_ap hn hg words[j]!
  have d0 : 2 * j / 2 = j := by omega
  have m0 : 2 * j % 2 = 0 := by omega
  have d1 : (2 * j + 1) / 2 = j := by omega
  have m1 : (2 * j + 1) % 2 = 1 := by omega
  have e0 : (buildLetters n gens words)[2 * j]! = wordT n gens words[j]! := by
    unfold buildLetters
    rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
    simp only [d0, m0, ite_true]
  have e1 : (buildLetters n gens words)[2 * j + 1]! = invT n (wordT n gens words[j]!) := by
    unfold buildLetters
    rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
    simp only [d1, m1, Nat.one_ne_zero, ite_false]
  rw [e0, e1]
  refine ⟨(hw.2 x hx).1, ?_⟩
  exact (invT_get hn fun y hy => ⟨(hw.2 y hy).1, (hw.2 y hy).2, hH j hj y hy⟩).2 x hx

theorem gaussInv_eq {p d : Nat} {X Y : List (List Nat)} (hp : p.Prime)
    (hX : wfM d X = true ∧ X.all (fun r => r.all fun x => decide (x < p)) = true)
    (hY : wfM d Y = true ∧ Y.all (fun r => r.all fun x => decide (x < p)) = true)
    (h : mulL p d Y X = idL d) : gaussInv p d X = Y :=
  GI.gaussInv_spec hp hX hY h

end CFSG.KS.VO

end
