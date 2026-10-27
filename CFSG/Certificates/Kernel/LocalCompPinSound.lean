
module

public import Certificates.Data.Kernel.LocalComp.ConjPin
public import CFSG.Sporadic.SmallOddCore.ClassSimple
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinBaseSound
import all CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.LocalCompPinSnd.Conj
public import CFSG.Certificates.Kernel.Spor.RawDefs

namespace CFSG.KC.LocalComp.Pin

open CFSG.PSL3Four.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.KS.BfsReplay CFSG.KS.PEnum
open CFSG.KLie.CT (fget)

def PInv (n w ng : Nat) (gens : Array Tab) (T : Nat → Nat) (c : Nat) (s : St) : Prop :=
  s.1.size = c ∧ s.2.1.size = c ∧ s.2.2.1.size = c ∧
    (∀ i < c, s.1[i]! = unpack n w (T i)) ∧
    (∀ x, s.2.2.2.contains x = true ↔ ∃ i < c, unpack n w (T i) = x) ∧
    (∀ i < c, i ≠ 0 → s.2.1[i]! < i ∧ s.2.2.1[i]! < ng ∧
      s.1[i]! = leftStep n gens s.2.2.1[i]! s.1[s.2.1[i]!]!)

section Search

variable {n w ng N : Nat} {G T E : Nat → Nat} {gens : Array Tab}

structure PinF (n w ng N : Nat) (G T : Nat → Nat) (gens : Array Tab) : Prop where
  size : gens.size = ng
  bind : ∀ k < ng, gens[k]! = unpack n w (G k)
  canG : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true
  canT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true
  inj : ∀ a < N, ∀ b < N, T a = T b → a = b

theorem PinF.step (P : PinF n w ng N G T gens) {j h : Nat} (hj : j < ng) (hh : h < N) :
    leftStep n gens j (unpack n w (T h)) = unpack n w (pcomp n w (mask w) (G j) (T h)) := by
  unfold leftStep
  rw [P.bind j hj]
  exact comp_unpack (P.canG j hj) (P.canT h hh)

theorem PinF.uinj (P : PinF n w ng N G T gens) {a b : Nat} (ha : a < N) (hb : b < N)
    (e : unpack n w (T a) = unpack n w (T b)) : a = b :=
  P.inj a ha b hb (unpack_inj (P.canT a ha) (P.canT b hb) e)

theorem pin_inner (P : PinF n w ng N G T gens) {h j c : Nat} (hh : h < c) (hj : j < ng)
    {s : St} (hI : PInv n w ng gens T c s)
    (h0 : genStep n w (mask w) T (T h) (E h) (G j) j c ≠ 0)
    (hN : genStep n w (mask w) T (T h) (E h) (G j) j c ≤ N) :
    ∃ s', innerBody (leftStep n gens) (unpack n w (T h)) h j s = pure (ForInStep.yield s') ∧
      PInv n w ng gens T (genStep n w (mask w) T (T h) (E h) (G j) j c) s' := by
  obtain ⟨h1, h2, h3, hget, hK, htr⟩ := hI
  have hcN : c ≤ N := le_trans (genStep_spec rfl h0).2.1 hN
  have hy := P.step hj (by omega : h < N)
  have e := genStep_eq n w (mask w) T (T h) (E h) (G j) j c
  generalize fget (E h) j 16 = q at e
  generalize hY : pcomp n w (mask w) (G j) (T h) = y at e hy
  have hc0 : c ≠ 0 := by omega
  rw [ite_eq_right hc0] at e
  by_cases hlt : q < c
  · rw [ite_eq_left hlt] at e
    by_cases hT : T q = y
    · rw [ite_eq_left hT] at e
      rw [e]
      have hc : s.2.2.2.contains (unpack n w y) = true := (hK _).2 ⟨q, hlt, by rw [hT]⟩
      exact ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp [innerBody, hy, hc],
        h1, h2, h3, hget, hK, htr⟩
    · rw [ite_eq_right hT] at e
      exact absurd e h0
  · rw [ite_eq_right hlt] at e
    by_cases heq : q = c
    · by_cases hT : T c = y
      · rw [ite_eq_left heq, ite_eq_left hT] at e
        rw [e] at hN ⊢
        have hnc : s.2.2.2.contains (unpack n w y) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          obtain ⟨i, hi, ei⟩ := (hK _).1 hc
          rw [← hT] at ei
          have := P.uinj (by omega) (by omega) ei
          omega
        refine ⟨(s.1.push (unpack n w y), s.2.1.push h, s.2.2.1.push j,
          s.2.2.2.insert (unpack n w y) s.1.size), by simp [innerBody, hy, hnc],
          by simp [h1], by simp [h2], by simp [h3], fun i hi => ?_, fun x => ?_,
          fun i hi hi0 => ?_⟩
        · rcases Nat.lt_or_ge i c with a | a
          · change (s.1.push _)[i]! = _
            rw [push_lt (by omega)]
            exact hget i a
          · have ei : i = s.1.size := by omega
            subst ei
            change (s.1.push _)[s.1.size]! = _
            rw [push_eq, h1, hT]
        · change (s.2.2.2.insert _ _).contains x = true ↔ _
          rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hK]
          constructor
          · rintro (ex | ⟨i, hi, ex⟩)
            · exact ⟨c, by omega, by rw [hT, ex]⟩
            · exact ⟨i, by omega, ex⟩
          · rintro ⟨i, hi, ex⟩
            rcases Nat.lt_or_ge i c with a | a
            · exact Or.inr ⟨i, a, ex⟩
            · have ei : i = c := by omega
              subst ei
              rw [← ex, hT]
              exact Or.inl rfl
        · change (s.2.1.push h)[i]! < i ∧ (s.2.2.1.push j)[i]! < ng ∧
            (s.1.push _)[i]! =
              leftStep n gens (s.2.2.1.push j)[i]! (s.1.push _)[(s.2.1.push h)[i]!]!
          rcases Nat.lt_or_ge i c with a | a
          · obtain ⟨t1, t2, t3⟩ := htr i a hi0
            rw [push_lt (by omega : i < s.2.1.size), push_lt (by omega : i < s.2.2.1.size),
              push_lt (by omega : i < s.1.size), push_lt (by omega : s.2.1[i]! < s.1.size)]
            exact ⟨t1, t2, t3⟩
          · have ei : i = c := by omega
            subst ei
            have e2 : (s.2.1.push h)[i]! = h := by rw [← h2]; exact push_eq
            have e3 : (s.2.2.1.push j)[i]! = j := by rw [← h3]; exact push_eq
            have e1 : (s.1.push (unpack n w y))[i]! = unpack n w y := by rw [← h1]; exact push_eq
            rw [e1, e2, e3, push_lt (by omega : h < s.1.size), hget h hh, hy]
            exact ⟨hh, hj, rfl⟩
      · rw [ite_eq_left heq, ite_eq_right hT] at e
        exact absurd e h0
    · rw [ite_eq_right heq] at e
      exact absurd e h0

theorem pointF_le {m : Nat} {h len lo c r : Nat} (hl : lo + len ≤ ng)
    (hr : pointF n w m G T E h len lo c = r) (h0 : r ≠ 0) : c ≤ r :=
  (pointF_spec (ng := ng) (fun _ => True) h (fun _ _ => trivial) len lo c r hl hr h0
    fun _ _ => trivial).1

theorem runF_le {m : Nat} : ∀ {len lo c r : Nat}, runF n w m ng G T E len lo c = r → r ≠ 0 →
    c ≤ r
  | 0, _, _, _, hr, _ => Nat.le_of_eq hr
  | len + 1, lo, c, r, hr, h0 => by
    rw [runF_succ] at hr
    cases hb : Nat.blt lo c
    · rw [hb] at hr
      change runF n w m ng G T E len (Nat.succ lo) 0 = r at hr
      rw [runF_zero] at hr
      exact absurd hr.symm h0
    · rw [hb] at hr
      change runF n w m ng G T E len (Nat.succ lo) (pointStep n w m ng G T E lo c) = r at hr
      have hp0 : pointStep n w m ng G T E lo c ≠ 0 := by
        intro e
        rw [e, runF_zero] at hr
        exact h0 hr.symm
      exact le_trans (pointF_le (ng := ng) (by omega) (pointStep_eq lo c).symm hp0) (runF_le hr h0)

theorem pointF_add {m : Nat} (h : Nat) : ∀ (a b lo c : Nat),
    pointF n w m G T E h (a + b) lo c =
      pointF n w m G T E h b (lo + a) (pointF n w m G T E h a lo c)
  | 0, b, lo, c => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | a + 1, b, lo, c => by
    have e : Nat.succ lo + a = lo + (a + 1) := by omega
    rw [Nat.add_right_comm]
    change pointF n w m G T E h (a + b) (Nat.succ lo) (genStep n w m T (T h) (E h) (G lo) lo c) =
      pointF n w m G T E h b (lo + (a + 1))
        (pointF n w m G T E h a (Nat.succ lo) (genStep n w m T (T h) (E h) (G lo) lo c))
    rw [pointF_add h a b (Nat.succ lo), e]

theorem pin_point (P : PinF n w ng N G T gens) {h c : Nat} (hh : h < c) {s : St}
    (hI : PInv n w ng gens T c s) (h0 : pointStep n w (mask w) ng G T E h c ≠ 0)
    (hN : pointStep n w (mask w) ng G T E h c ≤ N) :
    PInv n w ng gens T (pointStep n w (mask w) ng G T E h c)
      (Id.run (forIn (List.range' 0 ng) (s.1, s.2.1, s.2.2.1, s.2.2.2)
        (innerBody (leftStep n gens) (unpack n w (T h)) h))) := by
  rw [pointStep_eq] at h0 hN ⊢
  have hfin : ∀ j ≤ ng, pointF n w (mask w) G T E h j 0 c ≠ 0 ∧
      pointF n w (mask w) G T E h j 0 c ≤ N := by
    intro j hj
    have e := pointF_add (n := n) (w := w) (m := mask w) (G := G) (T := T) (E := E) h j (ng - j) 0 c
    rw [Nat.add_sub_cancel' hj, Nat.zero_add] at e
    have hj0 : pointF n w (mask w) G T E h j 0 c ≠ 0 := by
      intro z
      rw [z, pointF_zero] at e
      exact h0 e
    exact ⟨hj0, le_trans (pointF_le (ng := ng) (by omega) e.symm h0) hN⟩
  have := forIn_range'_yield ng 0 (s.1, s.2.1, s.2.2.1, s.2.2.2)
    (innerBody (leftStep n gens) (unpack n w (T h)) h)
    (fun j s' => PInv n w ng gens T (pointF n w (mask w) G T E h j 0 c) s')
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      have e : pointF n w (mask w) G T E h (j + 1) 0 c =
          genStep n w (mask w) T (T h) (E h) (G j) j (pointF n w (mask w) G T E h j 0 c) := by
        rw [pointF_add h j 1 0 c, Nat.zero_add]
        rfl
      have hc := (hfin (j + 1) (by omega))
      rw [e] at hc ⊢
      have hle := pointF_le (ng := ng) (n := n) (w := w) (m := mask w) (G := G) (T := T) (E := E)
        (h := h) (len := j) (lo := 0) (c := c) (by omega) rfl (hfin j (by omega)).1
      exact pin_inner P (by omega) hj hP hc.1 hc.2)
    hI
  exact this

theorem pin_outer (P : PinF n w ng N G T gens) {cap : Nat} (hcap : N ≤ cap) (hN0 : N ≠ 0)
    (hrun : runF n w (mask w) ng G T E N 0 1 = N) (hT0 : idTab n = unpack n w (T 0)) :
    PInv n w ng gens T N
      (Id.run (forIn (List.range' 0 cap) (initSt (idTab n) cap)
        (outerBody (leftStep n gens) ng))) := by
  refine forIn_range'_done cap 0 (initSt (idTab n) cap) (outerBody (leftStep n gens) ng)
    (fun h s => h ≤ N ∧ ∃ c, h ≤ c ∧ PInv n w ng gens T c s ∧
      runF n w (mask w) ng G T E (N - h) h c = N)
    (PInv n w ng gens T N) (fun h hh s hP => ?_) (fun s hP => ?_)
    ⟨Nat.zero_le _, 1, Nat.zero_le _, ?_, by rw [Nat.sub_zero]; exact hrun⟩
  · obtain ⟨hhN, c, hhc, hI, hr⟩ := hP
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge h N with a | a
    · have e : N - h = (N - (h + 1)) + 1 := by omega
      rw [e, runF_succ] at hr
      cases hb : Nat.blt h c
      · rw [hb] at hr
        change runF n w (mask w) ng G T E _ (Nat.succ h) 0 = N at hr
        rw [runF_zero] at hr
        exact absurd hr.symm hN0
      · rw [hb] at hr
        change runF n w (mask w) ng G T E _ (Nat.succ h) (pointStep n w (mask w) ng G T E h c) = N
          at hr
        have hlt : h < c := Nat.blt_eq.mp hb
        have hp0 : pointStep n w (mask w) ng G T E h c ≠ 0 := by
          intro z
          rw [z, runF_zero] at hr
          exact hN0 hr.symm
        have hpN := runF_le hr hN0
        have hpc := pointF_le (ng := ng) (by omega) (pointStep_eq h c).symm hp0
        have hhs : h < s.1.size := by rw [hI.1]; exact hlt
        have hsh : s.1[h]! = unpack n w (T h) := hI.2.2.2.1 h hlt
        refine Or.inl ⟨Id.run (forIn (List.range' 0 ng) (s.1, s.2.1, s.2.2.1, s.2.2.2)
          (innerBody (leftStep n gens) (unpack n w (T h)) h)), ?_, by omega, _, by omega,
          pin_point P hlt hI hp0 hpN, hr⟩
        rw [outerBody, ite_eq_left hhs, hsh]
    · have e : h = N := by omega
      subst e
      rw [Nat.sub_self] at hr
      change c = h at hr
      subst hr
      have hns : ¬ c < s.1.size := by rw [hI.1]; exact Nat.lt_irrefl _
      exact Or.inr ⟨_, by simp [outerBody, hns], hI⟩
  · obtain ⟨hcN, c, hc, hI, hr⟩ := hP
    have e : cap = N := by omega
    subst e
    rw [Nat.sub_self] at hr
    change c = cap at hr
    subst hr
    exact hI
  · refine ⟨rfl, rfl, rfl, fun i hi => ?_, fun x => ?_, fun i hi hi0 => absurd hi (by omega)⟩
    · have e : i = 0 := by omega
      subst e
      simp [initSt, hT0]
    · simp only [initSt]
      rw [Std.HashMap.contains_insert, Std.HashMap.contains_emptyWithCapacity, Bool.or_false,
        beq_iff_eq, hT0]
      constructor
      · intro e
        exact ⟨0, by omega, e⟩
      · rintro ⟨i, hi, e⟩
        have : i = 0 := by omega
        subst this
        exact e

end Search

end CFSG.KC.LocalComp.Pin

public section

namespace CFSG.KC.LocalComp.Pin

open CFSG.PSL3Four.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.LocalComp.ConjPin

theorem enumBFS_of_bfsK {n w ng N cap : Nat} {G T E S : Nat → Nat} {gens : Array Tab}
    (hs : gens.size = ng) (hg : ∀ k < ng, gens[k]! = unpack n w (G k))
    (hk : bfsK n w ng G N T E S = true) (hf : N ≤ cap) :
    enumOK n gens (enumBFS n gens cap) = true ∧
      (enumBFS n gens cap).tabs = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
  have hk' := hk
  unfold bfsK at hk'
  simp only [CFSG.KS.bAnd_iff] at hk'
  obtain ⟨hsz, hGc, -, hT0, hdist, hrun⟩ := hk'
  have P : PinF n w ng N G T gens :=
    ⟨hs, hg, fun k hk => CFSG.KS.allN_spec hGc k hk, bfsK_canon hk, distinctK_inj hdist⟩
  obtain ⟨hNpos, -, -, hcl⟩ := bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) hk
  have hR : runF n w (mask w) ng G T E N 0 1 = N := by
    rw [← runK_eq]
    exact Nat.eq_of_beq_eq_true hrun
  have hid : idTab n = unpack n w (T 0) := by
    rw [Nat.eq_of_beq_eq_true hT0]
    exact CFSG.KS.PEnum.idTab_unpack hsz
  have hO := pin_outer P hf (by omega) hR hid
  unfold enumBFS
  rw [CFSG.KS.BfsReplay.bfs_eq, hs]
  generalize Id.run (forIn (List.range' 0 cap) (CFSG.KS.BfsReplay.initSt (idTab n) cap)
    (CFSG.KS.BfsReplay.outerBody (leftStep n gens) ng)) = s at hO
  obtain ⟨h1, h2, h3, hget, -, htr⟩ := hO
  have htabs : s.1 = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
    apply Array.ext
    · simp [h1]
    · intro i hi1 hi2
      rw [Array.getElem_ofFn, ← getElem!_pos s.1 i hi1, hget i (by omega)]
  refine ⟨?_, htabs⟩
  unfold enumOK treeOK
  simp only
  rw [hs]
  have hinj : ∀ a < s.1.size, ∀ b < s.1.size, s.1[a]! = s.1[b]! → a = b := fun a ha b hb e => by
    rw [hget a (by omega), hget b (by omega)] at e
    exact P.uinj (by omega) (by omega) e
  obtain ⟨hi1, -⟩ := CFSG.KS.BfsReplay.indexOf_spec hinj
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨by omega, by rw [hget 0 (by omega), hid]⟩,
    CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_⟩
  rw [h1] at hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨?_, CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => ?_⟩, ?_⟩
  · unfold posOf
    exact hi1 i (by omega)
  · obtain ⟨q, hq, hx⟩ := hcl i hi j hj
    have e : leftStep n gens j s.1[i]! = s.1[q]! := by
      rw [hget i hi, hget q hq, hx, P.step hj hi]
    unfold found posOf
    rw [e, hi1 q (by omega)]
    simp [h1, hq]
  · by_cases h0 : i = 0
    · exact Or.inl h0
    · right
      obtain ⟨a1, a2, a3⟩ := htr i hi h0
      exact ⟨⟨a1, a2⟩, a3⟩

theorem orbitBFS_of_bfsCK {n w ng N cap X : Nat} {G GI T E S : Nat → Nat} {gens ginv : Array Tab}
    {x : Tab} (hs : gens.size = ng) (hsi : ginv.size = ng)
    (hg : ∀ k < ng, gens[k]! = unpack n w (G k)) (hgi : ∀ k < ng, ginv[k]! = unpack n w (GI k))
    (hx : x = unpack n w X) (hk : bfsCK n w ng G GI X N T E S = true) (hf : N ≤ cap) :
    treeOK (conjStep n gens ginv) gens.size x (orbitBFS n gens ginv x cap) = true ∧
      (orbitBFS n gens ginv x cap).tabs = Array.ofFn (n := N) fun i => unpack n w (T i.val) :=
  CFSG.KC.LocalComp.PinSnd.orbit_of_bfsCK hs hsi hg hgi hx hk hf

theorem notin_notB_eq_false {b : Bool} (h : CFSG.KLie.CT.notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem notin_getElem_ofFn {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {k : Nat}
    (hk : k < m) : (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem notInOK_of_K {n w N X : Nat} {T : Nat → Nat} {x : Tab} (hx : x = unpack n w X)
    (h : notInK n w N T X = true) :
    notInOK (Array.ofFn (n := N) fun i => unpack n w (T i.val)) x = true := by
  have h' := h
  unfold notInK at h'
  simp only [CFSG.KS.bAnd_iff] at h'
  obtain ⟨hX, hall⟩ := h'
  have hpt := CFSG.KS.allN_spec hall
  subst hx
  unfold CFSG.PSL3Four.Native.notInOK CFSG.PSL3Four.Native.allBelow
  rw [Array.size_ofFn, List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have e : (Array.ofFn (n := N) fun i => unpack n w (T i.val))[k]! = unpack n w (T k) :=
    notin_getElem_ofFn (fun i : Fin N => unpack n w (T i.val)) hk
  obtain ⟨hTk, hnB⟩ := (CFSG.KS.bAnd_iff _ _).1 (hpt k hk)
  have hbf : Nat.beq (T k) X = false := notin_notB_eq_false hnB
  have hne : unpack n w (T k) ≠ unpack n w X := fun heq =>
    Nat.ne_of_beq_eq_false hbf (CFSG.KS.PEnum.unpack_inj hTk hX heq)
  simp only [e, beq_false_of_ne hne, Bool.not_false]

theorem cover_getElem!_ofFn {α : Type*} [Inhabited α] {m : Nat} (f : Fin m → α) {i : Nat}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  simp [hi]

theorem cover_size_of_K {n w L : Nat} {NL : Nat → Nat} {OT : Nat → Nat → Nat}
    {O : Array Enum}
    (hO : ∀ l < L, O[l]!.tabs = Array.ofFn (n := NL l) fun p => unpack n w (OT l p.val))
    {l : Nat} (hl : l < L) : O[l]!.tabs.size = NL l := by
  rw [hO l hl, Array.size_ofFn]

theorem cover_found_of_K {n w L : Nat} {T NL : Nat → Nat} {OT : Nat → Nat → Nat}
    {O : Array Enum}
    (hO : ∀ l < L, O[l]!.tabs = Array.ofFn (n := NL l) fun p => unpack n w (OT l p.val))
    {l p k : Nat} (hl : l < L) (hp : p < NL l) (e : OT l p = T k) :
    CFSG.PSL3Four.Native.found (CFSG.PSL3Four.Native.indexOf O[l]!.tabs) O[l]!.tabs
      (unpack n w (T k)) = true := by
  rw [CFSG.KS.PEnum.found_indexOf_iff]
  refine ⟨p, by rw [cover_size_of_K hO hl]; exact hp, ?_⟩
  rw [hO l hl, cover_getElem!_ofFn _ hp]
  exact congrArg (unpack n w) e

theorem coverAllOK_of_K {n w N L : Nat} {T : Nat → Nat} {NL : Nat → Nat} {OT : Nat → Nat → Nat}
    {C : Nat → Nat} {O : Array Enum} (hL : O.size = L)
    (hO : ∀ l < L, O[l]!.tabs = Array.ofFn (n := NL l) fun p => unpack n w (OT l p.val))
    (h : allN N (fun i => bAnd(Nat.blt (Nat.land (C i) (nat_lit 65535)) L,
      bAnd(Nat.blt (Nat.shiftRight (C i) (nat_lit 16)) (NL (Nat.land (C i) (nat_lit 65535))),
        Nat.beq (OT (Nat.land (C i) (nat_lit 65535)) (Nat.shiftRight (C i) (nat_lit 16))) (T i))))
      = true) :
    CFSG.Sporadic.SmallOddCore.coverAllOK (Array.ofFn (n := N) fun i => unpack n w (T i.val)) O =
      true := by
  simp only [CFSG.Sporadic.SmallOddCore.coverAllOK,
    CFSG.ComponentClassification.PSL3Four.allBelow_eq_true,
    CFSG.ComponentClassification.PSL3Four.anyBelow_eq_true, Array.size_ofFn]
  intro k hk
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 (CFSG.KS.allN_spec h k hk)
  obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  simp only [Nat.blt_eq] at h1 h2
  have hlO : Nat.land (C k) (nat_lit 65535) < O.size := by rw [hL]; exact h1
  refine ⟨Nat.land (C k) (nat_lit 65535), hlO, ?_⟩
  rw [CFSG.Sporadic.SmallOddCore.getElem!_map_eq (fun e => CFSG.PSL3Four.Native.indexOf e.tabs) O hlO,
    cover_getElem!_ofFn _ hk]
  exact cover_found_of_K hO h1 h2 (Nat.eq_of_beq_eq_true h3)

end CFSG.KC.LocalComp.Pin

end
