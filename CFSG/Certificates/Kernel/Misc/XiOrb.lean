module

public import CFSG.Certificates.Kernel.Misc.XiBits
public import CFSG.Certificates.Kernel.J4Q.BfsOrder
public import CFSG.Certificates.Kernel.Spor.TabWords

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Xi

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46 CFSG.KC.Misc.Lines
  CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KS.TW
  CFSG.KC.J4Q.BfsOrder

abbrev OSt := Array Flags × Array Nat × Array Nat × Std.HashMap (Array UInt64) Nat

@[expose] def oInner (gs gi : Array Table) (M : List Nat) (h : Nat) (l : Nat) (st : OSt) :
    Id (ForInStep OSt) :=
  if (!st.2.2.2.contains (packImg gs[l]! M)) = true then
    pure (ForInStep.yield (st.1.push (imgFlags gi[l]! st.1[h]!), st.2.1.push h, st.2.2.1.push l,
      st.2.2.2.insert (packImg gs[l]! M) st.1.size))
  else pure (ForInStep.yield st)

@[expose] def oBody (gs gi : Array Table) (h : Nat) (st : OSt) : Id (ForInStep OSt) :=
  if h < st.1.size then
    pure (ForInStep.yield (Id.run (forIn [:gs.size] st (oInner gs gi (members st.1[h]!) h))))
  else pure (ForInStep.done st)

theorem orbitEnum_eq (R : Flags) (gs gi : Array Table) (cap : Nat) :
    orbitEnum R gs gi cap =
      (let s := Id.run (forIn [:cap] ((#[R], #[0], #[0],
          (∅ : Std.HashMap (Array UInt64) Nat).insert (packList (members R)) 0) : OSt)
          (oBody gs gi))
       (s.1, s.2.1, s.2.2.1)) := by
  unfold orbitEnum
  rfl

theorem packImg_eq (T : Table) (M : List Nat) : packImg T M = packList (M.map (ap T)) := by
  unfold packImg packList
  rw [List.foldl_map]

theorem mem_map_ap {S : Nat} {T : Table} {g : Nat → Nat} (hT : TR 693 T g) {q : Nat} :
    q ∈ (members (fl S)).map (ap T) ↔ ∃ p < 693, S.testBit p = true ∧ g p = q := by
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_members_fl] at hp
    exact ⟨p, hp.1, hp.2, ((hT.2 p hp.1).1).symm⟩
  · rintro ⟨p, hp, h1, rfl⟩
    exact ⟨p, mem_members_fl.2 ⟨hp, h1⟩, (hT.2 p hp).1⟩

theorem key_iff {T : Table} {g : Nat → Nat} (hT : TR 693 T g) {S S' S'' : Nat} (hS : S < 2 ^ 693)
    (hS' : S' < 2 ^ 693) (hS'' : S'' < 2 ^ 693)
    (hset : ∀ q, S''.testBit q = true ↔ ∃ p < 693, S.testBit p = true ∧ g p = q) :
    packImg T (members (fl S)) = packList (members (fl S')) ↔ S' = S'' := by
  rw [packImg_eq, eq_comm]
  have e1 : ∀ p ∈ (members (fl S)).map (ap T), p < 704 := by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
    have := ((hT.2 p' (mem_members_fl.1 hp').1).1).symm
    have h2 := (hT.2 p' (mem_members_fl.1 hp').1).2
    rw [(hT.2 p' (mem_members_fl.1 hp').1).1]
    omega
  have e2 : ∀ p ∈ members (fl S'), p < 704 := fun p hp => by
    have := (mem_members_fl.1 hp).1
    omega
  rw [packList_eq_iff e2 e1]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    have h1 := h q
    rw [mem_members_fl, mem_map_ap hT, ← hset] at h1
    by_cases hq : q < 693
    · cases hb : S'.testBit q <;> cases hb' : S''.testBit q <;> simp_all
    · have a1 : S'.testBit q = false := by
        cases hb : S'.testBit q
        · rfl
        · exact absurd (lt_of_testBit hS' hb) hq
      have a2 : S''.testBit q = false := by
        cases hb : S''.testBit q
        · rfl
        · exact absurd (lt_of_testBit hS'' hb) hq
      rw [a1, a2]
  · intro h q
    subst h
    rw [mem_members_fl, mem_map_ap hT, ← hset]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lt_of_testBit hS' h, h⟩

structure OrbHyp (R : Flags) (gs gi : Array Table) (gm gim : Nat → Nat → Nat)
    (HSo Jo nn : Nat → Nat) : Prop where
  gs_size : gs.size = 2
  gi_size : gi.size = 2
  Ts : ∀ l < 2, TR 693 gs[l]! (gm l)
  Ti : ∀ l < 2, TR 693 gi[l]! (gim l)
  inv : ∀ l < 2, ∀ x < 693, gim l (gm l x) = x ∧ gm l (gim l x) = x
  Rsz : R.size = 693
  R0 : ∀ p < 693, R[p]! = (HSo 0).testBit p
  HS_lt : ∀ j < 1408, HSo j < 2 ^ 693
  dist : ∀ j < 1408, ∀ j' < 1408, HSo j = HSo j' → j = j'
  n0 : nn 0 = 1
  nend : nn 2816 = 1408
  step : ∀ t < 2816, t / 2 < nn t ∧
    ((Jo t < nn t ∧ nn (t + 1) = nn t) ∨ (Jo t = nn t ∧ nn (t + 1) = nn t + 1))
  set : ∀ t < 2816, Jo t < 1408 ∧ ∀ q, (HSo (Jo t)).testBit q = true ↔
    ∃ p < 693, (HSo (t / 2)).testBit p = true ∧ gm (t % 2) p = q

structure OInv (HSo Jo : Nat → Nat) (n : Nat) (st : OSt) : Prop where
  size : st.1.size = n
  sets : ∀ j < n, st.1[j]! = fl (HSo j)
  psize : st.2.1.size = n
  lsize : st.2.2.1.size = n
  p0 : st.2.1[0]! = 0
  l0 : st.2.2.1[0]! = 0
  tree : ∀ j, 1 ≤ j → j < n → st.2.1[j]! < j ∧ st.2.2.1[j]! < 2 ∧
    Jo (2 * st.2.1[j]! + st.2.2.1[j]!) = j ∧ ∀ e < 2 * st.2.1[j]! + st.2.2.1[j]!, Jo e ≠ j
  idx : ∀ q, st.2.2.2.contains q = true ↔ ∃ j < n, packList (members (fl (HSo j))) = q

theorem imgFlags_fl {T : Table} {g gi : Nat → Nat} (hT : TR 693 T gi)
    (hinv : ∀ x < 693, gi (g x) = x ∧ g (gi x) = x) {S S' : Nat}
    (hset : ∀ q, S'.testBit q = true ↔ ∃ p < 693, S.testBit p = true ∧ g p = q) :
    imgFlags T (fl S) = fl S' := by
  have key : (fun q : Fin 693 => (fl S)[ap T q.val]!) =
      (fun p : Fin 693 => S'.testBit p.val) := by
    funext q
    have hq : q.val < 693 := q.isLt
    rw [(hT.2 q hq).1, fl_get S (hT.2 q hq).2]
    rw [Bool.eq_iff_iff, hset]
    constructor
    · intro h
      exact ⟨gi q, (hT.2 q hq).2, h, (hinv q hq).2⟩
    · rintro ⟨p, hp, h1, hpq⟩
      have : gi q = p := by rw [← hpq, (hinv p hp).1]
      rw [this]
      exact h1
  show Array.ofFn (n := 693) (fun q : Fin 693 => (fl S)[ap T q.val]!) = fl S'
  rw [key]
  rfl

namespace OrbHyp

variable {R : Flags} {gs gi : Array Table} {gm gim : Nat → Nat → Nat} {HSo Jo nn : Nat → Nat}

theorem nn_mono (H : OrbHyp R gs gi gm gim HSo Jo nn) :
    ∀ t, t ≤ 2816 → ∀ s ≤ t, nn s ≤ nn t := by
  intro t
  induction t with
  | zero =>
    intro _ s hs
    have : s = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ t ih =>
    intro ht s hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hs) with h | h
    · have h1 := ih (by omega) s (by omega)
      have h2 := (H.step t (by omega)).2
      omega
    · subst h
      exact Nat.le_refl _

theorem nn_le (H : OrbHyp R gs gi gm gim HSo Jo nn) {t : Nat} (ht : t ≤ 2816) :
    nn t ≤ 1408 := by
  have := H.nn_mono 2816 (Nat.le_refl _) t ht
  rw [H.nend] at this
  exact this

theorem nn_pos (H : OrbHyp R gs gi gm gim HSo Jo nn) {t : Nat} (ht : t ≤ 2816) : 1 ≤ nn t := by
  have := H.nn_mono t ht 0 (Nat.zero_le _)
  rw [H.n0] at this
  exact this

theorem Jo_lt (H : OrbHyp R gs gi gm gim HSo Jo nn) {e t : Nat} (het : e < t) (ht : t ≤ 2816) :
    Jo e < nn t := by
  have h1 := H.nn_mono t ht (e + 1) het
  have h2 := (H.step e (by omega)).2
  omega

end OrbHyp

theorem oInner_step {R : Flags} {gs gi : Array Table} {gm gim : Nat → Nat → Nat}
    {HSo Jo nn : Nat → Nat} (H : OrbHyp R gs gi gm gim HSo Jo nn) {h l : Nat} (hl : l < 2)
    (ht : 2 * h + l < 2816) {M : List Nat} (hM : M = members (fl (HSo h))) {st : OSt}
    (hI : OInv HSo Jo (nn (2 * h + l)) st) :
    ∃ st', oInner gs gi M h l st = pure (ForInStep.yield st') ∧
      OInv HSo Jo (nn (2 * h + l + 1)) st' := by
  have ht2 : (2 * h + l) / 2 = h := by omega
  have ht3 : (2 * h + l) % 2 = l := by omega
  obtain ⟨hlt, hcase⟩ := H.step (2 * h + l) ht
  rw [ht2] at hlt
  obtain ⟨hJlt, hJset⟩ := H.set (2 * h + l) ht
  rw [ht2, ht3] at hJset
  have hnn1 : nn (2 * h + l) ≤ 1408 := H.nn_le (by omega)
  have hh1408 : h < 1408 := by omega
  have hkey : ∀ j, j < 1408 →
      (packImg gs[l]! M = packList (members (fl (HSo j))) ↔ HSo j = HSo (Jo (2 * h + l))) := by
    intro j hj
    rw [hM]
    exact key_iff (H.Ts l hl) (H.HS_lt h hh1408) (H.HS_lt j hj) (H.HS_lt _ hJlt) hJset
  have hcont : st.2.2.2.contains (packImg gs[l]! M) = true ↔
      Jo (2 * h + l) < nn (2 * h + l) := by
    rw [hI.idx]
    constructor
    · rintro ⟨j, hj, hjk⟩
      have h1 := (hkey j (by omega)).1 hjk.symm
      have h2 := H.dist j (by omega) _ hJlt h1
      omega
    · intro hlt'
      exact ⟨Jo (2 * h + l), hlt', ((hkey _ hJlt).2 rfl).symm⟩
  rcases hcase with ⟨hknown, hnn⟩ | ⟨hnew, hnn⟩
  · refine ⟨st, ?_, ?_⟩
    · unfold oInner
      rw [if_neg (by simp [hcont.2 hknown])]
    · rw [hnn]
      exact hI
  · have hn0 : st.1.size = nn (2 * h + l) := hI.size
    have hnotc : (!st.2.2.2.contains (packImg gs[l]! M)) = true := by
      have : ¬ st.2.2.2.contains (packImg gs[l]! M) = true := fun hc => by
        have := hcont.1 hc
        omega
      simpa using this
    refine ⟨(st.1.push (imgFlags gi[l]! st.1[h]!), st.2.1.push h, st.2.2.1.push l,
      st.2.2.2.insert (packImg gs[l]! M) st.1.size), ?_, ?_⟩
    · unfold oInner
      rw [if_pos hnotc]
    · rw [hnn]
      have hsh : st.1[h]! = fl (HSo h) := hI.sets h hlt
      have hF : imgFlags gi[l]! st.1[h]! = fl (HSo (nn (2 * h + l))) := by
        rw [hsh, ← hnew]
        exact imgFlags_fl (H.Ti l hl) (H.inv l hl) hJset
      refine ⟨?_, fun j hj => ?_, ?_, ?_, ?_, ?_, fun j hj1 hj2 => ?_, fun q => ?_⟩
      · simp [hn0]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · show (st.1.push _)[j]! = _
          rw [push_getElem!_lt _ _ (by omega)]
          exact hI.sets j hj
        · show (st.1.push _)[j]! = _
          rw [hj, ← hn0, push_getElem!_size, hn0]
          exact hF
      · simp [hI.psize]
      · simp [hI.lsize]
      · show (st.2.1.push h)[0]! = 0
        rw [push_getElem!_lt _ _
          (by rw [hI.psize]; have := H.nn_pos (t := 2 * h + l) (by omega); omega)]
        exact hI.p0
      · show (st.2.2.1.push l)[0]! = 0
        rw [push_getElem!_lt _ _
          (by rw [hI.lsize]; have := H.nn_pos (t := 2 * h + l) (by omega); omega)]
        exact hI.l0
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hj | hj
        · show (st.2.1.push h)[j]! < j ∧ (st.2.2.1.push l)[j]! < 2 ∧
            Jo (2 * (st.2.1.push h)[j]! + (st.2.2.1.push l)[j]!) = j ∧
              ∀ e < 2 * (st.2.1.push h)[j]! + (st.2.2.1.push l)[j]!, Jo e ≠ j
          rw [push_getElem!_lt _ _ (by rw [hI.psize]; exact hj),
            push_getElem!_lt _ _ (by rw [hI.lsize]; exact hj)]
          exact hI.tree j hj1 hj
        · show (st.2.1.push h)[j]! < j ∧ (st.2.2.1.push l)[j]! < 2 ∧
            Jo (2 * (st.2.1.push h)[j]! + (st.2.2.1.push l)[j]!) = j ∧
              ∀ e < 2 * (st.2.1.push h)[j]! + (st.2.2.1.push l)[j]!, Jo e ≠ j
          have e1 : (st.2.1.push h)[j]! = h := by
            rw [hj, ← hI.psize, push_getElem!_size]
          have e2 : (st.2.2.1.push l)[j]! = l := by
            rw [hj, ← hI.lsize, push_getElem!_size]
          rw [e1, e2]
          refine ⟨by omega, hl, by rw [hj]; exact hnew, fun e he => ?_⟩
          have := H.Jo_lt he (by omega : 2 * h + l ≤ 2816)
          omega
      · show (st.2.2.2.insert (packImg gs[l]! M) st.1.size).contains q = true ↔ _
        rw [Std.HashMap.contains_insert, Bool.or_eq_true, hI.idx]
        constructor
        · rintro (hq | ⟨j, hj, hjq⟩)
          · refine ⟨nn (2 * h + l), by omega, ?_⟩
            have := ((hkey (nn (2 * h + l)) (by omega)).2 (by rw [hnew])).symm
            rw [this]
            exact beq_iff_eq.1 hq
          · exact ⟨j, by omega, hjq⟩
        · rintro ⟨j, hj, hjq⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · exact Or.inr ⟨j, hj, hjq⟩
          · left
            subst hj
            have := ((hkey (nn (2 * h + l)) (by omega)).2 (by rw [hnew])).symm
            rw [← hjq, this]
            exact beq_self_eq_true _

@[expose] def oInit (R : Flags) : OSt :=
  (#[R], #[0], #[0], (∅ : Std.HashMap (Array UInt64) Nat).insert (packList (members R)) 0)

theorem oInit_inv {R : Flags} {gs gi : Array Table} {gm gim : Nat → Nat → Nat}
    {HSo Jo nn : Nat → Nat} (H : OrbHyp R gs gi gm gim HSo Jo nn) :
    OInv HSo Jo (nn 0) (oInit R) := by
  have hR : R = fl (HSo 0) := flags_eq H.Rsz H.R0
  rw [H.n0]
  refine ⟨rfl, fun j hj => ?_, rfl, rfl, rfl, rfl, fun j hj1 hj2 => absurd hj2 (by omega),
    fun q => ?_⟩
  · have : j = 0 := by omega
    subst this
    show #[R][0]! = _
    rw [← hR]
    rfl
  · show ((∅ : Std.HashMap (Array UInt64) Nat).insert (packList (members R)) 0).contains q =
      true ↔ _
    rw [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, beq_iff_eq]
    constructor
    · intro h
      exact ⟨0, by omega, by rw [← hR]; exact h⟩
    · rintro ⟨j, hj, hjq⟩
      have : j = 0 := by omega
      subst this
      rw [hR] at *
      exact hjq

theorem orbitEnum_spec {R : Flags} {gs gi : Array Table} {gm gim : Nat → Nat → Nat}
    {HSo Jo nn : Nat → Nat} (H : OrbHyp R gs gi gm gim HSo Jo nn) :
    ∃ par lab : Array Nat, orbitEnum R gs gi 1408 =
      (Array.ofFn (n := 1408) fun j => fl (HSo j), par, lab) ∧ par.size = 1408 ∧
      lab.size = 1408 ∧ par[0]! = 0 ∧ lab[0]! = 0 ∧ ∀ j, 1 ≤ j → j < 1408 →
        par[j]! < j ∧ lab[j]! < 2 ∧ Jo (2 * par[j]! + lab[j]!) = j ∧
          ∀ e < 2 * par[j]! + lab[j]!, Jo e ≠ j := by
  have hfin : OInv HSo Jo 1408 (Id.run (forIn [:1408] (oInit R) (oBody gs gi))) := by
    refine forIn_range_inv (fun h st => OInv HSo Jo (nn (2 * h)) st)
      (fun st => OInv HSo Jo 1408 st) (oBody gs gi) 1408 (oInit R) (fun h st hh hI => ?_)
      (fun st hI => ?_) (oInit_inv H)
    · have hlt : h < st.1.size := by
        rw [hI.size]
        have := (H.step (2 * h) (by omega)).1
        omega
      unfold oBody
      rw [if_pos hlt]
      show OInv HSo Jo (nn (2 * (h + 1)))
        (Id.run (forIn [:gs.size] st (oInner gs gi (members st.1[h]!) h)))
      have hM : members st.1[h]! = members (fl (HSo h)) := by
        rw [hI.sets h (by have := (H.step (2 * h) (by omega)).1; omega)]
      rw [H.gs_size]
      have hres := forIn_range_inv (fun l st' => OInv HSo Jo (nn (2 * h + l)) st')
        (fun st' => OInv HSo Jo (nn (2 * h + 2)) st') (oInner gs gi (members st.1[h]!) h) 2 st
        (fun l st' hl hI' => ?_) (fun st' hI' => hI') (by simpa using hI)
      · have e : 2 * (h + 1) = 2 * h + 2 := by omega
        rw [e]
        exact hres
      · obtain ⟨st'', hst'', hI''⟩ := oInner_step H hl (by omega) hM hI'
        rw [hst'']
        exact hI''
    · have : 2 * 1408 = 2816 := by omega
      rw [this, H.nend] at hI
      exact hI
  obtain ⟨hsz, hsets, hpsz, hlsz, hp0, hl0, htree, -⟩ := hfin
  have hsz' : (Id.run (forIn [:1408] (oInit R) (oBody gs gi))).1 =
      Array.ofFn (n := 1408) fun j => fl (HSo j) := by
    apply Array.ext
    · rw [hsz, Array.size_ofFn]
    · intro i h1 h2
      have hi : i < 1408 := hsz ▸ h1
      have e1 := hsets i hi
      rw [getElem!_pos _ i h1] at e1
      rw [e1, Array.getElem_ofFn]
  refine ⟨(Id.run (forIn [:1408] (oInit R) (oBody gs gi))).2.1,
    (Id.run (forIn [:1408] (oInit R) (oBody gs gi))).2.2.1, ?_, hpsz, hlsz, hp0, hl0, htree⟩
  rw [orbitEnum_eq]
  show ((Id.run (forIn [:1408] (oInit R) (oBody gs gi))).1, _, _) = _
  rw [hsz']
  rfl

@[expose] noncomputable def kst (X Y : Nat) (HS ML : Nat → Nat) (J o : Nat) : Nat → Nat
  | 0 => 2
  | t + 1 => orbK.step X Y HS ML J o (t / 2) (t % 2) (kst X Y HS ML J o t)

theorem orbK_rec_eq (X Y : Nat) (HS ML : Nat → Nat) (J o : Nat) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) 2
      (fun h acc => Nat.rec (motive := fun _ => Nat) acc
        (fun l acc2 => orbK.step X Y HS ML J o h l acc2) 2) n = kst X Y HS ML J o (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show orbK.step X Y HS ML J o n 1 (orbK.step X Y HS ML J o n 0
      (Nat.rec (motive := fun _ => Nat) 2
        (fun h acc => Nat.rec (motive := fun _ => Nat) acc
          (fun l acc2 => orbK.step X Y HS ML J o h l acc2) 2) n)) =
          kst X Y HS ML J o (2 * (n + 1))
    rw [ih]
    have e1 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [e1]
    show _ = orbK.step X Y HS ML J o ((2 * n + 1) / 2) ((2 * n + 1) % 2)
      (orbK.step X Y HS ML J o (2 * n / 2) (2 * n % 2) (kst X Y HS ML J o (2 * n)))
    have e2 : (2 * n + 1) / 2 = n := by omega
    have e3 : (2 * n + 1) % 2 = 1 := by omega
    have e4 : 2 * n / 2 = n := by omega
    have e5 : 2 * n % 2 = 0 := by omega
    rw [e2, e3, e4, e5]

theorem step_eq (X Y : Nat) (HS ML : Nat → Nat) (J o h l cnt : Nat) :
    orbK.step X Y HS ML J o h l cnt =
      if 0 < cnt ∧ h < cnt - 1 ∧ fd 11 J (2 * h + l) < cnt ∧
        HS (1408 * o + fd 11 J (2 * h + l)) =
          imgP (if l = 1 then Y else X) (ML (1408 * o + h)) then
        (if fd 11 J (2 * h + l) + 1 = cnt then cnt + 1 else cnt) else 0 := by
  unfold orbK.step
  simp only [letN_eq, nIf_eq, andB_eq, Nat.blt_eq, Nat.beq_eq, at'_eq, Bool.and_eq_true,
    Nat.mul_eq, Nat.add_eq, Nat.succ_eq_add_one, Nat.pred_eq_sub_one, and_assoc]

theorem img_set_iff {S M T q : Nat} (hl : listsP S M = true) :
    (imgP T M).testBit q = true ↔ ∃ p < 693, S.testBit p = true ∧ fd 10 T p = q := by
  obtain ⟨hS, hspec⟩ := listsP_spec hl
  rw [testBit_imgP]
  constructor
  · rintro ⟨i, hi, hq⟩
    have hp : S.testBit (fd 10 M i) = true := (hspec _).2 ⟨i, hi, rfl⟩
    exact ⟨fd 10 M i, lt_of_testBit hS hp, hp, hq⟩
  · rintro ⟨p, hp, hbit, hq⟩
    obtain ⟨i, hi, rfl⟩ := (hspec p).1 hbit
    exact ⟨i, hi, hq⟩

theorem kst_succ (X Y : Nat) (HS ML : Nat → Nat) (J o t : Nat) :
    kst X Y HS ML J o (t + 1) =
      if 0 < kst X Y HS ML J o t ∧ t / 2 < kst X Y HS ML J o t - 1 ∧
        fd 11 J t < kst X Y HS ML J o t ∧
        HS (1408 * o + fd 11 J t) = imgP (if t % 2 = 1 then Y else X) (ML (1408 * o + t / 2)) then
        (if fd 11 J t + 1 = kst X Y HS ML J o t then kst X Y HS ML J o t + 1
          else kst X Y HS ML J o t) else 0 := by
  show orbK.step X Y HS ML J o (t / 2) (t % 2) (kst X Y HS ML J o t) = _
  rw [step_eq]
  have e : 2 * (t / 2) + t % 2 = t := by omega
  rw [e]

theorem kst_zero_of (X Y : Nat) (HS ML : Nat → Nat) (J o t : Nat)
    (h : kst X Y HS ML J o t = 0) : ∀ n, kst X Y HS ML J o (t + n) = 0 := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [← Nat.add_assoc, kst_succ, ih]
    simp

theorem kst_mono (X Y : Nat) (HS ML : Nat → Nat) (J o t : Nat) :
    kst X Y HS ML J o t ≠ 0 → kst X Y HS ML J o (t + 1) ≠ 0 →
      kst X Y HS ML J o t ≤ kst X Y HS ML J o (t + 1) := by
  intro h h'
  rw [kst_succ] at h' ⊢
  split_ifs at h' ⊢ <;> omega

theorem orbK_spec {UP X Y c J : Nat} {HS ML : Nat → Nat} (o : Nat) (ho : o < 3)
    (hmem : ∀ k < 4224, listsP (HS k) (ML k) = true)
    (h : orbK UP X Y HS ML J o c = true) :
    HS (1408 * o) = rootK UP c ∧ ∃ nn : Nat → Nat, nn 0 = 1 ∧ nn 2816 = 1408 ∧
      (∀ t < 2816, t / 2 < nn t ∧ ((fd 11 J t < nn t ∧ nn (t + 1) = nn t) ∨
        (fd 11 J t = nn t ∧ nn (t + 1) = nn t + 1))) ∧
      (∀ t < 2816, fd 11 J t < 1408 ∧ ∀ q, (HS (1408 * o + fd 11 J t)).testBit q = true ↔
        ∃ p < 693, (HS (1408 * o + t / 2)).testBit p = true ∧
          fd 10 (if t % 2 = 1 then Y else X) p = q) := by
  unfold orbK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [orbK_rec_eq] at h2
  have hk : kst X Y HS ML J o 2816 = 1409 := h2
  refine ⟨h1, fun t => kst X Y HS ML J o t - 1, rfl,
    by show kst X Y HS ML J o 2816 - 1 = 1408; rw [hk], ?_⟩
  have hnz : ∀ t ≤ 2816, kst X Y HS ML J o t ≠ 0 := by
    intro t ht h0
    have := kst_zero_of X Y HS ML J o t h0 (2816 - t)
    rw [show t + (2816 - t) = 2816 by omega, hk] at this
    omega
  have hmon : ∀ s t, t + s ≤ 2816 → kst X Y HS ML J o t ≤ kst X Y HS ML J o (t + s) := by
    intro s
    induction s with
    | zero => intro t _; exact Nat.le_refl _
    | succ s ih =>
      intro t hts
      have h1 := ih t (by omega)
      have h2 := kst_mono X Y HS ML J o (t + s) (hnz _ (by omega)) (hnz _ (by omega))
      rw [← Nat.add_assoc]
      omega
  have hle : ∀ t ≤ 2816, kst X Y HS ML J o t ≤ 1409 := by
    intro t ht
    have := hmon (2816 - t) t (by omega)
    rw [show t + (2816 - t) = 2816 by omega, hk] at this
    exact this
  have hstep : ∀ t < 2816, (0 < kst X Y HS ML J o t ∧ t / 2 < kst X Y HS ML J o t - 1 ∧
        fd 11 J t < kst X Y HS ML J o t ∧
        HS (1408 * o + fd 11 J t) = imgP (if t % 2 = 1 then Y else X) (ML (1408 * o + t / 2))) ∧
      kst X Y HS ML J o (t + 1) = (if fd 11 J t + 1 = kst X Y HS ML J o t then
        kst X Y HS ML J o t + 1 else kst X Y HS ML J o t) := by
    intro t ht
    have hs := kst_succ X Y HS ML J o t
    have hne := hnz (t + 1) (by omega)
    by_cases hc : (0 < kst X Y HS ML J o t ∧ t / 2 < kst X Y HS ML J o t - 1 ∧
        fd 11 J t < kst X Y HS ML J o t ∧
        HS (1408 * o + fd 11 J t) = imgP (if t % 2 = 1 then Y else X) (ML (1408 * o + t / 2)))
    · rw [if_pos hc] at hs
      exact ⟨hc, hs⟩
    · rw [if_neg hc] at hs
      exact absurd hs hne
  have hJ : ∀ t < 2816, fd 11 J t < 1408 := by
    intro t ht
    obtain ⟨⟨h0, h1, h2, h3⟩, h4⟩ := hstep t ht
    have hl1 := hle t (by omega)
    have hl2 := hle (t + 1) (by omega)
    by_cases hc : fd 11 J t + 1 = kst X Y HS ML J o t
    · rw [if_pos hc] at h4
      omega
    · omega
  refine ⟨fun t ht => ?_, fun t ht => ⟨hJ t ht, fun q => ?_⟩⟩
  · obtain ⟨⟨h0, h1, h2, h3⟩, h4⟩ := hstep t ht
    beta_reduce
    refine ⟨by omega, ?_⟩
    by_cases hc : fd 11 J t + 1 = kst X Y HS ML J o t
    · rw [if_pos hc] at h4
      right
      omega
    · rw [if_neg hc] at h4
      left
      omega
  · obtain ⟨⟨h0, h1, h2, h3⟩, h4⟩ := hstep t ht
    have hk1 : 1408 * o + fd 11 J t < 4224 := by have := hJ t ht; omega
    have hk2 : 1408 * o + t / 2 < 4224 := by omega
    have hl1 := hmem _ hk2
    obtain ⟨hS1, -⟩ := listsP_spec (hmem _ hk1)
    rw [h3]
    exact img_set_iff hl1

end CFSG.KC.Misc.Xi

end
