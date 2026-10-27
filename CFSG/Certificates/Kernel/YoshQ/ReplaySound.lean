module

public import Certificates.Data.Kernel.YoshQ.Replay
public import CFSG.Certificates.Kernel.YoshQ.TabNSound
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import Std.Data.HashMap.Lemmas
import Init.Data.Nat.Fold

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.KS.BfsReplay CFSG.KS.HBfs CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.Fin76b

structure ReplayN (n w m k : Nat) (G E par lab : Nat → Nat) (pos : Nat → Nat → Nat)
    (cnt cap : Nat) : Prop where
  pos_cnt : 0 < cnt
  le_cap : cnt ≤ cap
  root : E 0 % 2 ^ (n * w) = pidn n w % 2 ^ (n * w)
  par0 : par 0 = 0
  lab0 : lab 0 = 0
  tree : ∀ i, 0 < i → i < cnt → par i < i ∧ lab i < k ∧
    E i % 2 ^ (n * w) = pmN n w (E (par i)) (G (lab i)) % 2 ^ (n * w)
  order : ∀ i, 0 < i → i + 1 < cnt → LexLt (par i) (lab i) (par (i + 1)) (lab (i + 1))
  close : ∀ h < cnt, ∀ j < k, pos h j < cnt ∧
    pmN n w (E h) (G j) % 2 ^ (n * w) = E (pos h j) % 2 ^ (n * w) ∧
    (pos h j = 0 ∨ ¬ LexLt h j (par (pos h j)) (lab (pos h j)))
  kinj : ∀ a < cnt, ∀ b < cnt, hkeyK m w (mask w) (E a) = hkeyK m w (mask w) (E b) → a = b
  finj : ∀ a < cnt, ∀ b < cnt, hkeyK n w (mask w) (E a) = hkeyK n w (mask w) (E b) → a = b

private theorem incrL_spec : ∀ l : List Nat, incrL l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [incrL, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := incrL_spec (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.mp ih).1 x hx)

private theorem sortedK_inj {key : Nat → Nat} {cnt : Nat} {S : List Nat}
    (h : sortedK key cnt S = true) : ∀ a < cnt, ∀ b < cnt, key a = key b → a = b := by
  simp only [sortedK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hlen, hlt⟩, hinc⟩ := h
  have hnd : (S.map key).Nodup := (incrL_spec _ hinc).imp ne_of_lt
  have hmem : ∀ a < cnt, a ∈ S := by
    intro a ha
    have hsub : S.toFinset ⊆ Finset.range cnt := fun x hx =>
      Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
    have hcard : (Finset.range cnt).card ≤ S.toFinset.card := by
      rw [Finset.card_range, List.toFinset_card_of_nodup (hnd.of_map key), hlen]
    rw [← List.mem_toFinset, Finset.eq_of_subset_of_card_le hsub hcard]
    exact Finset.mem_range.mpr ha
  intro a ha b hb hab
  exact List.inj_on_of_nodup_map hnd (hmem a ha) (hmem b hb) hab

private theorem lexB_iff_lexLt (a b c d : Nat) : lexB a b c d = true ↔ LexLt a b c d := by
  unfold lexB LexLt
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]

theorem replayK_sound {n w m cap cnt EP PL POS : Nat} {GS SM SF : List Nat}
    (h : replayK n w m cap GS cnt EP PL POS SM SF = true) :
    ReplayN n w m GS.length (fun j => GS.getD j 0) (fun i => fldN EP (n * w) i) (rpar PL)
      (rlab PL) (fun h j => fldN POS 16 (h * GS.length + j)) cnt cap := by
  unfold replayK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hcap⟩, hroot⟩, hpar⟩, hlab⟩, htree⟩, hord⟩, hclose⟩, hSM⟩, hSF⟩ := h
  refine ⟨Nat.blt_eq.mp h0, Nat.ble_eq.mp hcap, Nat.eq_of_beq_eq_true hroot,
    Nat.eq_of_beq_eq_true hpar, Nat.eq_of_beq_eq_true hlab, ?_, ?_, ?_, sortedK_inj hSM,
    sortedK_inj hSF⟩
  · intro i hi0 hi
    have := CFSG.KS.allN_spec htree i hi
    simp only [Bool.or_eq_true] at this
    rcases this with h | h
    · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
    · unfold treeAt at h
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      exact ⟨h.1.1, h.1.2, Nat.eq_of_beq_eq_true h.2⟩
  · intro i hi0 hi
    have := CFSG.KS.allN_spec hord i (by omega)
    simp only [Bool.or_eq_true] at this
    rcases this with (h | h) | h
    · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
    · rw [show Nat.blt (i + 1) cnt = true from Nat.blt_eq.mpr hi] at h
      exact absurd h (by decide)
    · exact (lexB_iff_lexLt _ _ _ _).mp h
  · intro a ha j hj
    have := CFSG.KS.allN_spec (CFSG.KS.allN_spec hclose a ha) j hj
    unfold closeAt at this
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, Nat.eq_of_beq_eq_true h2, ?_⟩
    rcases h3 with h3 | h3
    · exact Or.inl (Nat.eq_of_beq_eq_true h3)
    · right
      rw [← lexB_iff_lexLt]
      simpa using h3

variable {n w : Nat}

theorem tabN_congr {x y : Nat} (h : x % 2 ^ (n * w) = y % 2 ^ (n * w)) : tabN n w x = tabN n w y := by
  unfold tabN
  rw [h]

theorem hkey_of_fields {m : Nat} (hw : w ≤ 32) {T : Table} {x : Nat}
    (hT : ∀ i < m, (T[i]!).toNat = pg w (mask w) x i) :
    (hkey m T).toNat = hkeyK m w (mask w) x := by
  have step : ∀ i < m, ∀ a : UInt64,
      ((a ^^^ (T[i]!).toUInt64) * 1099511628211).toNat = hkStep a.toNat (pg w (mask w) x i) := by
    intro i hi a
    rw [UInt64.toNat_mul, UInt64.toNat_xor, UInt32.toNat_toUInt64, hT i hi]
    rfl
  have key : ∀ r ≤ m, (Nat.fold r (fun i _ h => (h ^^^ (T[i]!).toUInt64) * 1099511628211)
      (14695981039346656037 : UInt64)).toNat = hkGo w (mask w) x r 0 14695981039346656037 := by
    intro r
    induction r with
    | zero =>
      intro _
      rw [Nat.fold_zero]
      rfl
    | succ r ih =>
      intro hr
      rw [Nat.fold_succ, step r (by omega), ih (by omega), hkGo_last, Nat.zero_add]
  exact key m (Nat.le_refl m)

theorem toNat_getElem!_tabN (hw : w ≤ 32) {x i : Nat} (hi : i < n) :
    ((tabN n w x)[i]!).toNat = pg w (mask w) x i := by
  rw [getElem!_tabN]
  simp only [hi, ↓reduceIte]
  rw [toNat_ofNat_pg hw, pg_mod hi]

theorem hkey_tabN (hw : w ≤ 32) (x : Nat) : (hkey n (tabN n w x)).toNat = hkeyK n w (mask w) x :=
  hkey_of_fields hw fun _ hi => toNat_getElem!_tabN hw hi

theorem skey_tabN {m : Nat} (hm : m ≤ n) (hw : w ≤ 32) (x : Nat) :
    (skey m (tabN n w x)).toNat = hkeyK m w (mask w) x := by
  unfold skey
  apply hkey_of_fields hw
  intro i hi
  have hs : i < ((tabN n w x).extract 0 m).size := by simp [size_tabN]; omega
  rw [getElem!_pos _ i hs, Array.getElem_extract, ← getElem!_pos (tabN n w x) (0 + i)
    (by rw [size_tabN]; omega), Nat.zero_add, toNat_getElem!_tabN hw (by omega)]

theorem getElem!_mapTabN {GS : List Nat} {j : Nat} (hj : j < GS.length) :
    ((GS.map (tabN n w)).toArray)[j]! = tabN n w (GS.getD j 0) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getElem?_eq_getElem hj]

theorem hreplay_of (hn : n < 2 ^ 32) (hn24 : n < 16777216) (hnw : n + 1 < 2 ^ w) (hw : w ≤ 32)
    {m cnt cap : Nat} (hm : m ≤ n) {GS : List Nat} {E par lab : Nat → Nat}
    {pos : Nat → Nat → Nat}
    (R : ReplayN n w m GS.length (fun j => GS.getD j 0) E par lab pos cnt cap) :
    HReplay (skey m) (fun j y => compT n y ((GS.map (tabN n w)).toArray)[j]!)
      ((GS.map (tabN n w)).toArray).size (idT n) cnt (fun i => tabN n w (E i)) par lab pos := by
  have hk : ((GS.map (tabN n w)).toArray).size = GS.length := by simp
  rw [hk]
  refine ⟨R.pos_cnt, ?_, R.par0, R.lab0, ?_, ?_, R.order, ?_⟩
  · rw [idT_tabN hn24 hnw hw]
    exact tabN_congr R.root
  · intro a ha b hb e
    have e' := congrArg UInt64.toNat e
    rw [skey_tabN hm hw, skey_tabN hm hw] at e'
    exact R.kinj a ha b hb e'
  · intro i h0 hi
    obtain ⟨h1, h2, h3⟩ := R.tree i h0 hi
    refine ⟨h1, h2, ?_⟩
    rw [getElem!_mapTabN h2, compT_tabN hw hn]
    exact tabN_congr h3
  · intro h hh j hj
    obtain ⟨h1, h2, h3⟩ := R.close h hh j hj
    refine ⟨h1, ?_, h3⟩
    rw [getElem!_mapTabN hj, compT_tabN hw hn]
    exact tabN_congr h2

theorem mulClosureS_eq_hbfs (n m : Nat) (gens : Array Table) (cap : Nat) :
    mulClosureS n m gens cap =
      hbfs (skey m) (fun l y => compT n y gens[l]!) gens.size (idT n) cap := rfl

theorem mulClosureS_eq (hn : n < 2 ^ 32) (hn24 : n < 16777216) (hnw : n + 1 < 2 ^ w) (hw : w ≤ 32)
    {m cnt cap cap' : Nat} (hm : m ≤ n) {GS : List Nat} {E par lab : Nat → Nat}
    {pos : Nat → Nat → Nat}
    (R : ReplayN n w m GS.length (fun j => GS.getD j 0) E par lab pos cnt cap) (hcap : cnt ≤ cap') :
    mulClosureS n m ((GS.map (tabN n w)).toArray) cap' =
      (Array.ofFn (n := cnt) fun i => tabN n w (E i.val), Array.ofFn (n := cnt) fun i => par i.val,
        Array.ofFn (n := cnt) fun i => lab i.val) := by
  rw [mulClosureS_eq_hbfs]
  exact hbfs_replay (hreplay_of hn hn24 hnw hw hm R) hcap

theorem hashIndexS_get {m : Nat} {L : Array Table}
    (hinj : ∀ a < L.size, ∀ b < L.size, skey m L[a]! = skey m L[b]! → a = b) :
    ∀ p < L.size, (hashIndexS m L)[skey m L[p]!]? = some p := by
  have key : ∀ j ≤ L.size, ∀ p < j,
      ((List.range j).foldl (fun idx i => idx.insert (skey m L[i]!) i)
        (∅ : Std.HashMap UInt64 Nat))[skey m L[p]!]? = some p := by
    intro j
    induction j with
    | zero => intro _ p hp; omega
    | succ j ih =>
      intro hj p hp
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getElem?_insert]
      by_cases e : p = j
      · subst e
        simp
      · have hne : (skey m L[j]! == skey m L[p]!) = false := by
          rw [beq_eq_false_iff_ne]
          intro h'
          exact e (hinj j (by omega) p (by omega) h').symm
        rw [hne]
        exact ih (by omega) p (by omega)
  intro p hp
  exact key L.size (Nat.le_refl _) p hp

theorem closedOKS_of {n m : Nat} {gens L : Array Table}
    (hinj : ∀ a < L.size, ∀ b < L.size, skey m L[a]! = skey m L[b]! → a = b)
    (hcl : ∀ a < L.size, ∀ j < gens.size, ∃ p < L.size, compT n L[a]! gens[j]! = L[p]!) :
    closedOKS n m gens L = true := by
  unfold closedOKS
  rw [Array.all_eq_true]
  intro a ha
  rw [Array.all_eq_true]
  intro j hj
  obtain ⟨p, hp, e⟩ := hcl a ha j hj
  rw [← getElem!_pos L a ha, ← getElem!_pos gens j hj, e]
  unfold memTS
  rw [hashIndexS_get hinj p hp]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hp, tblEqH_self n _⟩

theorem ofFn_get {β : Type} [Inhabited β] {cnt i : Nat} (f : Nat → β) (hi : i < cnt) :
    (Array.ofFn (n := cnt) fun j => f j.val)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem enumOK_of (hn : n < 2 ^ 32) (hn24 : n < 16777216) (hnw : n + 1 < 2 ^ w) (hw : w ≤ 32)
    {m cnt cap size : Nat} (hm : m ≤ n) {GS : List Nat} {E par lab : Nat → Nat}
    {pos : Nat → Nat → Nat}
    (R : ReplayN n w m GS.length (fun j => GS.getD j 0) E par lab pos cnt cap)
    (hperm : ((GS.map (tabN n w)).toArray).all
      (fun x => CFSG.Sporadic.SmallOddCore.permOK n x) = true) (hsz : cnt = size) :
    enumOK n m ((GS.map (tabN n w)).toArray)
      (Array.ofFn (n := cnt) fun i => tabN n w (E i.val), Array.ofFn (n := cnt) fun i => par i.val,
        Array.ofFn (n := cnt) fun i => lab i.val) size = true := by
  have H := hreplay_of hn hn24 hnw hw hm R
  have hT := mulTree_of H
  have hD : hkeysDistinct n (Array.ofFn (n := cnt) fun i => tabN n w (E i.val)).toList = true :=
    hkeysDistinct_ofFn (U := fun i => tabN n w (E i)) fun a ha b hb e => by
      rw [hkey_tabN hw, hkey_tabN hw] at e
      exact R.finj a ha b hb e
  have hS : ((Array.ofFn (n := cnt) fun i => tabN n w (E i.val)).size == size) = true := by
    simp [hsz]
  unfold enumOK
  rw [hperm, hT, hD, hS]
  simp only [Bool.true_and, Bool.and_true]
  · apply closedOKS_of
    · intro a ha b hb e
      have ha' : a < cnt := by simpa using ha
      have hb' : b < cnt := by simpa using hb
      rw [ofFn_get (fun i => tabN n w (E i)) ha', ofFn_get (fun i => tabN n w (E i)) hb'] at e
      exact H.kinj a ha' b hb' e
    · intro a ha j hj
      have ha' : a < cnt := by simpa using ha
      obtain ⟨h1, h2, -⟩ := H.close a ha' j hj
      refine ⟨pos a j, by simpa using h1, ?_⟩
      rw [ofFn_get (fun i => tabN n w (E i)) ha', ofFn_get (fun i => tabN n w (E i)) h1]
      exact h2

structure RecOK (n w m cap : Nat) (gens : Array Table) (GS RL : List Nat) (cnt EP PL POS : Nat)
    (SM SF : List Nat) : Prop where
  gens_eq : gens = (GS.map (tabN n w)).toArray
  check : replayK n w m cap GS cnt EP PL POS SM SF = true
  rl : (List.range cnt).map (fldN EP (n * w)) = RL

theorem ofFn_tabN_eq {cnt EP : Nat} {RL : List Nat} (hrl : (List.range cnt).map (fldN EP (n * w)) = RL) :
    (Array.ofFn (n := cnt) fun i => tabN n w (fldN EP (n * w) i.val)) = (RL.map (tabN n w)).toArray := by
  rw [← hrl, List.map_map]
  apply Array.ext (by simp)
  intro i h1 h2
  simp

theorem RecOK.size_le {m cap : Nat} {gens : Array Table} {GS RL : List Nat} {cnt EP PL POS : Nat}
    {SM SF : List Nat} (R : RecOK n w m cap gens GS RL cnt EP PL POS SM SF) : cnt ≤ cap :=
  (replayK_sound R.check).le_cap

theorem RecOK.closure_fst (hn24 : n < 16777216) (hnw : n + 1 < 2 ^ w) (hw : w ≤ 32) {m cap : Nat}
    (hm : m ≤ n) {gens : Array Table} {GS RL : List Nat} {cnt EP PL POS : Nat} {SM SF : List Nat}
    (R : RecOK n w m cap gens GS RL cnt EP PL POS SM SF) :
    (mulClosureS n m gens cap).1 = (RL.map (tabN n w)).toArray := by
  rw [R.gens_eq, mulClosureS_eq (Nat.lt_trans hn24 (by decide)) hn24 hnw hw hm
    (replayK_sound R.check) R.size_le]
  exact ofFn_tabN_eq R.rl

theorem RecOK.enumOK (hn24 : n < 16777216) (hnw : n + 1 < 2 ^ w) (hw : w ≤ 32) {m cap size : Nat}
    (hm : m ≤ n) {gens : Array Table} {GS RL : List Nat} {cnt EP PL POS : Nat} {SM SF : List Nat}
    (R : RecOK n w m cap gens GS RL cnt EP PL POS SM SF)
    (hperm : gens.all (fun x => CFSG.Sporadic.SmallOddCore.permOK n x) = true) (hsz : cnt = size) :
    enumOK n m gens (mulClosureS n m gens cap) size = true := by
  have hR := replayK_sound R.check
  rw [R.gens_eq, mulClosureS_eq (Nat.lt_trans hn24 (by decide)) hn24 hnw hw hm hR R.size_le]
  rw [R.gens_eq] at hperm
  exact enumOK_of (Nat.lt_trans hn24 (by decide)) hn24 hnw hw hm hR hperm hsz

end CFSG.KC.YoshQ

end
