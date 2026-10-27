module

public import Certificates.Data.Kernel.Q47K
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
import CFSG.Certificates.Kernel.HexaKGlue
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.KC.Bfs CFSG.KC.BfsPin
open CFSG.ComponentClassification.AS81.HeSylow (certN eltsN enumCheckN)

variable {n w ng : Nat} {G : Nat → Nat}

theorem memK_eq (L : List Nat) (x : Nat) : memK L x = decide (x ∈ L) := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    change CFSG.KLie.CT.orB (Nat.beq x y) (memK L x) = _
    rw [ih, CFSG.KC.HexaK.orB_eq]
    cases h : Nat.beq x y
    · have := Nat.ne_of_beq_eq_false h
      simp [this]
    · have := Nat.eq_of_beq_eq_true h
      simp [this]

theorem strictL_eq' (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by cases y <;> rfl

def addN (L : List Nat) (y : Nat) : List Nat := if y ∈ L then L else L ++ [y]

theorem runStep_rec (x : Nat) (pts : List Nat) : ∀ m,
    Nat.rec (motive := fun _ => List Nat) pts (fun k acc => strictL (HexaK.mul n w (G k) x) fun y =>
      Bool.rec (motive := fun _ => List Nat) (acc ++ [y]) acc (memK acc y)) m =
    (List.range m).foldl (fun acc k => addN acc (HexaK.mul n w (G k) x)) pts
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← runStep_rec x pts m]
    have e : ∀ acc : List Nat, strictL (HexaK.mul n w (G m) x) (fun y =>
        Bool.rec (motive := fun _ => List Nat) (acc ++ [y]) acc (memK acc y)) =
        addN acc (HexaK.mul n w (G m) x) := by
      intro acc
      rw [strictL_eq', memK_eq]
      unfold addN
      by_cases h : HexaK.mul n w (G m) x ∈ acc
      · rw [decide_eq_true h, ite_eq_left h]
      · rw [decide_eq_false h, ite_eq_right h]
    exact e _

theorem runStep_eq (x : Nat) (pts : List Nat) :
    runStep n w ng G x pts = (List.range ng).foldl (fun acc k => addN acc (HexaK.mul n w (G k) x)) pts :=
  runStep_rec x pts ng

noncomputable def rkF (n w ng : Nat) (G : Nat → Nat) (st : List Nat × Nat) : List Nat × Nat :=
  if st.2 < st.1.length then (runStep n w ng G (st.1.getD st.2 0) st.1, st.2 + 1) else st

theorem runK_iter (fuel : Nat) :
    runK n w ng G fuel = ((rkF n w ng G)^[fuel] ([pidn n w], 0)).1 := by
  unfold runK
  congr 1
  induction fuel with
  | zero => rfl
  | succ f ih =>
    rw [Function.iterate_succ_apply', ← ih]
    have e : ∀ st : List Nat × Nat, Bool.rec (motive := fun _ => List Nat × Nat) st
        (runStep n w ng G (st.1.getD st.2 0) st.1, Nat.succ st.2) (Nat.blt st.2 st.1.length) =
        rkF n w ng G st := by
      intro st
      unfold rkF
      cases h : Nat.blt st.2 st.1.length
      · rw [ite_eq_right fun h' => by rw [Nat.blt_eq.mpr h'] at h; cases h]
      · rw [ite_eq_left (Nat.blt_eq.mp h)]
    exact e _

theorem getD_mem {L : List Nat} {j : Nat} (h : j < L.length) : L.getD j 0 ∈ L := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem addN_getD {L : List Nat} {j : Nat} (y : Nat) (h : j < L.length) :
    (addN L y).getD j 0 = L.getD j 0 := by
  unfold addN
  split
  · rfl
  · rw [List.getD_append _ _ _ _ h]

theorem addN_len (L : List Nat) (y : Nat) : L.length ≤ (addN L y).length := by
  unfold addN
  split
  · exact le_rfl
  · simp

theorem mem_addN (L : List Nat) (y : Nat) : y ∈ addN L y := by
  unfold addN
  split
  · assumption
  · simp

theorem mem_addN_of {L : List Nat} {z : Nat} (y : Nat) (h : z ∈ L) : z ∈ addN L y := by
  unfold addN
  split
  · exact h
  · simp [h]

theorem mem_addN_iff {L : List Nat} {z y : Nat} (h : z ∈ addN L y) : z ∈ L ∨ z = y := by
  unfold addN at h
  split at h
  · exact Or.inl h
  · simpa using h

theorem foldl_addN (f : Nat → Nat) : ∀ (ks : List Nat) (L : List Nat),
    L.length ≤ (ks.foldl (fun acc k => addN acc (f k)) L).length ∧
    (∀ j < L.length, (ks.foldl (fun acc k => addN acc (f k)) L).getD j 0 = L.getD j 0) ∧
    (∀ z ∈ L, z ∈ ks.foldl (fun acc k => addN acc (f k)) L) ∧
    (∀ k ∈ ks, f k ∈ ks.foldl (fun acc k => addN acc (f k)) L) ∧
    (∀ z ∈ ks.foldl (fun acc k => addN acc (f k)) L, z ∈ L ∨ ∃ k ∈ ks, z = f k)
  | [], L => ⟨le_rfl, fun _ _ => rfl, fun _ h => h, fun _ h => absurd h List.not_mem_nil,
      fun _ h => Or.inl h⟩
  | k :: ks, L => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4, h5⟩ := foldl_addN f ks (addN L (f k))
    refine ⟨le_trans (addN_len L _) h1, fun j hj => ?_, fun z hz => h3 z (mem_addN_of _ hz),
      fun k' hk' => ?_, fun z hz => ?_⟩
    · rw [h2 j (lt_of_lt_of_le hj (addN_len L _)), addN_getD _ hj]
    · rcases List.mem_cons.1 hk' with rfl | hk'
      · exact h3 _ (mem_addN L _)
      · exact h4 k' hk'
    · rcases h5 z hz with hz | ⟨k', hk', e⟩
      · rcases mem_addN_iff hz with hz | e
        · exact Or.inl hz
        · exact Or.inr ⟨k, List.mem_cons_self, e⟩
      · exact Or.inr ⟨k', List.mem_cons_of_mem k hk', e⟩

def Sim (n w : Nat) (L : List Nat) (pts : Array (Array Nat)) (idx : Std.HashMap Nat Nat) : Prop :=
  (∀ y ∈ L, PP n w y) ∧ pts = (L.map (unpack n w)).toArray ∧
    (∀ j < L.length, idx[keyA n (List.range n) (unpack n w (L.getD j 0))]? = some j) ∧
    ∀ m j, idx[m]? = some j → j < L.length ∧ keyA n (List.range n) (unpack n w (L.getD j 0)) = m

theorem key_inj {p q : Nat} (hp : PP n w p) (hq : PP n w q)
    (h : keyA n (List.range n) (unpack n w p) = keyA n (List.range n) (unpack n w q)) : p = q :=
  keyA_range_inj hp.1 hq.1 h

section Sim

variable {gs : Array (Array Nat)}
  (hact : ∀ k < ng, ∀ y, PP n w y → leftA n gs k (unpack n w y) = unpack n w (HexaK.mul n w (G k) y))
  (hPG : ∀ k < ng, PP n w (G k))
include hact hPG

theorem gF_sim {L : List Nat} {pts : Array (Array Nat)} {idx : Std.HashMap Nat Nat}
    {par lab row : Array Nat} {i k : Nat} (hs : Sim n w L pts idx) (hi : i < L.length)
    (hk : k < ng) :
    Sim n w (addN L (HexaK.mul n w (G k) (L.getD i 0)))
      (gF (leftA n gs) (keyA n (List.range n)) i (pts, par, lab, idx, row) k).1
      (gF (leftA n gs) (keyA n (List.range n)) i (pts, par, lab, idx, row) k).2.2.2.1 := by
  obtain ⟨hP, rfl, h1, h2⟩ := hs
  have hx : PP n w (L.getD i 0) := hP _ (getD_mem hi)
  have hpi : (L.map (unpack n w)).toArray[i]! = unpack n w (L.getD i 0) := by
    rw [getElem!_pos _ i (by simpa using hi), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  have hq : PP n w (HexaK.mul n w (G k) (L.getD i 0)) := (hPG k hk).mul hx
  have hact' := hact k hk _ hx
  simp only [gF]
  rw [hpi, hact']
  generalize HexaK.mul n w (G k) (L.getD i 0) = q at hq ⊢
  split
  · next j heq =>
    rw [Std.HashMap.get?_eq_getElem?] at heq
    obtain ⟨hj, hkj⟩ := h2 _ _ heq
    have e : L.getD j 0 = q := key_inj (hP _ (getD_mem hj)) hq hkj
    have hmem : q ∈ L := e ▸ getD_mem hj
    unfold addN
    rw [ite_eq_left hmem]
    exact ⟨hP, rfl, h1, h2⟩
  · next heq =>
    rw [Std.HashMap.get?_eq_getElem?] at heq
    have hnot : q ∉ L := by
      intro hm
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
      have := h1 j hj
      rw [List.getD_eq_getElem _ _ hj, e, heq] at this
      cases this
    have hne : ∀ j < L.length, (keyA n (List.range n) (unpack n w q) ==
        keyA n (List.range n) (unpack n w (L.getD j 0))) = false := by
      intro j hj
      rw [beq_eq_false_iff_ne]
      intro e
      exact hnot (key_inj hq (hP _ (getD_mem hj)) e ▸ getD_mem hj)
    unfold addN
    rw [ite_eq_right hnot]
    have hlen : (L.map (unpack n w)).toArray.size = L.length := by simp
    have hlast : (L ++ [q]).getD L.length 0 = q := by
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      rfl
    refine ⟨fun y hy => ?_, by simp, fun j hj => ?_, fun m j h => ?_⟩
    · rcases List.mem_append.1 hy with hy | hy
      · exact hP y hy
      · rw [List.mem_singleton.1 hy]
        exact hq
    · rw [hlen, Std.HashMap.getElem?_insert]
      rw [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [List.getD_append _ _ _ _ hj, hne j hj, ite_eq_right Bool.false_ne_true]
        exact h1 j hj
      · rw [hlast, beq_self_eq_true, ite_eq_left rfl]
    · rw [hlen, Std.HashMap.getElem?_insert] at h
      rw [List.length_append, List.length_singleton]
      split at h
      · next e =>
        rw [beq_iff_eq] at e
        cases h
        exact ⟨Nat.lt_succ_self _, by rw [hlast, e]⟩
      · obtain ⟨hj, e⟩ := h2 m j h
        exact ⟨Nat.lt_succ_of_lt hj, by rw [List.getD_append _ _ _ _ hj, e]⟩

theorem fold_sim {i x : Nat} : ∀ (ks : List Nat), (∀ k ∈ ks, k < ng) →
    ∀ (L : List Nat) (st : Array (Array Nat) × Array Nat × Array Nat × Std.HashMap Nat Nat × Array Nat),
    Sim n w L st.1 st.2.2.2.1 → i < L.length → L.getD i 0 = x →
    Sim n w (ks.foldl (fun acc k => addN acc (HexaK.mul n w (G k) x)) L)
      (ks.foldl (gF (leftA n gs) (keyA n (List.range n)) i) st).1
      (ks.foldl (gF (leftA n gs) (keyA n (List.range n)) i) st).2.2.2.1
  | [], _, _, _, hs, _, _ => hs
  | k :: ks, hks, L, st, hs, hi, hx => by
    obtain ⟨pts, par, lab, idx, row⟩ := st
    rw [List.foldl_cons, List.foldl_cons]
    have hk := hks k List.mem_cons_self
    have h1 := gF_sim (row := row) (par := par) (lab := lab) hact hPG hs hi hk
    rw [hx] at h1
    exact fold_sim ks (fun k' hk' => hks k' (List.mem_cons_of_mem k hk')) _ _ h1
      (lt_of_lt_of_le hi (addN_len L _)) (by rw [addN_getD _ hi, hx])

theorem gLoop_sim (hs : gs.size = ng) : ∀ (f i : Nat) (L : List Nat) (pts : Array (Array Nat))
    (edges : Array (Array Nat)) (par lab : Array Nat) (idx : Std.HashMap Nat Nat),
    Sim n w L pts idx → i ≤ L.length →
    (gLoop (leftA n gs) gs.size (keyA n (List.range n)) f i pts edges par lab idx).1 =
      (((rkF n w ng G)^[f] (L, i)).1.map (unpack n w)).toArray := by
  intro f
  induction f with
  | zero =>
    intro i L pts edges par lab idx hsim _
    exact hsim.2.1
  | succ f ih =>
    intro i L pts edges par lab idx hsim hi
    have hsz : pts.size = L.length := by rw [hsim.2.1]; simp
    rw [gLoop, Function.iterate_succ_apply]
    split
    · next hlt =>
      have hlt' : i < L.length := hsz ▸ hlt
      have e1 : rkF n w ng G (L, i) = (runStep n w ng G (L.getD i 0) L, i + 1) := by
        unfold rkF
        rw [ite_eq_left hlt']
      rw [e1, runStep_eq]
      have hfold := fold_sim hact hPG (List.range ng) (fun k hk => List.mem_range.1 hk) L
        (pts, par, lab, idx, #[]) hsim hlt' rfl
      have e2 : gStep (leftA n gs) gs.size (keyA n (List.range n)) i (pts, par, lab, idx) =
          (List.range ng).foldl (gF (leftA n gs) (keyA n (List.range n)) i)
            (pts, par, lab, idx, #[]) := by
        unfold gStep
        rw [hs]
      rw [e2]
      have hle := (foldl_addN (fun k => HexaK.mul n w (G k) (L.getD i 0)) (List.range ng) L).1
      generalize (List.range ng).foldl (gF (leftA n gs) (keyA n (List.range n)) i)
        (pts, par, lab, idx, #[]) = s at hfold
      obtain ⟨a, b, l, d, r⟩ := s
      exact ih _ _ a (edges.push r) b l d hfold (by omega)
    · next hge =>
      have e1 : rkF n w ng G (L, i) = (L, i) := by
        unfold rkF
        rw [ite_eq_right (by rw [← hsz]; exact hge)]
      rw [e1, Function.iterate_fixed e1]
      exact hsim.2.1

end Sim

def RInv (n w ng : Nat) (G : Nat → Nat) (gs : Array (Array Nat)) (st : List Nat × Nat) : Prop :=
  (∀ y ∈ st.1, PP n w y ∧ Reach (leftA n gs) gs.size (idA n) (unpack n w y)) ∧
    st.2 ≤ st.1.length ∧ (∀ j < st.2, ∀ k < ng, HexaK.mul n w (G k) (st.1.getD j 0) ∈ st.1) ∧
    0 < st.1.length ∧ st.1.getD 0 0 = pidn n w

theorem rInv_step {gs : Array (Array Nat)} (hs : gs.size = ng)
    (hact : ∀ k < ng, ∀ y, PP n w y → leftA n gs k (unpack n w y) = unpack n w (HexaK.mul n w (G k) y))
    (hPG : ∀ k < ng, PP n w (G k)) {st : List Nat × Nat} (h : RInv n w ng G gs st) :
    RInv n w ng G gs (rkF n w ng G st) := by
  obtain ⟨L, i⟩ := st
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  unfold rkF
  dsimp only
  split
  · next hlt =>
    rw [runStep_eq]
    obtain ⟨f1, f2, f3, f4, f5⟩ := foldl_addN (fun k => HexaK.mul n w (G k) (L.getD i 0))
      (List.range ng) L
    have hx := h1 _ (getD_mem hlt)
    refine ⟨fun y hy => ?_, Nat.succ_le_of_lt (lt_of_lt_of_le hlt f1), fun j hj k hk => ?_,
      lt_of_lt_of_le h4 f1, by rw [f2 0 h4, h5]⟩
    · rcases f5 y hy with hy | ⟨k, hk, rfl⟩
      · exact h1 y hy
      · have hk' := List.mem_range.1 hk
        refine ⟨(hPG k hk').mul hx.1, ?_⟩
        rw [← hact k hk' _ hx.1]
        exact Reach.step k (hs ▸ hk') hx.2
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [f2 j (by omega)]
        exact f3 _ (h3 j hj k hk)
      · rw [f2 _ hlt]
        exact f4 k (List.mem_range.2 hk)
  · exact ⟨h1, h2, h3, h4, h5⟩

theorem rkF_count (s : List Nat × Nat) (hs : s.2 = 0) : ∀ f,
    ((rkF n w ng G)^[f] s).2 = f ∨ rkF n w ng G ((rkF n w ng G)^[f] s) = (rkF n w ng G)^[f] s
  | 0 => Or.inl hs
  | f + 1 => by
    rw [Function.iterate_succ_apply']
    rcases rkF_count s hs f with h | h
    · generalize (rkF n w ng G)^[f] s = t at h ⊢
      by_cases hlt : t.2 < t.1.length
      · have e : rkF n w ng G t = (runStep n w ng G (t.1.getD t.2 0) t.1, t.2 + 1) := by
          unfold rkF
          rw [ite_eq_left hlt]
        rw [e]
        exact Or.inl (by rw [h])
      · have e : rkF n w ng G t = t := by
          unfold rkF
          rw [ite_eq_right hlt]
        rw [e]
        exact Or.inr e
    · rw [h]
      exact Or.inr h

theorem runK_sound {gs : List (Array Nat)} {fuel : Nat} (hsz : szOK n w = true)
    (hl : gs.length = ng)
    (hb : ∀ k < ng, gs[k]! = unpack n w (G k) ∧
      permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true)
    (hf : (runK n w ng G fuel).length ≤ fuel) (h4 : fuel ≤ 4000) :
    (∀ y ∈ runK n w ng G fuel, PP n w y) ∧ eltsN n gs = (runK n w ng G fuel).map (unpack n w) ∧
      enumCheckN n gs (runK n w ng G fuel).length = true := by
  have hA : gs.toArray.size = ng := by simpa using hl
  have hAk : ∀ k < ng, gs.toArray[k]! = unpack n w (G k) := by
    intro k hk
    rw [getElem!_pos gs.toArray k (by simpa [hl] using hk), List.getElem_toArray,
      ← getElem!_pos gs k (by omega)]
    exact (hb k hk).1
  have hPG : ∀ k < ng, PP n w (G k) := fun k hk => PP_of_permOK hsz (hb k hk).2
  have hact : ∀ k < ng, ∀ y, PP n w y →
      leftA n gs.toArray k (unpack n w y) = unpack n w (HexaK.mul n w (G k) y) := by
    intro k hk y hy
    unfold leftA
    rw [hAk k hk, compA_PP (hPG k hk) hy]
    rfl
  have hid : idA n = unpack n w (pidn n w) := idA_eq hsz
  have hPid := PP.id (n := n) (w := w) hsz
  have hinv : ∀ f, RInv n w ng G gs.toArray ((rkF n w ng G)^[f] ([pidn n w], 0)) := by
    intro f
    induction f with
    | zero =>
      refine ⟨fun y hy => ?_, Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j),
        Nat.one_pos, rfl⟩
      rw [List.mem_singleton.1 hy, ← hid]
      exact ⟨hPid, Reach.root⟩
    | succ f ih =>
      rw [Function.iterate_succ_apply']
      exact rInv_step hA hact hPG ih
  rw [runK_iter] at hf ⊢
  generalize hst : (rkF n w ng G)^[fuel] ([pidn n w], 0) = st at hf ⊢
  have hI : RInv n w ng G gs.toArray st := hst ▸ hinv fuel
  have hfix : rkF n w ng G st = st := by
    rcases rkF_count (n := n) (w := w) (ng := ng) (G := G) ([pidn n w], 0) rfl fuel with h | h
    · rw [hst] at h
      unfold rkF
      rw [ite_eq_right (by have := hI.2.1; omega)]
    · rwa [hst] at h
  have hdone : ¬ st.2 < st.1.length := by
    intro hlt
    have e := congrArg Prod.snd hfix
    unfold rkF at e
    rw [ite_eq_left hlt] at e
    simp at e
  have h4000 : (rkF n w ng G)^[4000] ([pidn n w], 0) = st := by
    rw [← Nat.sub_add_cancel h4, Function.iterate_add_apply, hst, Function.iterate_fixed hfix]
  have hsim0 : Sim n w [pidn n w] #[idA n]
      ((∅ : Std.HashMap Nat Nat).insert (keyA n (List.range n) (idA n)) 0) := by
    have e0 : [pidn n w].getD 0 0 = pidn n w := rfl
    refine ⟨fun y hy => by rw [List.mem_singleton.1 hy]; exact hPid, by rw [hid]; rfl,
      fun j hj => ?_, fun m j h => ?_⟩
    · have e : j = 0 := by simpa using hj
      subst e
      rw [e0, ← hid]
      simp
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · next e =>
        rw [beq_iff_eq] at e
        cases h
        exact ⟨Nat.one_pos, by rw [e0, ← e, hid]⟩
      · rw [Std.HashMap.getElem?_empty] at h
        cases h
  have hpts : (certN n gs).pts = (st.1.map (unpack n w)).toArray := by
    unfold certN enumBfs
    rw [arrBfs_eq]
    change (gLoop (leftA n gs.toArray) gs.toArray.size (keyA n (List.range n)) 4000 0 #[idA n] #[]
      #[0] #[0] ((∅ : Std.HashMap Nat Nat).insert (keyA n (List.range n) (idA n)) 0)).1 = _
    rw [gLoop_sim hact hPG hA 4000 0 [pidn n w] _ _ _ _ _ hsim0 (Nat.zero_le _), h4000]
  refine ⟨fun y hy => (hI.1 y hy).1, ?_, ?_⟩
  · unfold eltsN
    rw [hpts]
  obtain ⟨h1, h2, h3, h4', h5⟩ := hI
  have hlen : st.2 = st.1.length := by omega
  let Sf : Finset (Array Nat) := (st.1.map (unpack n w)).toFinset
  have hmemS : ∀ x, x ∈ Sf ↔ ∃ y ∈ st.1, unpack n w y = x := by
    intro x
    simp only [Sf, List.mem_toFinset, List.mem_map]
  have hroot : idA n ∈ Sf := (hmemS _).2 ⟨_, h5 ▸ getD_mem h4', hid.symm⟩
  have hclosed : ∀ x ∈ Sf, ∀ k < gs.toArray.size, leftA n gs.toArray k x ∈ Sf := by
    intro x hx k hk
    obtain ⟨y, hy, rfl⟩ := (hmemS x).1 hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    have hk' : k < ng := hA ▸ hk
    rw [hact k hk' _ (h1 _ hy).1]
    refine (hmemS _).2 ⟨_, ?_, rfl⟩
    have := h3 j (by omega) k hk'
    rwa [List.getD_eq_getElem _ _ hj] at this
  have hR : ∀ x ∈ Sf, Reach (leftA n gs.toArray) gs.toArray.size (idA n) x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmemS x).1 hx
    exact (h1 y hy).2
  have hS : ∀ x, Reach (leftA n gs.toArray) gs.toArray.size (idA n) x ↔ x ∈ Sf :=
    reach_iff_of_closed hroot hclosed hR
  have hvg : ∀ k < gs.toArray.size, validA n gs.toArray[k]! = true := by
    intro k hk
    rw [hAk k (hA ▸ hk)]
    exact validA_unpack (hb k (hA ▸ hk)).2
  have hv : ∀ x ∈ Sf, validA n x = true := by
    intro x hx
    have hr := hR x hx
    clear hx
    induction hr with
    | root => exact CFSG.RankThree.Native.F2.validA_of_rep rep_idA
    | step k hk1 _ ih =>
      unfold leftA
      exact CFSG.RankThree.Native.F2.validA_of_rep
        (rep_compA (rep_of_validA (hvg k hk1)) (rep_of_validA ih))
  have hkeyS : ∀ x ∈ Sf, ∀ y ∈ Sf, keyA n (List.range n) x = keyA n (List.range n) y → x = y := by
    intro x hx y hy e
    obtain ⟨p, hp, rfl⟩ := (hmemS x).1 hx
    obtain ⟨q, hq, rfl⟩ := (hmemS y).1 hy
    rw [key_inj (h1 p hp).1 (h1 q hq).1 e]
  have hcard : Sf.card ≤ 4000 := by
    have e1 := List.toFinset_card_le (st.1.map (unpack n w))
    rw [List.length_map] at e1
    have e2 : Sf.card = (st.1.map (unpack n w)).toFinset.card := rfl
    omega
  obtain ⟨hcert, -, -, -⟩ := arrBfs_spec (act := leftA n gs.toArray) (ngen := gs.toArray.size)
    (valid := validA n) (key := keyA n (List.range n)) (root := idA n) (fuel := 4000) Sf hS hv
    hkeyS hcard
  unfold enumCheckN
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold enumOK
    rw [Bool.and_eq_true]
    exact ⟨allLt_iff.2 hvg, hcert⟩
  · rw [hpts]
    simp

end CFSG.KC.Q47K

end
