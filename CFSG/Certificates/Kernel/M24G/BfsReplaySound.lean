module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.ReplayFacts

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

private abbrev ksBfsS (α : Type) : Type :=
  Array α × Array Nat × Array Nat × Std.HashMap Nat Nat × Nat

private def ksBfsInner {α : Type} [Inhabited α] (key : α → Nat) (x : α) (h : Nat)
    (s : α → α) (st : ksBfsS α) : Id (ForInStep (ksBfsS α)) :=
  if (!st.2.2.2.1.contains (key (s x))) = true then
    pure (.yield (st.1.push (s x), st.2.1.push h, st.2.2.1.push st.2.2.2.2,
      st.2.2.2.1.insert (key (s x)) st.1.size, st.2.2.2.2 + 1))
  else pure (.yield (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2 + 1))

private def ksBfsOuter {α : Type} [Inhabited α] (key : α → Nat) (steps : List (α → α))
    (_ : Nat) (st : ksBfsS α) : Id (ForInStep (ksBfsS α)) :=
  if st.2.2.2.2 < st.1.size then do
    let t ← forIn steps (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0)
      (ksBfsInner key st.1[st.2.2.2.2]! st.2.2.2.2)
    pure (.yield (t.1, t.2.1, t.2.2.1, t.2.2.2.1, st.2.2.2.2 + 1))
  else pure (.done st)

private def ksBfsInit {α : Type} (key : α → Nat) (base : α) : ksBfsS α :=
  (#[base], #[0], #[0], (∅ : Std.HashMap Nat Nat).insert (key base) 0, 0)

private theorem ksBfs_eq {α : Type} [Inhabited α] (key : α → Nat) (steps : List (α → α))
    (base : α) (fuel : Nat) :
    Native.bfs key steps base fuel =
      (let s := Id.run (forIn (List.range' 0 fuel) (ksBfsInit key base) (ksBfsOuter key steps))
       (s.1, s.2.1, s.2.2.1)) := by
  unfold Native.bfs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def ksBfsInv {α : Type} [Inhabited α] (key : α → Nat) (L : List α) (par gen : List Nat)
    (lA : Array α) (pA gA : Array Nat) (mA : Std.HashMap Nat Nat) (sz : Nat) : Prop :=
  lA = (L.take sz).toArray ∧ pA = (par.take sz).toArray ∧ gA = (gen.take sz).toArray ∧
    (∀ k, mA.contains k = true ↔ ∃ i < sz, key L[i]! = k) ∧
    sz ≤ L.length ∧ par.length = L.length ∧ gen.length = L.length

private theorem ksBfs_take_getElem! {β : Type} [Inhabited β] {l : List β} {sz i : Nat}
    (hi : i < sz) : ((l.take sz).toArray)[i]! = l[i]! := by
  rw [List.getElem!_toArray]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take, if_pos hi]

private theorem ksBfs_push_take {β : Type} {l : List β} {sz : Nat} {a : Array β}
    (ha : a = (l.take sz).toArray) (hlt : sz < l.length) {y : β} (hy : l[sz] = y) :
    a.push y = (l.take (sz + 1)).toArray := by
  rw [ha, List.push_toArray, List.take_succ_eq_append_getElem hlt, hy]

private theorem ksBfs_contains_false {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {L : List α} {mA : Std.HashMap Nat Nat} {sz k : Nat}
    (hd : ∀ (i : Nat) (hi : i < L.length) (j : Nat) (hj : j < L.length),
      key L[i] = key L[j] → i = j)
    (hmap : ∀ k, mA.contains k = true ↔ ∃ i < sz, key L[i]! = k)
    (hkey : key L[sz]! = k) (hn : sz < L.length) : mA.contains k = false := by
  rw [Bool.eq_false_iff]
  intro hcon
  obtain ⟨q, hq, hqk⟩ := (hmap k).1 hcon
  have hqL : q < L.length := by omega
  have e : key L[q] = key L[sz] := by
    rw [← getElem!_pos L q hqL, ← getElem!_pos L sz hn]
    exact hqk.trans hkey.symm
  exact absurd (hd q hqL sz hn e) (by omega)

private theorem ksBfs_inv_push {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {L : List α} {par gen : List Nat} {h j : Nat} {x : α} {s : α → α}
    {y : α} {p g : Nat} {nw0 : List α} {np0 ng0 : List Nat}
    {lA : Array α} {pA gA : Array Nat} {mA : Std.HashMap Nat Nat} {sz : Nat}
    (hI : ksBfsInv key L par gen lA pA gA mA sz) (e1 : L.drop sz = y :: nw0)
    (e2 : par.drop sz = p :: np0) (e3 : gen.drop sz = g :: ng0)
    (hy : y = s x) (hph : p = h) (hgj : g = j) (hkey : key L[sz]! = key (s x)) :
    ksBfsInv key L par gen (lA.push (s x)) (pA.push h) (gA.push j)
      (mA.insert (key (s x)) lA.size) (sz + 1) := by
  obtain ⟨hlA, hpA, hgA, hmap, hle, hpl, hgl⟩ := hI
  obtain ⟨hn, eL1, eL2⟩ := drop_eq_cons e1
  obtain ⟨hpL, eP1, eP2⟩ := drop_eq_cons e2
  obtain ⟨hgL, eG1, eG2⟩ := drop_eq_cons e3
  refine ⟨?_, ?_, ?_, ?_, by omega, hpl, hgl⟩
  · exact ksBfs_push_take hlA hn (eL1.trans hy)
  · exact ksBfs_push_take hpA (by omega) (eP1.trans hph)
  · exact ksBfs_push_take hgA (by omega) (eG1.trans hgj)
  · intro k
    rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hmap k]
    constructor
    · rintro (e | ⟨q, hq, hqk⟩)
      · exact ⟨sz, by omega, hkey.trans e⟩
      · exact ⟨q, by omega, hqk⟩
    · rintro ⟨q, hq, hqk⟩
      rcases Nat.lt_or_ge q sz with hq' | hq'
      · exact Or.inr ⟨q, hq', hqk⟩
      · have hqs : q = sz := by omega
        rw [hqs] at hqk
        exact Or.inl (hkey.symm.trans hqk)

private theorem ksBfs_step_new {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {L : List α} {par gen : List Nat} {pos : KTree (Nat × Nat)} {x : α} {h : Nat}
    {s : α → α} {ss : List (α → α)} {j sz : Nat} {nw0 : List α} {np0 ng0 : List Nat}
    {nw' : List α} {np' ng' : List Nat} {sz' : Nat} {y : α} {p g : Nat}
    {lA : Array α} {pA gA : Array Nat} {mA : Std.HashMap Nat Nat}
    (hI : ksBfsInv key L par gen lA pA gA mA sz)
    (e1 : L.drop sz = y :: nw0) (e2 : par.drop sz = p :: np0) (e3 : gen.drop sz = g :: ng0)
    (hy : y = s x) (hph : p = h) (hgj : g = j) (hkey : key L[sz]! = key (s x))
    (hcf : mA.contains (key (s x)) = false)
    (hr : replayStep key pos x h ss (j + 1) nw0 np0 ng0 (sz + 1) = some (nw', np', ng', sz')) :
    ∃ (sz₁ : Nat) (lA₁ : Array α) (pA₁ gA₁ : Array Nat) (mA₁ : Std.HashMap Nat Nat),
      ksBfsInner key x h s (lA, pA, gA, mA, j) = pure (.yield (lA₁, pA₁, gA₁, mA₁, j + 1)) ∧
      ksBfsInv key L par gen lA₁ pA₁ gA₁ mA₁ sz₁ ∧ sz ≤ sz₁ ∧
      replayStep key pos x h ss (j + 1) (L.drop sz₁) (par.drop sz₁) (gen.drop sz₁) sz₁ =
        some (nw', np', ng', sz') := by
  have hbody : ksBfsInner key x h s (lA, pA, gA, mA, j) =
      pure (.yield (lA.push (s x), pA.push h, gA.push j,
        mA.insert (key (s x)) lA.size, j + 1)) := by
    simp [ksBfsInner, hcf]
  refine ⟨sz + 1, lA.push (s x), pA.push h, gA.push j, mA.insert (key (s x)) lA.size, hbody,
    ksBfs_inv_push hI e1 e2 e3 hy hph hgj hkey, by omega, ?_⟩
  obtain ⟨hL, eL2, eL3⟩ := drop_eq_cons e1
  obtain ⟨hP, eP2, eP3⟩ := drop_eq_cons e2
  obtain ⟨hG, eG2, eG3⟩ := drop_eq_cons e3
  rw [← eL3, ← eP3, ← eG3] at hr
  exact hr

private theorem ksBfs_inner_step {α : Type} [Inhabited α] [DecidableEq α]
    {key : α → Nat} {L : List α} {par gen : List Nat} {pos : KTree (Nat × Nat)}
    (hpos : posOK key L pos = true)
    (hd : ∀ (i : Nat) (hi : i < L.length) (j : Nat) (hj : j < L.length),
      key L[i] = key L[j] → i = j)
    {x : α} {h : Nat} {s : α → α} {ss : List (α → α)} {j sz : Nat}
    {nw : List α} {np ng : List Nat} {nw' : List α} {np' ng' : List Nat} {sz' : Nat}
    {lA : Array α} {pA gA : Array Nat} {mA : Std.HashMap Nat Nat}
    (hr : replayStep key pos x h (s :: ss) j nw np ng sz = some (nw', np', ng', sz'))
    (e1 : nw = L.drop sz) (e2 : np = par.drop sz) (e3 : ng = gen.drop sz)
    (hI : ksBfsInv key L par gen lA pA gA mA sz) :
    ∃ (sz₁ : Nat) (lA₁ : Array α) (pA₁ gA₁ : Array Nat) (mA₁ : Std.HashMap Nat Nat),
      ksBfsInner key x h s (lA, pA, gA, mA, j) = pure (.yield (lA₁, pA₁, gA₁, mA₁, j + 1)) ∧
      ksBfsInv key L par gen lA₁ pA₁ gA₁ mA₁ sz₁ ∧ sz ≤ sz₁ ∧
      replayStep key pos x h ss (j + 1) (L.drop sz₁) (par.drop sz₁) (gen.drop sz₁) sz₁ =
        some (nw', np', ng', sz') := by
  obtain ⟨hlA, hpA, hgA, hmap, hle, hpl, hgl⟩ := hI
  simp only [replayStep] at hr
  split at hr
  · cases hr
  · rename_i i hf
    obtain ⟨hiL, hkey⟩ := (findK_eq_some key hpos (key (s x)) i).1 hf
    split at hr
    · rename_i hilt
      have hkey! : key L[i]! = key (s x) := by
        rw [getElem!_pos L i hiL]
        exact hkey
      have hcont : mA.contains (key (s x)) = true := (hmap (key (s x))).2 ⟨i, hilt, hkey!⟩
      have hbody : ksBfsInner key x h s (lA, pA, gA, mA, j) =
          pure (.yield (lA, pA, gA, mA, j + 1)) := by
        simp [ksBfsInner, hcont]
      rw [e1, e2, e3] at hr
      exact ⟨sz, lA, pA, gA, mA, hbody, ⟨hlA, hpA, hgA, hmap, hle, hpl, hgl⟩,
        Nat.le_refl _, hr⟩
    · split at hr
      · rename_i hieq
        have hkey! : key L[i]! = key (s x) := by
          rw [getElem!_pos L i hiL]
          exact hkey
        rw [hieq] at hkey!
        split at hr
        · rename_i y nw0 p0 np0 g0 ng0
          split at hr
          · rename_i hc
            obtain ⟨hy, hph, hgj⟩ := hc
            exact ksBfs_step_new ⟨hlA, hpA, hgA, hmap, hle, hpl, hgl⟩ e1.symm e2.symm e3.symm
              hy hph hgj hkey! (ksBfs_contains_false hd hmap hkey! (by omega)) hr
          · cases hr
        · cases hr
      · cases hr

private theorem ksBfs_inner {α : Type} [Inhabited α] [DecidableEq α]
    {key : α → Nat} {L : List α} {par gen : List Nat} {pos : KTree (Nat × Nat)}
    (hpos : posOK key L pos = true)
    (hd : ∀ (i : Nat) (hi : i < L.length) (j : Nat) (hj : j < L.length),
      key L[i] = key L[j] → i = j)
    (x : α) (h : Nat) :
    ∀ (ss : List (α → α)) (j sz : Nat) (nw' : List α) (np' ng' : List Nat) (sz' : Nat)
      (lA : Array α) (pA gA : Array Nat) (mA : Std.HashMap Nat Nat),
      replayStep key pos x h ss j (L.drop sz) (par.drop sz) (gen.drop sz) sz =
        some (nw', np', ng', sz') →
      ksBfsInv key L par gen lA pA gA mA sz →
      ∃ (lA' : Array α) (pA' gA' : Array Nat) (mA' : Std.HashMap Nat Nat),
        Id.run (forIn ss (lA, pA, gA, mA, j) (ksBfsInner key x h)) =
          (lA', pA', gA', mA', j + ss.length) ∧
        ksBfsInv key L par gen lA' pA' gA' mA' sz' ∧ sz ≤ sz' ∧
        nw' = L.drop sz' ∧ np' = par.drop sz' ∧ ng' = gen.drop sz'
  | [], j, sz, nw', np', ng', sz', lA, pA, gA, mA, hr, hI => by
    simp only [replayStep, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
    exact ⟨lA, pA, gA, mA, by simp, hI, by omega, rfl, rfl, rfl⟩
  | s :: ss, j, sz, nw', np', ng', sz', lA, pA, gA, mA, hr, hI => by
    obtain ⟨sz₁, lA₁, pA₁, gA₁, mA₁, hbody, hI₁, hle, hr'⟩ :=
      ksBfs_inner_step hpos hd hr rfl rfl rfl hI
    obtain ⟨lA', pA', gA', mA', heq, hI', hle', e1, e2, e3⟩ :=
      ksBfs_inner hpos hd x h ss (j + 1) sz₁ nw' np' ng' sz' lA₁ pA₁ gA₁ mA₁ hr' hI₁
    refine ⟨lA', pA', gA', mA', ?_, hI', by omega, e1, e2, e3⟩
    rw [List.forIn_cons, hbody]
    simp only [pure_bind, Id.run]
    have heq' : forIn ss (lA₁, pA₁, gA₁, mA₁, j + 1) (ksBfsInner key x h) =
        (lA', pA', gA', mA', (j + 1) + ss.length) := heq
    rw [heq']
    have hind : (j + 1) + ss.length = j + (s :: ss).length := by
      simp [List.length_cons]
      omega
    rw [hind]


private theorem ksBfs_outer_step {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {steps : List (α → α)} {L : List α} {par gen : List Nat} {pos : KTree (Nat × Nat)}
    (hpos : posOK key L pos = true)
    (hd : ∀ (i : Nat) (hi : i < L.length) (j : Nat) (hj : j < L.length),
      key L[i] = key L[j] → i = j)
    {f lo h sz : Nat} {hs nw : List α} {np ng : List Nat} {st : ksBfsS α}
    (hr : replayGo key steps pos (f + 1) hs h nw np ng sz = true)
    (e0 : hs = L.drop h) (e1 : nw = L.drop sz) (e2 : np = par.drop sz) (e3 : ng = gen.drop sz)
    (hlt : h < sz) (hst : st.2.2.2.2 = h)
    (hI : ksBfsInv key L par gen st.1 st.2.1 st.2.2.1 st.2.2.2.1 sz) :
    ∃ (sz' : Nat) (st' : ksBfsS α),
      ksBfsOuter key steps lo st = pure (.yield st') ∧
      ksBfsInv key L par gen st'.1 st'.2.1 st'.2.2.1 st'.2.2.2.1 sz' ∧
      h + 1 ≤ sz' ∧ st'.2.2.2.2 = h + 1 ∧
      replayGo key steps pos f (L.drop (h + 1)) (h + 1) (L.drop sz') (par.drop sz')
        (gen.drop sz') sz' = true := by
  simp only [replayGo] at hr
  rw [if_pos hlt] at hr
  split at hr
  · cases hr
  · rename_i x hs'
    split at hr
    · cases hr
    · rename_i nw' np' ng' sz' hstep
      obtain ⟨hn, eL1, eL2⟩ := drop_eq_cons e0.symm
      have hsize : st.1.size = sz := by
        rw [hI.1, List.size_toArray, List.length_take, Nat.min_eq_left hI.2.2.2.2.1]
      have hx : st.1[h]! = x := by
        rw [hI.1, ksBfs_take_getElem! hlt, getElem!_pos L h hn, eL1]
      rw [e1, e2, e3] at hstep
      obtain ⟨lA', pA', gA', mA', hin, hI', hle', e1', e2', e3'⟩ :=
        ksBfs_inner hpos hd x h steps 0 sz nw' np' ng' sz' st.1 st.2.1 st.2.2.1
          st.2.2.2.1 hstep hI
      have hbody : ksBfsOuter key steps lo st = pure (.yield (lA', pA', gA', mA', h + 1)) := by
        unfold ksBfsOuter
        rw [if_pos (by rw [hsize, hst]; exact hlt)]
        simp only [hst, hx]
        have hin' : forIn steps (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0)
            (ksBfsInner key x h) = (lA', pA', gA', mA', 0 + steps.length) := hin
        rw [hin']
        rfl
      rw [← eL2, e1', e2', e3'] at hr
      exact ⟨sz', (lA', pA', gA', mA', h + 1), hbody, hI', by omega, rfl, hr⟩

private theorem ksBfs_outer_done {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {steps : List (α → α)} {L : List α} {par gen : List Nat} {pos : KTree (Nat × Nat)}
    {f lo h sz : Nat} {hs nw : List α} {np ng : List Nat} {st : ksBfsS α}
    (hr : replayGo key steps pos (f + 1) hs h nw np ng sz = true) (hge : ¬ h < sz)
    (e1 : nw = L.drop sz) (hst : st.2.2.2.2 = h)
    (hI : ksBfsInv key L par gen st.1 st.2.1 st.2.2.1 st.2.2.2.1 sz) :
    ∃ st', ksBfsOuter key steps lo st = pure (.done st') ∧
      st'.1 = L.toArray ∧ st'.2.1 = par.toArray ∧ st'.2.2.1 = gen.toArray := by
  simp only [replayGo] at hr
  rw [if_neg hge] at hr
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hr
  obtain ⟨⟨n1, n2⟩, n3⟩ := hr
  have m1 : L.length ≤ sz := List.drop_eq_nil_iff.1 (by rw [← e1]; exact n1)
  have hle : sz ≤ L.length := hI.2.2.2.2.1
  have hsz : sz = L.length := by omega
  have hsize : st.1.size = sz := by
    rw [hI.1, List.size_toArray, List.length_take, Nat.min_eq_left hle]
  have hns : ¬ st.2.2.2.2 < st.1.size := by rw [hsize, hst]; exact hge
  have hbody : ksBfsOuter key steps lo st = pure (.done st) := by
    simp [ksBfsOuter, hns]
  exact ⟨st, hbody, by rw [hI.1, hsz, List.take_length],
    by rw [hI.2.1, hsz, ← hI.2.2.2.2.2.1, List.take_length],
    by rw [hI.2.2.1, hsz, ← hI.2.2.2.2.2.2, List.take_length]⟩

private theorem ksBfs_go {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {steps : List (α → α)} {L : List α} {par gen : List Nat} {pos : KTree (Nat × Nat)}
    (hpos : posOK key L pos = true)
    (hd : ∀ (i : Nat) (hi : i < L.length) (j : Nat) (hj : j < L.length),
      key L[i] = key L[j] → i = j)
    (f : Nat) :
    ∀ (lo h sz : Nat) (hs nw : List α) (np ng : List Nat) (st : ksBfsS α),
      replayGo key steps pos f hs h nw np ng sz = true →
      hs = L.drop h → nw = L.drop sz → np = par.drop sz → ng = gen.drop sz →
      h ≤ sz → st.2.2.2.2 = h →
      ksBfsInv key L par gen st.1 st.2.1 st.2.2.1 st.2.2.2.1 sz →
      ∃ st', Id.run (forIn (List.range' lo f) st (ksBfsOuter key steps)) = st' ∧
        st'.1 = L.toArray ∧ st'.2.1 = par.toArray ∧ st'.2.2.1 = gen.toArray := by
  induction f with
  | zero =>
    intro lo h sz hs nw np ng st hr e0 e1 e2 e3 hh hst hI
    obtain ⟨hlA, hpA, hgA, hmap, hle, hpl, hgl⟩ := hI
    simp only [replayGo, Bool.and_eq_true, List.isEmpty_iff] at hr
    obtain ⟨⟨n1, n2⟩, n3⟩ := hr
    have m1 : L.length ≤ sz := List.drop_eq_nil_iff.1 (by rw [← e1]; exact n1)
    have hsz : sz = L.length := by omega
    refine ⟨st, ?_, ?_, ?_, ?_⟩
    · simp [List.range'_zero]
    · rw [hlA, hsz, List.take_length]
    · rw [hpA, hsz, ← hpl, List.take_length]
    · rw [hgA, hsz, ← hgl, List.take_length]
  | succ f ih =>
    intro lo h sz hs nw np ng st hr e0 e1 e2 e3 hh hst hI
    rw [List.range'_succ, List.forIn_cons]
    by_cases hlt : h < sz
    · obtain ⟨sz', st', hbody, hI', hh', hst', hr'⟩ :=
        ksBfs_outer_step hpos hd hr e0 e1 e2 e3 hlt hst hI
      have hrec := ih (lo + 1) (h + 1) sz' (L.drop (h + 1)) (L.drop sz') (par.drop sz')
        (gen.drop sz') st' hr' rfl rfl rfl rfl hh' hst' hI'
      rw [hbody]
      simp only [pure_bind, Id.run]
      exact hrec
    · obtain ⟨st', hbody, h1, h2, h3⟩ := ksBfs_outer_done hr hlt e1 hst hI
      exact ⟨st', by rw [hbody]; simp, h1, h2, h3⟩

theorem bfs_eq_of_replayOK {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {steps : List (α → α)} {base : α} {fuel : Nat} {L : List α} {par gen : List Nat}
    {pos : KTree (Nat × Nat)} (h : replayOK key steps base fuel L par gen pos = true) :
    Native.bfs key steps base fuel = (L.toArray, par.toArray, gen.toArray) := by
  obtain ⟨hpos, -, hpl, hgl, -, -⟩ := replay_facts h
  unfold replayOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i x nw p np g ng
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hxb, hp0⟩, hg0⟩, hgo⟩ := h
    subst x
    subst p
    subst g
    have hd : ∀ (i : Nat) (hi : i < (base :: nw).length) (j : Nat)
        (hj : j < (base :: nw).length), key (base :: nw)[i] = key (base :: nw)[j] → i = j :=
      fun i hi j hj e => posOK_inj hpos hi hj e
    have hI : ksBfsInv key (base :: nw) (0 :: np) (0 :: ng)
        (ksBfsInit key base).1 (ksBfsInit key base).2.1 (ksBfsInit key base).2.2.1
        (ksBfsInit key base).2.2.2.1 1 := by
      refine ⟨by simp [ksBfsInit], by simp [ksBfsInit], by simp [ksBfsInit], ?_,
        by simp, hpl, hgl⟩
      intro k
      simp only [ksBfsInit]
      rw [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, beq_iff_eq]
      constructor
      · intro e
        exact ⟨0, by omega, by simp [e]⟩
      · rintro ⟨i, hi, hik⟩
        have hi0 : i = 0 := by omega
        subst hi0
        simpa using hik
    obtain ⟨st', heq, h1, h2, h3⟩ :=
      ksBfs_go hpos hd fuel 0 0 1 (base :: nw) nw np ng (ksBfsInit key base) hgo rfl rfl rfl rfl
        (by omega) rfl hI
    rw [ksBfs_eq, heq]
    simp only [h1, h2, h3]
  · cases h

end CFSG.KC.M24G
