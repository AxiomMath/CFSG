module

public import Certificates.Data.Kernel.HSA312.Defs
public import CFSG.Certificates.Kernel.LocalQTPcOmSound
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
public import CFSG.Quasithin.Background.A312SporShapesCheck
public import CFSG.Quasithin.Background.A312SporE8Check
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.KC.HSA312

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.PcW CFSG.KC.LQT.PcOm
open CFSG.QuasithinUnique.K1.SporadicPerm (img applyTab ptsOf keyNat BaseEnumOK compArr)
open CFSG.QuasithinUnique.Ch1.SporLat (idTab powTab wordTabA ptAct sortN LatData GensIn)

variable {n w : Nat}

@[expose] def RepL (n w : Nat) (cs : List Nat) (ts : List (Array Nat)) : Prop :=
  cs.length = ts.length ∧ ∀ j < cs.length, Rep n w (cs.getD j 0) (ts.getD j #[])

theorem RepL.cons {c : Nat} {t : Array Nat} {cs : List Nat} {ts : List (Array Nat)}
    (hc : Rep n w c t) (h : RepL n w cs ts) : RepL n w (c :: cs) (t :: ts) := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  cases j with
  | zero => exact hc
  | succ j => exact h.2 j (by simpa using hj)

theorem RepL.tail {c : Nat} {t : Array Nat} {cs : List Nat} {ts : List (Array Nat)}
    (h : RepL n w (c :: cs) (t :: ts)) : Rep n w c t ∧ RepL n w cs ts := by
  refine ⟨h.2 0 (by simp), ⟨by simpa using h.1, fun j hj => h.2 (j + 1) (by simpa using hj)⟩⟩

theorem RepL.of_get {cs : List Nat} {ts : List (Array Nat)} (hlen : cs.length = ts.length)
    (h : ∀ j < ts.length, Rep n w (cs.getD j 0) ts[j]!) : RepL n w cs ts := by
  refine ⟨hlen, fun j hj => ?_⟩
  have hj' : j < ts.length := by rw [← hlen]; exact hj
  rw [List.getD_eq_getElem ts #[] hj', ← getElem!_pos ts j hj']
  exact h j hj'

theorem RepL.mem {cs : List Nat} {ts : List (Array Nat)} (h : RepL n w cs ts) {c : Nat}
    (hc : c ∈ cs) : ∃ t ∈ ts, Rep n w c t := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
  have hj' : j < ts.length := by rw [← h.1]; exact hj
  refine ⟨ts[j], List.getElem_mem hj', ?_⟩
  have := h.2 j hj
  rwa [List.getD_eq_getElem cs 0 hj, List.getD_eq_getElem ts #[] hj'] at this

theorem RepL.mem' {cs : List Nat} {ts : List (Array Nat)} (h : RepL n w cs ts) {t : Array Nat}
    (ht : t ∈ ts) : ∃ c ∈ cs, Rep n w c t := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ht
  have hj' : j < cs.length := by rw [h.1]; exact hj
  refine ⟨cs[j], List.getElem_mem hj', ?_⟩
  have := h.2 j hj'
  rwa [List.getD_eq_getElem cs 0 hj', List.getD_eq_getElem ts #[] hj] at this

theorem RepL.get {cs : List Nat} {ts : List (Array Nat)} (h : RepL n w cs ts) {j : Nat}
    (hj : j < ts.length) : Rep n w (cs.getD j 0) ts[j]! := by
  have hj' : j < cs.length := by rw [h.1]; exact hj
  have := h.2 j hj'
  rwa [List.getD_eq_getElem ts #[] hj, ← getElem!_pos ts j hj] at this

theorem img_rep {c : Nat} {t : Array Nat} (h : Rep n w c t) {p : Nat} (hp : p < n) :
    img t p = pg w (mask w) c p := by
  rw [← rep_get h p hp, Array.getElem!_eq_getD]
  rfl

theorem applyTab_rep {c : Nat} {t : Array Nat} (h : Rep n w c t) {T : List Nat}
    (hT : ∀ x ∈ T, x < n) : applyTab t T = appC w (mask w) c T := by
  unfold applyTab appC
  exact List.map_congr_left fun x hx => img_rep h (hT x hx)

theorem ptsOf_rep {B : List Nat} (hB : ∀ b ∈ B, b < n) :
    ∀ {cs : List Nat} {ts : List (Array Nat)}, RepL n w cs ts → ptsOf B ts = ptsC w (mask w) B cs
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h.1 (by simp)
  | _ :: _, [], h => absurd h.1 (by simp)
  | c :: cs, t :: ts, h => by
    obtain ⟨h0, h'⟩ := h.tail
    have e := ptsOf_rep hB h'
    unfold ptsOf ptsC at e ⊢
    simp only [List.flatMap_cons, List.append_cancel_left_eq] at e ⊢
    rw [e, List.map_congr_left fun b hb => img_rep h0 (hB b hb)]

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem rep_wordTab (hn : n < 2 ^ 32) (hw : 0 < w) {idn : Nat} (hid : Rep n w idn (idTab n))
    {Lc : Nat → Nat} {tabs : Array (Array Nat)} {v : List Nat}
    (hv : ∀ l ∈ v, Rep n w (Lc l) (tabs.getD l #[])) {c : Nat}
    (h : Nat.beq (wordPB n w (mask w) Lc v idn) c = true) : Rep n w c (wordTabA tabs n v) := by
  rw [wordTabA_foldr, ← Nat.eq_of_beq_eq_true h]
  exact rep_word hn hw hid v hv

theorem rep_letters {Lc : Nat → Nat} {L : List (Array Nat)}
    (hL : ∀ l < L.length, Rep n w (Lc l) L[l]!) {v : List Nat} (hv : ∀ l ∈ v, l < L.length) :
    ∀ l ∈ v, Rep n w (Lc l) (L.toArray.getD l #[]) :=
  fun l hl => by
    rw [getD_toArray (hv l hl)]
    exact hL l (hv l hl)

theorem repL_words (hn : n < 2 ^ 32) (hw : 0 < w) {idn : Nat} (hid : Rep n w idn (idTab n))
    {Lc : Nat → Nat} {L : List (Array Nat)} (hL : ∀ l < L.length, Rep n w (Lc l) L[l]!)
    {ws : List (List Nat)} (hws : ∀ v ∈ ws, ∀ l ∈ v, l < L.length) {cs : List Nat}
    (hlen : cs.length = ws.length)
    (h : (List.range ws.length).all (fun i =>
      Nat.beq (wordPB n w (mask w) Lc (ws.getD i []) idn) (cs.getD i 0)) = true) :
    RepL n w cs (ws.map (wordTabA L.toArray n)) := by
  refine ⟨by simp [hlen], fun j hj => ?_⟩
  have hj' : j < ws.length := by omega
  have hjm : j < (ws.map (wordTabA L.toArray n)).length := by simpa using hj'
  have e := List.all_eq_true.1 h j (List.mem_range.2 hj')
  rw [List.getD_eq_getElem ws [] hj'] at e
  rw [List.getD_eq_getElem _ #[] hjm, List.getElem_map]
  exact rep_wordTab hn hw hid (rep_letters hL (hws _ (List.getElem_mem hj'))) e

theorem RepL.pow (hn : n < 2 ^ 32) (hw : 0 < w) {idn : Nat} (hid : Rep n w idn (idTab n))
    {cs ds : List Nat} {ts : List (Array Nat)} (h : RepL n w cs ts) (k : Nat)
    (hlen : ds.length = cs.length)
    (he : (List.range cs.length).all (fun i =>
      Nat.beq (powS n w (mask w) idn (cs.getD i 0) k) (ds.getD i 0)) = true) :
    RepL n w ds (ts.map fun t => powTab n t k) := by
  refine ⟨by simp [hlen, h.1], fun j hj => ?_⟩
  have hj' : j < cs.length := by omega
  have hj'' : j < ts.length := by rw [← h.1]; exact hj'
  have hjm : j < (ts.map fun t => powTab n t k).length := by simpa using hj''
  have e := Nat.eq_of_beq_eq_true (List.all_eq_true.1 he j (List.mem_range.2 hj'))
  rw [← e, List.getD_eq_getElem _ #[] hjm, List.getElem_map]
  have := rep_pow hn hw hid (h.2 j hj') k
  rwa [List.getD_eq_getElem ts #[] hj''] at this

theorem comp_eq (hn : n < 2 ^ 32) (hw : 0 < w) {a b c d : Nat} {A B C D : Array Nat}
    (ha : Rep n w a A) (hb : Rep n w b B) (hc : Rep n w c C) (hd : Rep n w d D)
    (h : (pcS n w (mask w) a b == pcS n w (mask w) c d) = true) : compArr A B = compArr C D :=
  rep_eq (rep_comp hn hw ha hb) (rep_comp hn hw hc hd) (eq_of_beq h)

theorem baseEnum_sound {B cs ci : List Nat} {G Gi : List (Array Nat)} (hG : RepL n w cs G)
    (hGi : RepL n w ci Gi) {Ts : Array (List Nat)} {par cl : Array Nat}
    (h : baseEnumC n w (mask w) B cs ci Ts par cl = true) :
    BaseEnumOK n B G Gi Ts par cl ∧ ∀ T ∈ Ts.toList, ∀ x ∈ T, x < n := by
  unfold baseEnumC at h
  simp only [Bool.and_eq_true, beq_iff_eq, blt_iff, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.any_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, hlt, h3, h4, h5, h6⟩ := h
  have hl1 : G.length = cs.length := hG.1.symm
  have hl2 : Gi.length = ci.length := hGi.1.symm
  have hent : ∀ i < Ts.size, ∀ x ∈ Ts[i]!, x < n := fun i hi x hx => by
    rw [getElem!_pos Ts i hi] at hx
    exact hlt _ (Array.getElem_mem_toList hi) x hx
  have hB : ∀ b ∈ B, b < n := by
    intro b hb
    have := hent 0 h0 b
    rw [h1] at this
    exact this (List.mem_append_left _ hb)
  refine ⟨⟨h0, by rw [ptsOf_rep hB hG]; exact h1, h2, fun i hi hi0 => ?_, (distF_spec h4).1,
    fun i hi j hj => ?_, fun i hi j hj => ?_⟩, hlt⟩
  · rcases h3 i hi with h | ⟨hp, c, hc, he⟩
    · exact absurd h (by omega)
    · obtain ⟨s, hs, hr⟩ := hG.mem hc
      exact ⟨hp, s, hs, by rw [applyTab_rep hr (hent _ (by omega))]; exact he⟩
  · rw [hl1, hl2]
    rw [hl1] at hj
    obtain ⟨a, b⟩ := h5 i hi j hj
    refine ⟨a, ?_⟩
    rw [applyTab_rep (hG.get (by rw [hl1]; exact hj)) (hent i hi)]
    exact b
  · rw [hl1, hl2]
    rw [hl2] at hj
    obtain ⟨a, b⟩ := h6 i hi j hj
    refine ⟨a, ?_⟩
    rw [applyTab_rep (hGi.get (by rw [hl2]; exact hj)) (hent i hi)]
    exact b

theorem extra_sound (hn0 : 0 < n) {B es : List Nat} {E : List (Array Nat)} {z : Nat}
    {zt : Array Nat} (hE : RepL n w es E) (hz : Rep n w z zt) {Ts : Array (List Nat)}
    (hT : ∀ T ∈ Ts.toList, ∀ x ∈ T, x < n) (h0 : ptsOf B E ∈ Ts.toList)
    (h : extraC w (mask w) B es z Ts = true) :
    ∀ T ∈ Ts.toList, (∀ t < E.length, ∀ j < B.length,
      T.getD (B.length * (1 + t) + j) 0 = img (E.getD t #[]) (T.getD j 0)) →
      T = ptsOf B E ∨ T = applyTab zt (ptsOf B E) := by
  intro T hTm hc
  have hP := hT _ h0
  have hB : ∀ b ∈ B, b < n := fun b hb => hP b (by unfold ptsOf; exact List.mem_append_left _ hb)
  unfold extraC at h
  have hT' := List.all_eq_true.1 h T hTm
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hT'
  rw [applyTab_rep hz hP, ptsOf_rep hB hE]
  rcases hT' with (hT' | hT') | hT'
  · exfalso
    have hg : ∀ j, T.getD j 0 < n := fun j => by
      rw [List.getD_eq_getElem?_getD]
      cases hj : T[j]? with
      | none => exact hn0
      | some x => exact hT T hTm x (List.mem_of_getElem? hj)
    have : ((List.range es.length).all fun t => (List.range B.length).all fun j =>
        T.getD (B.length * (1 + t) + j) 0 == pg w (mask w) (es.getD t 0) (T.getD j 0)) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
      intro t ht j hj
      have htE : t < E.length := by rw [← hE.1]; exact ht
      have r := hE.2 t ht
      have := hc t htE j hj
      rwa [img_rep r (hg j)] at this
    rw [this] at hT'
    exact Bool.false_ne_true hT'.symm
  · exact Or.inl hT'
  · exact Or.inr hT'

theorem beq_rep (hw : 0 < w) {c d : Nat} {s t : Array Nat} (hc : Rep n w c s) (hd : Rep n w d t) :
    (s == t) = (c == d) := by
  by_cases e : c = d
  · rw [e, beq_self_eq_true, rep_eq hc hd e, beq_self_eq_true]
  · rw [beq_eq_false_iff_ne.2 e, beq_eq_false_iff_ne.2 (rep_ne hw hc hd e)]

theorem RepL.getA {cs : List Nat} {ts : Array (Array Nat)} (h : RepL n w cs ts.toList) {j : Nat}
    (hj : j < cs.length) : Rep n w (cs.getD j 0) (ts.getD j #[]) := by
  have := h.2 j hj
  have e : ts.toList.getD j #[] = ts.getD j #[] := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rwa [e] at this

theorem e8VPow_rep {vc : List Nat} {vt : Array (Array Nat)} {idn : Nat}
    (hid : Rep n w idn (idTab n)) (hv : RepL n w vc vt.toList) {b i : Nat}
    (hi : i < vc.length) :
    Rep n w (e8VPowC vc idn b i) (CFSG.Quasithin.A312S.e8VPow vt n b i) := by
  unfold e8VPowC CFSG.Quasithin.A312S.e8VPow
  by_cases hb : b = 1
  · subst hb
    exact hv.getA hi
  · have hb' : (b == 1) = false := beq_eq_false_iff_ne.2 hb
    rw [hb', if_neg hb]
    exact hid

theorem e8BTab_rep (hn : n < 2 ^ 32) (hw : 0 < w) {vc : List Nat} {vt : Array (Array Nat)}
    {idn : Nat} (hid : Rep n w idn (idTab n)) (hv : RepL n w vc vt.toList) (h3 : vc.length = 3)
    (c : List Nat) :
    Rep n w (e8BTabC n w (mask w) idn vc c) (CFSG.Quasithin.A312S.e8BTab vt n c) :=
  rep_comp hn hw (rep_comp hn hw (e8VPow_rep hid hv (by omega)) (e8VPow_rep hid hv (by omega)))
    (e8VPow_rep hid hv (by omega))

theorem e8_sound (hn : n < 2 ^ 32) (hw : 0 < w) {vc lc : List Nat} {vt letters : Array (Array Nat)}
    {idn : Nat} (hid : Rep n w idn (idTab n)) (hv : RepL n w vc vt.toList) (h3 : vc.length = 3)
    (hl : RepL n w lc letters.toList) {mats : List (List (List Nat))}
    (h : e8C n w (mask w) idn vc lc mats = true) :
    CFSG.Quasithin.A312S.e8Check n vt letters mats = true := by
  have hvi : ∀ i < 3, Rep n w (vc.getD i 0) (vt.getD i #[]) := fun i hi => hv.getA (by omega)
  have hsz : lc.length = letters.size := by rw [hl.1]; simp
  have hli : ∀ l < letters.size, Rep n w (lc.getD l 0) (letters.getD l #[]) := fun l hl' =>
    hl.getA (by rw [hsz]; exact hl')
  have hrange : Array.range n = idTab n := rfl
  unfold e8C at h
  unfold CFSG.Quasithin.A312S.e8Check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, and_assoc] at h ⊢
  obtain ⟨ha, hb, hc, hd⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_, fun c hc' => ?_, fun l hl' i hi => ?_⟩
  · rw [hrange, beq_rep hw (rep_comp hn hw (hvi i hi) (hvi i hi)) hid]
    exact ha i hi
  · rw [beq_rep hw (rep_comp hn hw (hvi i hi) (hvi j hj)) (rep_comp hn hw (hvi j hj) (hvi i hi))]
    exact hb i hi j hj
  · have := hc c hc'
    rw [hrange]
    simp only [bne, beq_rep hw (e8BTab_rep hn hw hid hv h3 c) hid]
    exact this
  · rw [beq_rep hw (rep_comp hn hw (hli l hl') (hvi i hi))
      (rep_comp hn hw (e8BTab_rep hn hw hid hv h3 _) (hli l hl'))]
    exact hd l (by rw [hsz]; exact hl') i hi

theorem ptAct_rep {c : Nat} {t : Array Nat} (h : Rep n w c t) {Δ : List Nat}
    (hΔ : ∀ p ∈ Δ, p < n) : ptAct t Δ = srtB (Δ.map (pg w (mask w) c)) := by
  unfold ptAct
  rw [sortN_eq_srtB]
  congr 1
  exact List.map_congr_left fun p hp => img_rep h (hΔ p hp)

theorem gensIn_iff {idn : Nat} {L : Nat → Nat} {ws : List (List Nat)} {tf : List Nat → Array Nat}
    (hr : ∀ v ∈ ws, Rep n w (wordPB n w (mask w) L v idn) (tf v)) {D : LatData (List Nat)}
    {Δ : List Nat} (hΔ : ∀ p ∈ Δ, p < n) {j jj : Nat} (hm : D.mt[j]! = ws.map tf) :
    GensIn ptAct Δ D j jj ↔ gensInC n w (mask w) idn L ws Δ D.Om[jj]!.lbl.toList = true := by
  unfold GensIn gensInC
  rw [hm, List.all_eq_true]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    List.contains_iff_mem]
  refine forall₂_congr fun v hv => ?_
  rw [ptAct_rep (hr v hv) hΔ]
  have e : labC n w (mask w) idn L Δ v = srtB (Δ.map (pg w (mask w) (wordPB n w (mask w) L v idn))) :=
    rfl
  rw [e]
  constructor
  · rintro ⟨x, hx, e⟩
    rw [← e, getElem!_pos _ x hx]
    exact Array.getElem_mem_toList hx
  · intro hmem
    obtain ⟨x, hx, e⟩ := List.mem_iff_getElem.1 hmem
    have hx' : x < D.Om[jj]!.lbl.size := by simpa using hx
    refine ⟨x, hx', ?_⟩
    rw [getElem!_pos _ x hx', ← e]
    simp

section Expl

open CFSG.Quasithin.A312Hs (ExplOK ExplOK' explTabs)

theorem explTabs_get {L : List (Array Nat)} {N : Nat} {word : Nat → List Nat} {i : Nat}
    (hi : i < N) : (explTabs n L N word)[i]! = wordTabA L.toArray n (word i) := by
  unfold explTabs
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem getElem!_getD {l : List Nat} {i : Nat} (hi : i < l.length) : l[i]! = l.getD i 0 := by
  rw [getElem!_pos l i hi, List.getD_eq_getElem l 0 hi]

theorem explOK_of (hn : n < 2 ^ 32) (hw : 0 < w) {idn nl N : Nat} {Lc : Nat → Nat}
    {L : List (Array Nat)} (hid : Rep n w idn (idTab n)) (hlen : L.length = nl)
    (hL : ∀ l < nl, Rep n w (Lc l) L[l]!) {word : Nat → List Nat} {mulf : Nat → Nat → Nat}
    {conj : List (List Nat)} {TC : Nat → Nat} (hW : explW nl N word = true)
    (hC : ∀ i < N, explCode n w (mask w) idn Lc word TC i = true)
    (hD : explDist N TC = true) (hM : ∀ i < N, explMul n w (mask w) N mulf TC i = true)
    (hJ : explConj n w (mask w) nl N Lc conj TC = true) : ExplOK n L N word mulf conj := by
  unfold explW at hW
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, blt_iff] at hW
  obtain ⟨hW0, hWl⟩ := hW
  have hT : ∀ i < N, Rep n w (TC i) (explTabs n L N word)[i]! := by
    intro i hi
    rw [explTabs_get hi]
    refine rep_wordTab hn hw hid (fun l hl => ?_) (hC i hi)
    have hl' := hWl i hi l hl
    rw [getD_toArray (by rw [hlen]; exact hl')]
    exact hL l hl'
  have hnd := (distF_spec hD).1
  unfold explConj at hJ
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, blt_iff] at hJ
  obtain ⟨hJ1, hJ2⟩ := hJ
  unfold ExplOK ExplOK'
  refine ⟨hW0, fun i hi l hl => by rw [hlen]; exact hWl i hi l hl, fun i hi k hk hik => ?_,
    fun i hi k hk => ?_, by rw [hJ1, hlen], fun l hl => ?_⟩
  · refine rep_ne hw (hT i hi) (hT k hk) fun e => hik ?_
    have h1 : ((List.range N).map TC)[i]'(by simpa using hi) =
        ((List.range N).map TC)[k]'(by simpa using hk) := by simpa using e
    exact (hnd.getElem_inj_iff).1 h1
  · have hm := hM i hi
    unfold explMul at hm
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, blt_iff] at hm
    obtain ⟨h1, h2⟩ := hm k hk
    exact ⟨h1, rep_eq (rep_comp hn hw (hT i hi) (hT k hk)) (hT _ h1) (Nat.eq_of_beq_eq_true h2)⟩
  · rw [hlen] at hl
    obtain ⟨h1, h2⟩ := hJ2 l hl
    have hcl : conj[l]! = conj.getD l [] := by
      rw [getElem!_pos conj l (by rw [hJ1]; exact hl), List.getD_eq_getElem conj [] (by rw [hJ1]; exact hl)]
    rw [hcl]
    refine ⟨h1, fun i hi => ?_⟩
    obtain ⟨h3, h4⟩ := h2 i hi
    rw [getElem!_getD (by rw [h1]; exact hi)]
    exact ⟨h3, rep_eq (rep_comp hn hw (hL l hl) (hT i hi)) (rep_comp hn hw (hT _ h3) (hL l hl))
      (Nat.eq_of_beq_eq_true h4)⟩

end Expl

end CFSG.KC.HSA312

end
