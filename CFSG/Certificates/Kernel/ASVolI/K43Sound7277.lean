module

public import Certificates.Data.Kernel.ASVolI.K43K7277
public import CFSG.Certificates.Kernel.ASVolI.K43Sound
public import CFSG.Certificates.Kernel.HMathieu.TabSound

public section

namespace CFSG.KS.ASVolI

open CFSG.ASVolI.K43Data CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.KS.MathieuAut
  CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem k43Img_eq (p : ℕ) : (unpk p).toList = k43Img p := by
  simp [unpk, k43Img]

theorem actC11_unpk (p m : ℕ) : actC11 (unpk p) m = actM (colsC11 (k43Img p)) m := by
  rw [actC11_eq_cols (size_unpk p), k43Img_eq]

theorem fixesOct_unpk (p : ℕ) : fixesOct (unpk p) = fixesOctP p := by
  have h : ∀ i ∈ octPts, i < 24 := by decide
  unfold fixesOct fixesOctP
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine ⟨fun H i hi => ?_, fun H i hi => ?_⟩
  · rw [← unpk_get p (h i hi)]
    exact H i hi
  · rw [unpk_get p (h i hi)]
    exact H i hi

theorem arrMul_unpk (p : ℕ) {q : ℕ} (hq : vpK q = true) :
    arrMul (unpk p) (unpk q) = unpk (pc24 p q) := by
  apply Array.ext (by simp [arrMul, size_unpk])
  intro i h1 h2
  have hi : i < 24 := by simpa [size_unpk] using h2
  rw [← getElem!_pos (unpk (pc24 p q)) i h2, unpk_get _ hi, pg_pc24 p q hi]
  simp only [arrMul, Array.getElem_ofFn]
  rw [unpk_get q hi, unpk_get p ((vpK_spec hq).2 i hi)]

theorem unpk_beq {p q : ℕ} (hp : vpK p = true) (hq : vpK q = true) :
    (unpk p == unpk q) = (p == q) := by
  by_cases h : p = q
  · subst h
    simp
  · have : unpk p ≠ unpk q := fun e => h (unpk_inj hp hq e)
    simp [h, this]

theorem k43_findIdx?_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.findIdx? p = l.findIdx? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.findIdx?_cons, List.findIdx?_cons, h a List.mem_cons_self,
      k43_findIdx?_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

variable [Fact (T24s2.check = true)] {E : List ℕ}

theorem vp_getD (H : Packed T24s2 E) {p : ℕ} (hp : p < E.length) : vpK (E.getD p 0) = true := by
  rw [List.getD_eq_getElem _ _ hp]
  exact H.vp _ (List.getElem_mem hp)

theorem tArr_eq (H : Packed T24s2 E) {p : ℕ} (hp : p < E.length) : tArr p = unpk (E.getD p 0) := by
  unfold tArr
  exact elems_get H hp

theorem kIdx_eq (H : Packed T24s2 E) : kIdx () = kIdxK E := by
  unfold kIdx kIdxK
  rw [n_eq H]
  refine List.filter_congr fun p hp => ?_
  rw [tArr_eq H (List.mem_range.1 hp), fixesOct_unpk]

theorem dzIdx_eq (H : Packed T24s2 E) : dzIdx () = dzIdxK E := by
  simp only [dzIdx, dzIdxK, centP]
  rw [n_eq H]
  refine List.filter_congr fun p hp => ?_
  rw [tArr_eq H (List.mem_range.1 hp)]
  simp only [actC11_unpk]

theorem z0Idx_eq (H : Packed T24s2 E) (hz : unpk z0P = z0Arr) (hvz : vpK z0P = true) :
    z0Idx = z0IdxK E := by
  unfold z0Idx z0IdxK
  rw [H.elems, List.findIdx?_toArray, List.findIdx?_map]
  congr 1
  refine k43_findIdx?_congr fun e he => ?_
  simp only [Function.comp_apply, ← hz]
  exact unpk_beq (H.vp e he) hvz

theorem lt_of_mem_filter_range {f : ℕ → Bool} {n p : ℕ} (h : p ∈ (List.range n).filter f) :
    p < n :=
  List.mem_range.1 (List.mem_filter.1 h).1

theorem getD_mem {p : ℕ} (hp : p < E.length) : E.getD p 0 ∈ E := by
  rw [List.getD_eq_getElem _ _ hp]
  exact List.getElem_mem hp

theorem map_getD_range (E : List ℕ) : (List.range E.length).map (fun p => E.getD p 0) = E := by
  apply List.ext_getElem (by simp)
  intro i _ h2
  simp [List.getElem?_eq_getElem h2]

theorem map_filter_range (f : ℕ → Bool) (E : List ℕ) :
    ((List.range E.length).filter fun p => f (E.getD p 0)).map (fun p => E.getD p 0) =
      E.filter f := by
  conv_rhs => rw [← map_getD_range E]
  rw [List.filter_map]
  rfl

theorem getD_mem_filter {f : ℕ → Bool} {p : ℕ}
    (h : p ∈ (List.range E.length).filter fun p => f (E.getD p 0)) : E.getD p 0 ∈ E.filter f := by
  rw [← map_filter_range]
  exact List.mem_map_of_mem h

theorem length_filter_range (f : ℕ → Bool) (E : List ℕ) :
    ((List.range E.length).filter fun p => f (E.getD p 0)).length = (E.filter f).length := by
  rw [← map_filter_range f E, List.length_map]

theorem mulIdx_comm (H : Packed T24s2 E) {p q : ℕ} (hp : p < E.length) (hq : q < E.length)
    (h : pc24 (E.getD p 0) (E.getD q 0) = pc24 (E.getD q 0) (E.getD p 0)) :
    T24s2.mulIdx p q = T24s2.mulIdx q p := by
  have hp' : p < T24s2.n := by rw [n_eq H]; exact hp
  have hq' : q < T24s2.n := by rw [n_eq H]; exact hq
  have e : (⟨p, hp'⟩ * ⟨q, hq'⟩ : T24s2.Elem) = ⟨q, hq'⟩ * ⟨p, hp'⟩ :=
    eq_of_pk H (by rw [pk_mul H, pk_mul H]; exact h)
  exact congrArg PT.Elem.idx e

theorem listsOK_of_K (H : Packed T24s2 E) (hid : E.getD 0 0 = pidn 24 5) (hs : listsS = true)
    (h : listsK E = true) : listsOK () = true := by
  unfold listsS at hs
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨hvz, hz, h32, h16, hnd, hzz, hany, hvb, hfz, hfix, hid'⟩ := hs
  have hidE : idArr = unpk (E.getD 0 0) := by rw [hid, hid']
  unfold listsK at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hzl, hze, hcent, hk, hd, hcomm, hsq, hfx⟩ := h
  have h0 : 0 < E.length := by omega
  have hv0 := vp_getD H h0
  have hcz : ∀ p < E.length, (arrMul (tArr p) z0Arr == arrMul z0Arr (tArr p)) = true := by
    intro p hp
    have hvp := vp_getD H hp
    rw [tArr_eq H hp, ← hz, arrMul_unpk _ hvz, arrMul_unpk _ hvp,
      unpk_beq (vpK_pc24 hvp hvz) (vpK_pc24 hvz hvp)]
    exact beq_iff_eq.2 (hcent _ (getD_mem hp))
  have hds : ∀ p ∈ dzIdxK E, p < E.length := fun p hp => lt_of_mem_filter_range hp
  have hks : ∀ p ∈ kIdxK E, p < E.length := fun p hp => lt_of_mem_filter_range hp
  have hmd : ∀ p ∈ dzIdxK E, E.getD p 0 ∈ E.filter (centP (vzMasks ())) :=
    fun p hp => getD_mem_filter (f := centP (vzMasks ())) hp
  unfold listsOK
  rw [kIdx_eq H, dzIdx_eq H, z0Idx_eq H hz hvz, n_eq H]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hzl, ?_, fun p hp => ?_, (length_filter_range fixesOctP E).trans hk,
    (length_filter_range (centP (vzMasks ())) E).trans hd, h32, h16, CFSG.Decide.nodup_of_bitsetNodup_nat hnd, hzz,
    hany, fun p hp => ?_, fun p hp => ?_, fun p hp q hq => ?_, fun p hp => ?_, fun p hp => ?_,
    fun p hp => ?_, hvb, hfz, hfix⟩
  · rw [tArr_eq H hzl, hze, hz]
  · have hp' := List.mem_range.1 hp
    refine mulIdx_comm H hp' hzl ?_
    rw [hze]
    exact hcent _ (getD_mem hp')
  · exact beq_iff_eq.1 (hcz p (hks p hp))
  · exact beq_iff_eq.1 (hcz p (hds p hp))
  · have hvp := vp_getD H (hds p hp)
    have hvq := vp_getD H (hds q hq)
    rw [tArr_eq H (hds p hp), tArr_eq H (hds q hq), arrMul_unpk _ hvq, arrMul_unpk _ hvp,
      hcomm _ (hmd p hp) _ (hmd q hq)]
  · have hvp := vp_getD H (hds p hp)
    rw [tArr_eq H (hds p hp), arrMul_unpk _ hvp, hsq _ (hmd p hp), hidE]
  · rw [tArr_eq H (List.mem_range.1 hp), size_unpk]
  · have hvp := vp_getD H (hds p hp)
    rw [tArr_eq H (hds p hp), fixesOct_unpk, hidE, ← hz, unpk_beq hvp hv0, unpk_beq hvp hvz]
    exact hfx _ (hmd p hp)

theorem f3OK_of_K (H : Packed T24s2 E) (hs : f3S = true) (h : f3K E = true) : f3OK () = true := by
  unfold f3OK
  rw [kIdx_eq H, inAutOK_eq_inAutK]
  simp only [Bool.and_eq_true]
  refine ⟨hs, ?_⟩
  unfold f3K at h
  rw [List.all_eq_true] at h ⊢
  intro p hp
  rw [tArr_eq H (lt_of_mem_filter_range hp)]
  exact h _ (getD_mem_filter (f := fixesOctP) hp)

theorem mem_wordsOfLen_lt {n : ℕ} : ∀ {k : ℕ} {w : List ℕ}, w ∈ wordsOfLen k n → ∀ g ∈ w, g < n
  | 0, w, hw, g, hg => by
    simp only [wordsOfLen, List.mem_singleton] at hw
    subst hw
    simp at hg
  | k + 1, w, hw, g, hg => by
    simp only [wordsOfLen, List.mem_flatMap, List.mem_map, List.mem_range] at hw
    obtain ⟨v, hv, a, ha, rfl⟩ := hw
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ha
    · exact mem_wordsOfLen_lt hv g hg

theorem mem_wordPool_lt {n L : ℕ} {w : List ℕ} (hw : w ∈ wordPool n L) : ∀ g ∈ w, g < n := by
  simp only [wordPool, List.mem_flatMap] at hw
  obtain ⟨k, -, hk⟩ := hw
  exact mem_wordsOfLen_lt hk

theorem applyWord_eq (hs : ∀ g ∈ moGens, g.size = 24) (hlen : moGens.length = 10) :
    ∀ w : List ℕ, (∀ g ∈ w, g < 10) → ∀ m, applyWord moGens w m = applyWordK w m
  | [], _, _ => rfl
  | g :: w, hw, m => by
    have ih := applyWord_eq hs hlen w (fun x hx => hw x (List.mem_cons_of_mem g hx)) m
    have hg : g < moGens.length := by rw [hlen]; exact hw g List.mem_cons_self
    have hm : moGens[g]! ∈ moGens := by
      rw [getElem!_pos moGens g hg]
      exact List.getElem_mem hg
    change actC11 (moGens[g]!) (applyWord moGens w m) = actM (moColsK.getD g []) (applyWordK w m)
    rw [ih, actC11_eq_cols (hs _ hm), moColsK, k43_getD_map _ _ hg]

theorem pick6_sub (cands : List ℕ) : ∀ x ∈ pick6 cands, x ∈ cands := by
  unfold pick6
  suffices H : ∀ (l acc : List ℕ), (∀ x ∈ acc, x ∈ cands) → (∀ x ∈ l, x ∈ cands) →
      ∀ x ∈ l.foldl (fun acc x =>
        if acc.length < 6 && !(combos acc).contains x then x :: acc else acc) acc, x ∈ cands from
    H cands [] (by simp) (fun x hx => hx)
  intro l
  induction l with
  | nil => intro acc ha _; exact ha
  | cons y l ih =>
    intro acc ha hl
    rw [List.foldl_cons]
    refine ih _ ?_ (fun x hx => hl x (List.mem_cons_of_mem y hx))
    split
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hl _ List.mem_cons_self
      · exact ha x hx
    · exact ha

theorem indep6_of_B {cands : List ℕ} (h : indep6B cands = true) : indep6 cands = true := by
  unfold indep6B at h
  unfold indep6
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  refine ⟨⟨h.1, CFSG.Decide.nodup_of_bitsetNodup_nat h.2⟩, fun x hx => ?_⟩
  simpa using pick6_sub cands x hx

theorem f4OK_of_K (hs : f4S = true) (h : ∀ i < 32, f4Slice i = true) : f4OK () = true := by
  unfold f4S at hs
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨hlen, hg⟩ := hs
  unfold f4OK
  rw [inAutOK_eq_inAutK]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun g hgm => ?_, fun m hm => ?_⟩
  · have := hg g hgm
    simp [this]
  · have hm' := List.mem_range.1 hm
    have hsl := h (m / 64) (by omega)
    unfold f4Slice at hsl
    have hp := List.all_eq_true.1 hsl m (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    unfold f4Pred at hp
    rw [Bool.or_eq_true] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl hp
    · refine Or.inr (indep6_of_B ?_)
      have e : (wordPool moGens.length 2).map (fun w => applyWord moGens w m) =
          (wordPool 10 2).map (fun w => applyWordK w m) := by
        rw [hlen]
        exact List.map_congr_left fun w hw =>
          applyWord_eq (fun g hg' => (hg g hg').1.1) hlen w (mem_wordPool_lt hw) m
      rw [e]
      exact hp

end CFSG.KS.ASVolI

end
