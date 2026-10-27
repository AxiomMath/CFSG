module

public import CFSG.Certificates.Kernel.Spor.BfsReplay
public import Certificates.Data.CFSGNative.PairSchreier.Core
public import CFSG.Certificates.Kernel.Spor.RawAgree

public section

namespace CFSG.KS.Raw.Dec

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays
  CFSG.Sporadic.Schreier.PairNative

structure LvOK (n : Nat) (L : Array Level) (bs : List Nat) : Prop where
  len : bs.length = L.size
  blt : ∀ i < L.size, bs[i]! < n
  trlt : ∀ i < L.size, ∀ k < L[i]!.pts.size, ∀ x < n, (L[i]!.tr[k]!)[x]! < n
  inv : ∀ i < L.size, ∀ k < L[i]!.pts.size, ∀ x < n,
    (L[i]!.trInv[k]!)[(L[i]!.tr[k]!)[x]!]! = x
  root : ∀ i < L.size, ∀ k < L[i]!.pts.size, (L[i]!.tr[k]!)[bs[i]!]! = L[i]!.pts[k]!
  pos : ∀ i < L.size, ∀ k < L[i]!.pts.size, L[i]!.pos[L[i]!.pts[k]!]! = k
  fix : ∀ i < L.size, ∀ k < L[i]!.pts.size, ∀ m < i, (L[i]!.tr[k]!)[bs[m]!]! = bs[m]!

@[expose] def tw (L : Array Level) (nf : Array Nat) (d : Nat) : List (Array Nat) :=
  (List.range' d (nf.size - d)).reverse.map fun i => L[i]!.tr[nf[i]!]!

theorem evR_append_one (A : List (Array Nat)) (t : Array Nat) (x : Nat) :
    evR (A ++ [t]) x = t[evR A x]! := by
  unfold evR
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem evR_cons (t : Array Nat) (A : List (Array Nat)) (x : Nat) :
    evR (t :: A) x = evR A t[x]! := by
  unfold evR
  rw [List.foldl_cons]

theorem nfWord_eq_tw (L : Array Level) (nf : Array Nat) : nfWord L nf = tw L nf 0 := by
  unfold nfWord tw
  rw [List.range_eq_range', Nat.sub_zero]

theorem evR_tw_succ (L : Array Level) (nf : Array Nat) {d : Nat} (hd : d < nf.size) (x : Nat) :
    evR (tw L nf d) x = (L[d]!.tr[nf[d]!]!)[evR (tw L nf (d + 1)) x]! := by
  unfold tw
  have e : nf.size - d = (nf.size - (d + 1)) + 1 := by omega
  rw [e, List.range'_succ, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
    evR_append_one]

theorem evR_tw_end (L : Array Level) (nf : Array Nat) {d : Nat} (hd : nf.size ≤ d) (x : Nat) :
    evR (tw L nf d) x = x := by
  unfold tw
  rw [Nat.sub_eq_zero_of_le hd]
  rfl

@[expose] def hw (L : Array Level) (nf : Array Nat) (j : Nat) : List (Array Nat) :=
  (List.range j).reverse.map fun i => L[i]!.tr[nf[i]!]!

theorem nfWord_eq_hw (L : Array Level) (nf : Array Nat) : nfWord L nf = hw L nf nf.size := rfl

theorem evR_hw_succ (L : Array Level) (nf : Array Nat) (j x : Nat) :
    evR (hw L nf (j + 1)) x = evR (hw L nf j) ((L[j]!.tr[nf[j]!]!)[x]!) := by
  unfold hw
  rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.map_cons, evR_cons]

section

variable {n : Nat} {L : Array Level} {bs : List Nat} (hL : LvOK n L bs) {nf : Array Nat}
  (hnf : nfOK L nf = true)
include hL hnf

omit hL in
theorem nfOK_spec : nf.size = L.size ∧ ∀ i < nf.size, nf[i]! < L[i]!.pts.size := by
  unfold nfOK at hnf
  rw [Bool.and_eq_true, beq_iff_eq, allLt_iff] at hnf
  exact ⟨hnf.1, fun i hi => of_decide_eq_true (hnf.2 i hi)⟩

theorem evR_tw_lt : ∀ d, ∀ x < n, evR (tw L nf d) x < n := by
  obtain ⟨hs, hv⟩ := nfOK_spec hnf
  have key : ∀ j d, nf.size - d = j → ∀ x < n, evR (tw L nf d) x < n := by
    intro j
    induction j with
    | zero => intro d hd x hx; rw [evR_tw_end L nf (by omega)]; exact hx
    | succ j ih =>
      intro d hd x hx
      rw [evR_tw_succ L nf (by omega)]
      exact hL.trlt d (by omega) _ (hv d (by omega)) _ (ih (d + 1) (by omega) x hx)
  exact fun d => key _ d rfl

theorem evR_hw_lt : ∀ j ≤ nf.size, ∀ x < n, evR (hw L nf j) x < n := by
  obtain ⟨hs, hv⟩ := nfOK_spec hnf
  intro j
  induction j with
  | zero => intro _ x hx; exact hx
  | succ j ih =>
    intro hj x hx
    rw [evR_hw_succ]
    exact ih (by omega) _ (hL.trlt j (by omega) _ (hv j (by omega)) _ hx)

theorem evR_tw_fix : ∀ d, ∀ m < d, m < L.size → evR (tw L nf d) bs[m]! = bs[m]! := by
  obtain ⟨hs, hv⟩ := nfOK_spec hnf
  have key : ∀ j d, nf.size - d = j → ∀ m < d, m < L.size → evR (tw L nf d) bs[m]! = bs[m]! := by
    intro j
    induction j with
    | zero => intro d hd m _ _; exact evR_tw_end L nf (by omega) _
    | succ j ih =>
      intro d hd m hm hmL
      rw [evR_tw_succ L nf (by omega), ih (d + 1) (by omega) m (by omega) hmL]
      exact hL.fix d (by omega) _ (hv d (by omega)) m hm
  exact fun d => key _ d rfl

theorem evR_tw_base {d : Nat} (hd : d < L.size) :
    evR (tw L nf d) bs[d]! = L[d]!.pts[nf[d]!]! := by
  obtain ⟨hs, hv⟩ := nfOK_spec hnf
  rw [evR_tw_succ L nf (by omega), evR_tw_fix hL hnf (d + 1) d (by omega) hd]
  exact hL.root d hd _ (hv d (by omega))

end

theorem getElem!_toArray_map (l : List Nat) (f : Nat → Nat) {i : Nat} (hi : i < l.length) :
    (l.map f).toArray[i]! = f l[i]! := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp [getElem!_pos l i hi]

@[expose] def decBody (L : Array Level) (i : Nat) (r : Array Nat × Array Nat) :
    Id (ForInStep (Array Nat × Array Nat)) :=
  pure (ForInStep.yield (r.1.map fun x => (L[i]!.trInv[L[i]!.pos[r.1[i]!]!]!)[x]!,
    r.2.push L[i]!.pos[r.1[i]!]!))

theorem decodeNF_eq (L : Array Level) (imgs : Array Nat) :
    decodeNF L imgs = (Id.run (forIn (List.range' 0 L.size) (imgs, #[]) (decBody L))).2 := by
  unfold decodeNF
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem decodeNF_nfWord {n : Nat} {L : Array Level} {bs : List Nat} (hL : LvOK n L bs)
    {nf : Array Nat} (hnf : nfOK L nf = true) :
    decodeNF L (baseImgs bs (nfWord L nf)).toArray = nf := by
  obtain ⟨hs, hv⟩ := nfOK_spec hnf
  rw [decodeNF_eq]
  have := CFSG.KS.BfsReplay.forIn_range'_yield L.size 0
    ((baseImgs bs (nfWord L nf)).toArray, (#[] : Array Nat)) (decBody L)
    (fun d r => r.1 = (bs.map (evR (tw L nf d))).toArray ∧ r.2 = nf.extract 0 d)
    (fun d hd r hr => by
      rw [Nat.zero_add]
      have e1 : r.1[d]! = L[d]!.pts[nf[d]!]! := by
        rw [hr.1, getElem!_toArray_map _ _ (by rw [hL.len]; omega), evR_tw_base hL hnf hd]
      have e2 : L[d]!.pos[r.1[d]!]! = nf[d]! := by rw [e1, hL.pos d hd _ (hv d (by omega))]
      refine ⟨_, rfl, ?_, ?_⟩
      · dsimp only
        rw [e2, hr.1, List.map_toArray, List.map_map]
        congr 1
        refine List.map_congr_left fun b hb => ?_
        have hbn : b < n := by
          obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hb
          have := hL.blt m (by rw [← hL.len]; exact hm)
          rwa [getElem!_pos bs m hm] at this
        simp only [Function.comp_apply]
        rw [evR_tw_succ L nf (by omega)]
        exact hL.inv d hd _ (hv d (by omega)) _ (evR_tw_lt hL hnf (d + 1) b hbn)
      · dsimp only
        rw [e2, hr.2]
        apply Array.ext
        · simp only [Array.size_push, Array.size_extract]
          omega
        · intro i h1 h2
          simp only [Array.size_push, Array.size_extract] at h1
          rw [Array.getElem_extract, Array.getElem_push]
          split
          · rw [Array.getElem_extract]
          · have e : i = d := by simp at *; omega
            subst e
            rw [getElem!_pos nf i (by omega)]
            simp)
    ⟨by rw [nfWord_eq_tw]; rfl, by simp⟩
  rw [this.2, ← hs]
  exact Array.extract_size

section Raw

variable {n w kS nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}

theorem steps_fix (hI : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true)
    (hbl : ∀ t < base.size, base[t]! < n) {i j : Nat} (hj : j < (rawSteps n S base i).size)
    {m : Nat} (hm : m < i) (hmb : m < base.size) :
    ((rawSteps n S base i)[j]!)[base[m]!]! = base[m]! := by
  have hmem : (rawSteps n S base i)[j]! ∈ levelSteps S (rawInvs n S) base i := by
    rw [getElem!_pos _ j hj]
    exact Array.getElem_mem hj
  unfold levelSteps at hmem
  rw [Array.mem_append, List.mem_toArray, List.mem_toArray, List.mem_map, List.mem_map] at hmem
  have hfx : ∀ j' ∈ levelIdx S base i, (S[j']!)[base[m]!]! = base[m]! ∧ j' < S.size := by
    intro j' hj'
    unfold levelIdx at hj'
    rw [List.mem_filter, List.mem_range] at hj'
    unfold fixesFirst at hj'
    rw [allLt_iff] at hj'
    exact ⟨beq_iff_eq.1 (hj'.2 m hm), hj'.1⟩
  rcases hmem with ⟨j', hj', e⟩ | ⟨j', hj', e⟩
  · rw [← e]
    exact (hfx j' hj').1
  · rw [← e]
    obtain ⟨h1, h2⟩ := hfx j' hj'
    have := (isInvA_spec (hI j' h2) (hbl m hmb)).2
    rwa [h1] at this

variable (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
include hb hp

theorem lvOK_rawLevels (hbl : ∀ t < nb, base[t]! < n) :
    LvOK n (rawLevels n S base) base.toList := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hsz : (rawLevels n S base).size = nb := by rw [rawLevels, Array.size_ofFn, hbs]
  have hI := isInv_of hb hp
  have hbl' : ∀ t < base.size, base[t]! < n := fun t ht => hbl t (by omega)
  have hbt : ∀ t, base.toList[t]! = base[t]! := fun t => by
    by_cases ht : t < base.size
    · rw [getElem!_pos base.toList t (by simpa using ht), getElem!_pos base t ht,
        Array.getElem_toList]
    · rw [getElem!_neg base.toList t (by simpa using ht), getElem!_neg base t ht]
  have F : ∀ i < nb, LevelFacts n base[i]! (rawSteps n S base i) (rawLevels n S base)[i]! :=
    fun i hi => native_facts hb hp hi (hbl i hi)
  have hfix : ∀ i < nb, ∀ k < (rawLevels n S base)[i]!.pts.size, ∀ m < i,
      ((rawLevels n S base)[i]!.tr[k]!)[base[m]!]! = base[m]! := by
    intro i hi k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk m hm
      have hbm := hbl m (by omega)
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have e := allLt_spec (F i hi).tr_zero hbm
        rw [beq_iff_eq, idA_get hbm] at e
        exact e
      · have e := allLt_spec ((F i hi).tr_step k hk hk0) hbm
        rw [beq_iff_eq, compA_get hbm] at e
        rw [e, ih _ ((F i hi).par_lt k hk hk0) (by have := (F i hi).par_lt k hk hk0; omega) m hm]
        exact steps_fix hI hbl' ((F i hi).lab_lt k hk hk0) hm (by omega)
  have hroot : ∀ i < nb, ∀ k < (rawLevels n S base)[i]!.pts.size,
      ((rawLevels n S base)[i]!.tr[k]!)[base[i]!]! = (rawLevels n S base)[i]!.pts[k]! := by
    intro i hi k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have hbi := hbl i hi
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have e := allLt_spec (F i hi).tr_zero hbi
        rw [beq_iff_eq, idA_get hbi] at e
        rw [e, (F i hi).root]
      · have e := allLt_spec ((F i hi).tr_step k hk hk0) hbi
        rw [beq_iff_eq, compA_get hbi] at e
        have hp' := (F i hi).par_lt k hk hk0
        rw [e, ih _ hp' (by omega)]
        exact (F i hi).edge k hk hk0
  refine ⟨by rw [Array.length_toList, hsz, hbs], fun i hi => by rw [hbt]; exact hbl i (by omega),
    fun i hi k hk x hx => ?_, fun i hi k hk x hx => ?_, fun i hi k hk => ?_,
    fun i hi k hk => (F i (by omega)).pos_pts k hk, fun i hi k hk m hm => ?_⟩
  · exact (isInvA_spec ((F i (by omega)).tr_inv k hk) hx).1
  · exact (isInvA_spec ((F i (by omega)).tr_inv k hk) hx).2
  · rw [hbt]
    exact hroot i (by omega) k hk
  · rw [hbt]
    exact hfix i (by omega) k hk m hm

end Raw

end CFSG.KS.Raw.Dec

end
