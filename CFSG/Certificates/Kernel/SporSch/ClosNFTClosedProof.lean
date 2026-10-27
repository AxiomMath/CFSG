module

public import CFSG.Certificates.Kernel.SporSch.PairClTProof

public section

namespace CFSG.KS.SporSch.ClR

open CFSG.KS CFSG.KS.Raw.Dec CFSG.KS.NKey CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Sporadic.Schreier.PairNative

theorem closure_replay_closed {n : Nat} {L : Array Level} {bs : List Nat}
    {gens gensInv : Array (Array Nat)} {rep : List (Array Nat)} {c cap fl M H : Nat}
    {T : Nat → Array Nat} {P Lb K C : Nat → Nat} {KS pos : Nat → Nat → Nat}
    {f : Nat → Nat → Nat → Nat}
    (hLv : LvOK n L bs) (hbn : ∀ b ∈ bs, b < n)
    (hgr : ∀ l < gens.size, ∀ y < n, (gens[l]!)[y]! < n ∧ (gensInv[l]!)[y]! < n)
    (hrr : ∀ x ∈ baseImgs bs rep, x < n)
    (hc0 : 0 < c) (hcap : c ≤ cap) (hcM : c ≤ M * H) (hfl : c ≠ fl)
    (hC0 : C 0 = 1) (hCM : C M = c) (hrun : ∀ t < M, runC f gens.size H (t * H) (C t) = C (t + 1))
    (habs : ∀ h l, l < gens.size → f h l fl = fl)
    (hT : ∀ i < c, nfOK L (T i) = true)
    (hκ : ∀ i < c, imgKey n (baseImgs bs (nfWord L (T i))) = K i)
    (hsk : ∀ h < c, ∀ l < gens.size, imgKey n (conjImgs bs gens[l]! gensInv[l]! (nfWord L (T h))) =
      KS h l)
    (hinj : ∀ a < c, ∀ b < c, K a = K b → a = b)
    (hk0 : imgKey n (baseImgs bs rep) = K 0) (hP0 : P 0 = 0) (hL0 : Lb 0 = 0)
    (hstep : ∀ h l cur, l < gens.size → f h l cur ≠ fl →
      (h < cur ∧ pos h l < cur ∧ K (pos h l) = KS h l ∧ f h l cur = cur) ∨
      (h < cur ∧ pos h l = cur ∧ K (pos h l) = KS h l ∧ P (pos h l) = h ∧ Lb (pos h l) = l ∧
        f h l cur = cur + 1) ∨
      (cur ≤ h ∧ cur = c ∧ f h l cur = cur)) :
    ∀ i < (conjClosureNF n L bs gens gensInv (decodeNF L (baseImgs bs rep).toArray) cap).1.size,
      ∀ l < gens.size,
      ∃ j < (conjClosureNF n L bs gens gensInv (decodeNF L (baseImgs bs rep).toArray) cap).1.size,
        baseImgs bs (nfWord L (conjClosureNF n L bs gens gensInv
          (decodeNF L (baseImgs bs rep).toArray) cap).1[j]!) =
        conjImgs bs gens[l]! gensInv[l]! (nfWord L (conjClosureNF n L bs gens gensInv
          (decodeNF L (baseImgs bs rep).toArray) cap).1[i]!) := by
  have hBI : ∀ nf, nfOK L nf = true → ∀ x ∈ baseImgs bs (nfWord L nf), x < n := by
    intro nf hnf' x hx
    obtain ⟨b, hm, rfl⟩ := List.mem_map.1 hx
    rw [nfWord_eq_hw]
    exact evR_hw_lt hLv hnf' _ (Nat.le_refl _) b (hbn b hm)
  have hCI : ∀ l < gens.size, ∀ nf, nfOK L nf = true →
      ∀ x ∈ conjImgs bs gens[l]! gensInv[l]! (nfWord L nf), x < n := by
    intro l hl' nf hnf' x hx
    obtain ⟨b, hm, rfl⟩ := List.mem_map.1 hx
    have hy := (hgr l hl' b (hbn b hm)).2
    refine (hgr l hl' _ ?_).1
    rw [nfWord_eq_hw]
    exact evR_hw_lt hLv hnf' _ (Nat.le_refl _) _ hy
  have hdec : ∀ (l : List Nat), ∀ i < c, l.length = bs.length → (∀ x ∈ l, x < n) →
      imgKey n l = K i → l = baseImgs bs (nfWord L (T i)) ∧ decodeNF L l.toArray = T i := by
    intro l i hi hlen hlt hk
    have e := imgKey_inj (by rw [hlen, baseImgs, List.length_map]) hlt (hBI _ (hT i hi))
      (hk.trans (hκ i hi).symm)
    refine ⟨e, ?_⟩
    rw [e]
    exact decodeNF_nfWord hLv (hT i hi)
  have hroot : T 0 = decodeNF L (baseImgs bs rep).toArray :=
    ((hdec _ 0 hc0 (by simp [baseImgs]) hrr hk0).2).symm
  have R : NKRec (fun l nf => imgKey n (conjImgs bs gens[l]! gensInv[l]! (nfWord L nf)))
      (fun l nf => decodeNF L (conjImgs bs gens[l]! gensInv[l]! (nfWord L nf)).toArray)
      (fun nf => imgKey n (baseImgs bs (nfWord L nf))) gens.size
      (decodeNF L (baseImgs bs rep).toArray)
      (imgKey n (baseImgs bs (nfWord L (decodeNF L (baseImgs bs rep).toArray)))) c T P Lb pos := by
    refine runC_rec (f := f) (fl := fl) (M := M) (H := H) (C := C) hc0 hcM hfl hC0 hCM hrun habs
      (fun h l cur hl' hne => ?_) hroot rfl hP0 hL0 (fun a ha b hb' e => ?_)
    · rcases hstep h l cur hl' hne with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3⟩
      · refine Or.inl ⟨h1, h2, h4, fun hcur => ?_⟩
        dsimp only
        rw [hsk h (by omega) l hl', hκ _ (by omega), h3]
      · refine Or.inr (Or.inl ⟨h1, h2, h6, fun hcur => ?_⟩)
        rw [h2] at h3 h4 h5
        have hk : imgKey n (conjImgs bs gens[l]! gensInv[l]! (nfWord L (T h))) = K cur := by
          rw [hsk h (by omega) l hl', h3]
        refine ⟨hk.trans (hκ cur hcur).symm, (hdec _ cur hcur (by simp [conjImgs])
          (hCI l hl' _ (hT h (by omega))) hk).2, h4, h5⟩
      · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
    · exact hinj a ha b hb' (by rw [← hκ a ha, ← hκ b hb']; exact e)
  rw [conjClosureNF_eq, nkbfs_rec R hcap]
  have hTa : ∀ i < c, (Array.ofFn (n := c) fun i => T i.val)[i]! = T i :=
    fun i hi => getElem!_ofFn_gen _ hi
  simp only [Array.size_ofFn]
  intro i hi l hl
  obtain ⟨hp, hk, -⟩ := R.close i hi l hl
  refine ⟨pos i l, hp, ?_⟩
  rw [hTa i hi, hTa _ hp]
  exact imgKey_inj (by simp [baseImgs, conjImgs]) (hBI _ (hT _ hp)) (hCI _ hl _ (hT i hi)) hk.symm

end CFSG.KS.SporSch.ClR

namespace CFSG.KS.SporSch.ClTP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Raw.Dec CFSG.KS.NKey
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Certificates
  CFSG.Certificates.ChainArrays CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.KS.SporSch

theorem closNFT_closedP {n w kS nb BP NS CH NR NL NT BT NQ BQ kg c cap nS R H nB B : Nat}
    {PS PSI LR Ts LT PT QT GLt X W K C SO SOI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs RP : List Nat}
    {gens gensInv : Array (Array Nat)} {rep : List (Array Nat)}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)
    (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) (hbs : base.toList = bs)
    (hg : gens.size = kg ∧ gensInv.size = kg ∧
      ∀ l < kg, gens[l]! = unpack n w (letterK PS PSI kS (GLt l)) ∧
        gensInv[l]! = unpack n w (letterK PS PSI kS (invL kS (GLt l))))
    (hrep : rep = RP.map (unpack n w))
    (h : ClosNFT n w kS nb NR NL LR LT PT QT bs kg GLt RP c cap nS R H nB B X W K C SO SOI) :
    ∀ i < (conjClosureNF n (rawLevels n S base) bs gens gensInv
        (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.size, ∀ l < kg,
      ∃ j < (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.size,
        baseImgs bs (nfWord (rawLevels n S base) (conjClosureNF n (rawLevels n S base) bs gens
          gensInv (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1[j]!) =
        conjImgs bs gens[l]! gensInv[l]! (nfWord (rawLevels n S base) (conjClosureNF n
          (rawLevels n S base) bs gens gensInv
            (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1[i]!) := by
  subst hbs hrep
  obtain ⟨hgs, hgis, hgl⟩ := hg
  subst hgs
  obtain ⟨hc0, hcap, hcS, hcB, hc20, -, -, hGLt, hRP, -, hst, hk0, hrec, hsrt, hC0, hCN, hrun⟩ := h
  have hbl := Tab.base_lt hb ho hN
  have hLv := lvOK_rawLevels hb hp hbl
  have hbn : ∀ b ∈ base.toList, b < n := fun b hm => ClR.mem_base_lt hb.2.2.2.2.2.1 hbl hm
  have hr : ∀ i < c, nfValidK nb LR (nfX nb (X i)) = true ∧
      K i = nfKeyT n w NR NL LT PT nb base.toList (nfX nb (X i)) := by
    intro i hi
    have h1 := all_of_blocks hcB hrec i hi
    unfold recOKT at h1
    rw [Orb.blt_true hi] at h1
    have h2 : strictB (nfX nb (X i)) (fun x => bAnd(allN nb (fun t =>
        Nat.blt (Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 16) t)) (nat_lit 65535))
          (rcnt (LR t))), Nat.beq (K i) (nfKeyT n w NR NL LT PT nb base.toList x))) = true := h1
    rw [Orb.strictB_eq, bAnd_iff] at h2
    exact ⟨h2.1, Nat.eq_of_beq_eq_true h2.2⟩
  have srt := keysK_sound (cs := [(c, K)]) (by simp) hcB hsrt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at srt
  have hD := nodup_of_strictInc_mergeSort srt
  have hgr : ∀ l < gens.size, ∀ y < n, (gens[l]!)[y]! < n ∧ (gensInv[l]!)[y]! < n := by
    intro l hl' y hy
    rw [(hgl l hl').1, (hgl l hl').2, unpack_get hy, unpack_get hy]
    exact ⟨letter_lt hb hp (hGLt l hl') hy,
      letter_lt hb hp (Tab.letterK_invL (PS := PS) (PSI := PSI) (hGLt l hl')).2 hy⟩
  have hrr : ∀ x ∈ baseImgs base.toList (RP.map (unpack n w)), x < n := by
    intro x hx
    obtain ⟨b, hm, rfl⟩ := List.mem_map.1 hx
    have := ClP.evRK_eq (ClP.range_of_canonL hRP) b (hbn b hm)
    rw [← this.1]
    exact this.2
  have hP0 : parNF nb (X 0) = 0 ∧ labNF nb (X 0) = 0 := by
    unfold startNFT at hst
    rw [bAnd_iff, bAnd_iff, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at hst
    exact hst.2
  exact ClR.closure_replay_closed (T := fun i => Tab.nfA nb (nfX nb (X i)))
    (P := fun i => parNF nb (X i)) (Lb := fun i => labNF nb (X i)) (K := K)
    (KS := fun h l => conjKeyT n w kS NR NL LT PT nb base.toList (GLt l) (nfX nb (X h)))
    (pos := ClP.posW W)
    (f := fun h l cur => stepNFT n w kS NR NL LT PT QT nb base.toList GLt X W K c h l cur)
    (fl := failC) (M := nS * R) (H := H) (C := C)
    hLv hbn hgr hrr hc0 hcap hcS (by rw [ClP.failC_eq]; omega) hC0 hCN (slices_of_groups hrun)
    (fun h l _ => stepNFT_fail) (fun i hi => (Tab.nfPtT_spec hb hp ho hN ht (hr i hi).1).1)
    (fun i hi => by rw [(hr i hi).2, nfKeyT_eq hb hp ho hN ht (hr i hi).1])
    (fun h hh l hl' => by
      rw [conjKeyT_eq hb hp ho hN ht (hr h hh).1 (hGLt l hl') (hgl l hl').1 (hgl l hl').2])
    (fun a ha b hb' e => List.inj_on_of_nodup_map hD (List.mem_range.2 ha) (List.mem_range.2 hb') e)
    (by rw [← ClP.wordKey_eq hRP hbn]; exact (Nat.eq_of_beq_eq_true hk0).symm) hP0.1 hP0.2
    (fun h l cur _ hne => stepNFT_spec hne)

end CFSG.KS.SporSch.ClTP

end
