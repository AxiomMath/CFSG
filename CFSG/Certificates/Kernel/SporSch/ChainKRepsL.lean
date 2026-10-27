module

public import CFSG.Certificates.Kernel.SporSch.ChainKReps
public import Certificates.Data.Kernel.Spor.MCount
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum
open CFSG.KS.Mathieu
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu CFSG.KS.SporSch.ClsSpec

variable {n w : Nat}

theorem bpos_zero (nw pm S c x lo hi : Nat) :
    bpos nw pm S c x 0 lo hi = if lo < hi ∧ blk S nw pm lo = x then lo else c := by
  change nIf(bAnd(Nat.blt lo hi, Nat.beq (blk S nw pm lo) x), lo, c) = _
  simp only [Orb.nIf_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, beq_dec, decide_eq_true_eq]

theorem bpos_succ (nw pm S c x d lo hi : Nat) :
    bpos nw pm S c x (d + 1) lo hi =
      if hi ≤ lo + 1 then (if lo < hi ∧ blk S nw pm lo = x then lo else c)
      else if x < blk S nw pm ((lo + hi) / 2) then bpos nw pm S c x d lo ((lo + hi) / 2)
      else bpos nw pm S c x d ((lo + hi) / 2) hi := by
  change nIf(Nat.ble hi (Nat.succ lo), nIf(bAnd(Nat.blt lo hi, Nat.beq (blk S nw pm lo) x), lo, c),
      strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) (fun mid =>
        nIf(Nat.blt x (blk S nw pm mid), bpos nw pm S c x d lo mid,
          bpos nw pm S c x d mid hi))) = _
  rw [Orb.strictN_eq]
  simp only [Orb.nIf_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_dec,
    decide_eq_true_eq, Nat.succ_eq_add_one, Nat.add_eq, Orb.shr_eq, Nat.pow_one]

theorem bpos_sound (nw pm S c x : Nat) : ∀ d lo hi, bpos nw pm S c x d lo hi < c →
    blk S nw pm (bpos nw pm S c x d lo hi) = x
  | 0, lo, hi, h => by
    rw [bpos_zero] at h ⊢
    split_ifs at h ⊢ with hc
    · exact hc.2
    · omega
  | d + 1, lo, hi, h => by
    rw [bpos_succ] at h ⊢
    split_ifs at h ⊢ with h1 hc h2
    · exact hc.2
    · omega
    · exact bpos_sound nw pm S c x d _ _ h
    · exact bpos_sound nw pm S c x d _ _ h

theorem bpos_complete (nw pm S c : Nat)
    (hinc : ∀ i j, i < j → j < c → blk S nw pm i < blk S nw pm j) {k : Nat} (hk : k < c) :
    ∀ d lo hi, lo ≤ k → k < hi → hi ≤ c → hi - lo ≤ 2 ^ d →
      bpos nw pm S c (blk S nw pm k) d lo hi = k
  | 0, lo, hi, h1, h2, h3, h4 => by
    have : k = lo := by simp at h4; omega
    subst this
    rw [bpos_zero]
    simp [h2]
  | d + 1, lo, hi, h1, h2, h3, h4 => by
    rw [bpos_succ]
    by_cases hb : hi ≤ lo + 1
    · have : k = lo := by omega
      subst this
      simp [hb, h2]
    simp only [hb, ↓reduceIte]
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; ring
    by_cases hx : blk S nw pm k < blk S nw pm ((lo + hi) / 2)
    · simp only [hx, ↓reduceIte]
      have hkm : k < (lo + hi) / 2 := by
        by_contra hc
        rcases Nat.lt_or_ge ((lo + hi) / 2) k with h | h
        · exact absurd (hinc _ _ h hk) (by omega)
        · have : k = (lo + hi) / 2 := by omega
          rw [this] at hx
          exact absurd hx (Nat.lt_irrefl _)
      exact bpos_complete nw pm S c hinc hk d lo _ h1 hkm (by omega) (by omega)
    · simp only [hx, ↓reduceIte]
      have hkm : (lo + hi) / 2 ≤ k := by
        by_contra hc
        exact hx (hinc _ _ (by omega) (by omega))
      exact bpos_complete nw pm S c hinc hk d _ hi hkm h2 h3 (by omega)

theorem bmem_sound {nw pm S c x : Nat} (h : bmem nw pm S c x = true) :
    ∃ k < c, blk S nw pm k = x := by
  unfold bmem at h
  rw [Nat.blt_eq] at h
  exact ⟨_, h, bpos_sound nw pm S c x _ _ _ h⟩

theorem bmem_complete {nw pm S c : Nat} (hc : c ≤ 2 ^ 32)
    (hinc : ∀ i j, i < j → j < c → blk S nw pm i < blk S nw pm j) {x : Nat}
    (h : bmem nw pm S c x = false) : ∀ k < c, blk S nw pm k ≠ x := by
  intro k hk e
  subst e
  unfold bmem at h
  rw [bpos_complete nw pm S c hinc hk 32 0 c (Nat.zero_le _) hk le_rfl (by simpa using hc),
    Nat.blt_eq.mpr hk] at h
  exact Bool.noConfusion h

@[expose] noncomputable def mstep (c : Nat) (q : Nat → Nat) (k M : Nat) : Nat :=
  if q k < c ∧ ¬ M.testBit (q k) then M ||| (1 <<< q k) else M ||| (1 <<< c)

theorem hasBit_eq (M l : Nat) : hasBit M l = M.testBit l := by
  unfold hasBit
  rw [Bool.eq_iff_iff, Nat.blt_eq]
  change 0 < M &&& 1 <<< l ↔ _
  rw [Nat.one_shiftLeft, Nat.and_two_pow, Nat.pos_iff_ne_zero]
  cases M.testBit l <;> simp

theorem testBit_mstep_mono (c : Nat) (q : Nat → Nat) (k M b : Nat) (h : M.testBit b = true) :
    (mstep c q k M).testBit b = true := by
  unfold mstep
  split <;> simp [Nat.testBit_or, h]

theorem testBit_foldl_mono (c : Nat) (q : Nat → Nat) (b : Nat) :
    ∀ (l : List Nat) (M : Nat), M.testBit b = true →
      (l.foldl (fun M k => mstep c q k M) M).testBit b = true
  | [], _, h => h
  | k :: l, M, h => testBit_foldl_mono c q b l _ (testBit_mstep_mono c q k M b h)

theorem testBit_foldl_mono' (c : Nat) (q : Nat → Nat) (b : Nat) (f : Nat → Nat) :
    ∀ (l : List Nat) (M : Nat), M.testBit b = true →
      (l.foldl (fun M i => mstep c q (f i) M) M).testBit b = true
  | [], _, h => h
  | i :: l, M, h => testBit_foldl_mono' c q b f l _ (testBit_mstep_mono c q (f i) M b h)

theorem mask_facts {c : Nat} {q : Nat → Nat}
    (h : ((List.range c).foldl (fun M k => mstep c q k M) 0) >>> c = 0) :
    ∀ k < c, q k < c ∧ ∀ k' < k, q k' ≠ q k := by
  set Ms : Nat → Nat := fun t => (List.range t).foldl (fun M k => mstep c q k M) 0
  have hsucc : ∀ t, Ms (t + 1) = mstep c q t (Ms t) := fun t => by
    simp only [Ms, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hfin : ∀ t, t ≤ c → ∀ b, (Ms t).testBit b = true → (Ms c).testBit b = true := by
    intro t ht b hb
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    have e : Ms c = (List.range d).foldl (fun M i => mstep c q (t + i) M) (Ms t) := by
      simp only [Ms, hd, List.range_add, List.foldl_append, List.foldl_map]
    rw [e]
    exact testBit_foldl_mono' c q b _ _ _ hb
  have hc : (Ms c).testBit c = false := by
    have := congrArg (fun x => x.testBit 0) h
    simpa [Nat.testBit_shiftRight] using this
  have hstep : ∀ k < c, q k < c ∧ ¬ (Ms k).testBit (q k) := by
    intro k hk
    by_contra hn
    have h1 : (Ms (k + 1)).testBit c = true := by
      rw [hsucc]
      unfold mstep
      simp only [hn, ↓reduceIte]
      simp [Nat.testBit_or, Nat.one_shiftLeft]
    rw [hfin (k + 1) hk c h1] at hc
    exact Bool.noConfusion hc
  intro k hk
  refine ⟨(hstep k hk).1, fun k' hk' e => (hstep k hk).2 ?_⟩
  have h1 : (Ms (k' + 1)).testBit (q k') = true := by
    rw [hsucc]
    unfold mstep
    simp [hstep k' (by omega), Nat.testBit_or]
  rw [← e]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show k' + 1 ≤ k by omega)
  have : Ms k = (List.range d).foldl (fun M i => mstep c q (k' + 1 + i) M) (Ms (k' + 1)) := by
    simp only [Ms, hd, List.range_add, List.foldl_append, List.foldl_map]
  rw [this]
  exact testBit_foldl_mono' c q _ _ _ _ h1

theorem lenN_eq' : ∀ l : List Nat, lenN l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenN_eq' l)

theorem nget_eq : ∀ (l : List Nat) (i : Nat), nget l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nget_eq l i

theorem allLtN_iff (b : Nat) : ∀ l : List Nat, allLtN b l = true ↔ ∀ x ∈ l, x < b
  | [] => by simp [allLtN]
  | x :: l => by
    change bAnd(Nat.blt x b, allLtN b l) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, allLtN_iff b l, List.forall_mem_cons]

theorem blk_packL {nw : Nat} {L : List Nat} (hL : ∀ x ∈ L, x < 2 ^ nw) (k : Nat) :
    blk (packL nw L) nw (mask nw) k = L.getD k 0 := by
  change pg nw (mask nw) (packL nw L) k = _
  refine PF.pg_of_fld (fld_packL nw L hL) ?_
  rcases Nat.lt_or_ge k L.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hL _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    exact Nat.two_pow_pos nw

theorem getD_lt {nw : Nat} {L : List Nat} (hL : ∀ x ∈ L, x < 2 ^ nw) (k : Nat) :
    L.getD k 0 < 2 ^ nw := by
  rcases Nat.lt_or_ge k L.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hL _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    exact Nat.two_pow_pos nw

theorem shr_of_lt {x n w : Nat} (h : x < 2 ^ (n * w)) : x >>> (n * w) = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt h

theorem clsOK_facts {A Ai B Bi mx cap R : Nat} {BlL P Lb SL : List Nat}
    (hBl : ∀ x ∈ BlL, x < 2 ^ (n * w)) (hS : ∀ x ∈ SL, x < 2 ^ (n * w))
    (h : clsOK n w (mask w) (n * w) (mask (n * w)) A Ai B Bi mx cap R (packL (n * w) BlL) P Lb
      (packL (n * w) SL) (lenN SL) = true) :
    SL.length ≤ cap ∧ ordC n w (mask w) R = mx ∧ BlL.getD 0 0 = R ∧
      (∀ k, k + 1 < SL.length → SL.getD k 0 < SL.getD (k + 1) 0) ∧
      (∀ k < SL.length, bmem (n * w) (mask (n * w)) (packL (n * w) SL) SL.length
          (conjK n w (mask w) A Ai (SL.getD k 0)) = true ∧
        bmem (n * w) (mask (n * w)) (packL (n * w) SL) SL.length
          (conjK n w (mask w) B Bi (SL.getD k 0)) = true) ∧
      (∀ k < SL.length, k ≠ 0 → P.getD k 0 < k ∧
        BlL.getD k 0 = if Lb.getD k 0 = 0 then conjK n w (mask w) A Ai (BlL.getD (P.getD k 0) 0)
          else conjK n w (mask w) B Bi (BlL.getD (P.getD k 0) 0)) ∧
      ((List.range SL.length).foldl (fun M k => mstep SL.length (fun k =>
        bpos (n * w) (mask (n * w)) (packL (n * w) SL) SL.length (BlL.getD k 0) 32 0
          SL.length) k M) 0) >>> SL.length = 0 := by
  unfold clsOK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, -, -, h6, -, h8, h9, h10⟩ := h
  rw [lenN_eq'] at h1 h6 h8 h9 h10
  simp only [blk_packL hBl, blk_packL hS] at h3 h6 h8 h9 h10
  refine ⟨Nat.ble_eq.mp h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    fun k hk => ?_, fun k hk => ?_, fun k hk hk0 => ?_, ?_⟩
  · have := allN_iff.1 h6 k (by change k < SL.length - 1; omega)
    simpa [Nat.blt_eq] using this
  · have := allN_iff.1 h8 k hk
    simp only [Orb.strictB_eq, Bool.and_eq_true] at this
    exact this
  · have := allN_iff.1 h9 k hk
    simp only [Orb.bIf_eq, Orb.strictB_eq, Bool.and_eq_true, beq_dec,
      decide_eq_true_eq, hk0, ↓reduceIte, Nat.blt_eq, nget_eq, Orb.nIf_eq] at this
    obtain ⟨hp, -, he⟩ := this
    exact ⟨hp, he⟩
  · have e := Nat.eq_of_beq_eq_true h10
    rw [Orb.shr_eq, foldUp_eq] at e
    rw [Nat.shiftRight_eq_div_pow]
    refine (congrArg (· / 2 ^ SL.length)
      (congrArg (fun f => (List.range SL.length).foldl f 0) ?_)).trans e
    funext M k
    simp only [Orb.strictN_eq, Orb.nIf_eq, Orb.bIf_eq, hasBit_eq, mstep]
    by_cases ha : bpos (n * w) (mask (n * w)) (packL (n * w) SL) SL.length (BlL.getD k 0) 32 0
      SL.length < SL.length <;>
    by_cases hb : M.testBit (bpos (n * w) (mask (n * w)) (packL (n * w) SL) SL.length
      (BlL.getD k 0) 32 0 SL.length) = true <;>
    simp_all

section Datum

variable {gA gB : Equiv.Perm (Fin n)} {A Ai B Bi : Nat} (hn : n < 2 ^ 32) (hw : 0 < w)
  (pA : PRep n w A gA) (pAi : PRep n w Ai gA⁻¹) (pB : PRep n w B gB) (pBi : PRep n w Bi gB⁻¹)
  {mx cap R : Nat} {BlL P Lb SL : List Nat} (hBl : ∀ x ∈ BlL, x < 2 ^ (n * w))
  (hS : ∀ x ∈ SL, x < 2 ^ (n * w))
  (hc : clsOK n w (mask w) (n * w) (mask (n * w)) A Ai B Bi mx cap R (packL (n * w) BlL) P Lb
    (packL (n * w) SL) (lenN SL) = true)
  {r : Equiv.Perm (Fin n)} (pR : PRep n w R r) (hpos : 0 < SL.length)
include hn hw pA pAi pB pBi hBl hS hc pR hpos

theorem list_class :
    (CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r).ncard = SL.length ∧
    ∀ z, z ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r ↔
        ∃ k < SL.length, PRep n w (SL.getD k 0) z := by
  set K := Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))
  set c := SL.length
  obtain ⟨-, -, h0, hinc1, hcl, htree, hmask⟩ := clsOK_facts hBl hS hc
  have hAK : gA ∈ K := Subgroup.subset_closure (by simp)
  have hBK : gB ∈ K := Subgroup.subset_closure (by simp)
  have hBLc : ∀ k < c, ∃ z ∈ CFSG.Sporadic.SmallOddCore.conjClass K r,
      PRep n w (BlL.getD k 0) z := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        refine ⟨r, ⟨1, K.one_mem, by simp⟩, ?_⟩
        rw [h0]
        exact pR
      · obtain ⟨hp, he⟩ := htree k hk hk0
        obtain ⟨z, hz, pz⟩ := ih _ hp (by omega)
        rw [he]
        split
        · exact ⟨gA * z * gA⁻¹, conj_mem_conjClass hAK hz, prep_conjK hn pA pAi pz⟩
        · exact ⟨gB * z * gB⁻¹, conj_mem_conjClass hBK hz, prep_conjK hn pB pBi pz⟩
  set q : Nat → Nat := fun k =>
    bpos (n * w) (mask (n * w)) (packL (n * w) SL) c (BlL.getD k 0) 32 0 c
  have hq := mask_facts hmask
  have hqv : ∀ k < c, SL.getD (q k) 0 = BlL.getD k 0 := fun k hk => by
    rw [← blk_packL hS]
    exact bpos_sound _ _ _ _ _ _ _ _ (hq k hk).1
  have hsurj : ∀ s < c, ∃ k < c, q k = s := by
    intro s hs
    let f : Fin c → Fin c := fun k => ⟨q k, (hq k k.2).1⟩
    have hf : Function.Injective f := fun a b e => by
      have e' : q a = q b := congrArg Fin.val e
      rcases Nat.lt_trichotomy a b with h | h | h
      · exact absurd e' ((hq b b.2).2 a h)
      · exact Fin.ext h
      · exact absurd e'.symm ((hq a a.2).2 b h)
    obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hf) ⟨s, hs⟩
    exact ⟨k, k.2, congrArg Fin.val hk⟩
  have hSc : ∀ s < c, ∃ z ∈ CFSG.Sporadic.SmallOddCore.conjClass K r,
      PRep n w (SL.getD s 0) z := by
    intro s hs
    obtain ⟨k, hk, rfl⟩ := hsurj s hs
    rw [hqv k hk]
    exact hBLc k hk
  have hshr : ∀ s, SL.getD s 0 >>> (n * w) = 0 := fun s => shr_of_lt (getD_lt hS s)
  have hinc := lt_of_consec (c := c) (ST := fun k => SL.getD k 0) hinc1
  have hmem : ∀ z, z ∈ CFSG.Sporadic.SmallOddCore.conjClass K r ↔
      ∃ k < c, PRep n w (SL.getD k 0) z := by
    intro z
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine conj_closed (S := {z | ∃ k < c, PRep n w (SL.getD k 0) z}) ?_ g hg r
        ⟨q 0, (hq 0 hpos).1, by rw [hqv 0 hpos, h0]; exact pR⟩
      rintro g' hg' z ⟨k, hk, pz⟩
      obtain ⟨hmA, hmB⟩ := hcl k hk
      rcases hg' with rfl | hg'
      · obtain ⟨k', hk', e⟩ := bmem_sound hmA
        rw [blk_packL hS] at e
        exact ⟨k', hk', by rw [e]; exact prep_conjK hn pA pAi pz⟩
      · rw [Set.mem_singleton_iff] at hg'
        subst hg'
        obtain ⟨k', hk', e⟩ := bmem_sound hmB
        rw [blk_packL hS] at e
        exact ⟨k', hk', by rw [e]; exact prep_conjK hn pB pBi pz⟩
    · rintro ⟨k, hk, pz⟩
      obtain ⟨z', hz', pz'⟩ := hSc k hk
      rw [prep_unique pz pz']
      exact hz'
  refine ⟨?_, hmem⟩
  refine Set.ncard_eq_of_bijective (fun k hk => Classical.choose (hSc k hk))
    (fun z hz => ?_) (fun k hk => (Classical.choose_spec (hSc k hk)).1) (fun i j hi hj e => ?_)
  · obtain ⟨k, hk, pz⟩ := (hmem z).1 hz
    exact ⟨k, hk, prep_unique (Classical.choose_spec (hSc k hk)).2 pz⟩
  · have p1 := (Classical.choose_spec (hSc i hi)).2
    have p2 := (Classical.choose_spec (hSc j hj)).2
    rw [e] at p1
    have eq : SL.getD i 0 = SL.getD j 0 := PF.eq_of_fields hw (hshr i) (hshr j) fun t ht => by
      rw [p1 ⟨t, ht⟩, p2 ⟨t, ht⟩]
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd eq (Nat.ne_of_lt (hinc i j h hj))
    · exact h
    · exact absurd eq (Nat.ne_of_gt (hinc j i h hi))

end Datum

theorem allC_iff (f : ClassDatum → Bool) :
    ∀ CL : List ClassDatum, allC f CL = true ↔ ∀ d ∈ CL, f d = true
  | [] => by simp [allC]
  | d :: CL => by
    change bAnd(f d, allC f CL) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, allC_iff f CL, List.forall_mem_cons]

theorem clsSize_eq : ∀ CL : List ClassDatum, clsSize CL = (CL.map (·.2.2.2.2.2.2.length)).sum
  | [] => rfl
  | d :: CL => by
    change Nat.add (lenN d.2.2.2.2.2.2) (clsSize CL) = _
    rw [lenN_eq', clsSize_eq CL, List.map_cons, List.sum_cons]
    rfl

theorem clsOneR_eq (n w : Nat) (tA tB : List Nat) (mx cap a b R : Nat) (BlL P Lb SL : List Nat) :
    clsOneR n w tA tB mx cap (a, b, R, BlL, P, Lb, SL) =
      (allLtN (Nat.shiftLeft 1 (n * w)) BlL && allLtN (Nat.shiftLeft 1 (n * w)) SL &&
        clsOK n w (mask w) (n * w) (mask (n * w)) (packL w tA) (pinvS n w (mask w) (packL w tA))
          (packL w tB) (pinvS n w (mask w) (packL w tB)) mx cap R (packL (n * w) BlL) P Lb
          (packL (n * w) SL) (lenN SL)) := by
  unfold clsOneR
  simp only [Orb.strictB_eq, bAnd_eq, Nat.mul_eq, Bool.and_assoc]

theorem clsDisj_spec (n w : Nat) : ∀ CL : List ClassDatum, clsDisj n w CL = true →
    ∀ i j (hi : i < CL.length) (hj : j < CL.length), i < j →
      bmem (n * w) (mask (n * w)) (packL (n * w) CL[i].2.2.2.2.2.2)
        (lenN CL[i].2.2.2.2.2.2) CL[j].2.2.1 = false
  | [], _ => fun i j hi => absurd hi (Nat.not_lt_zero _)
  | d :: CL, h => by
    have e : clsDisj n w (d :: CL) = (allC (fun e => !bmem (n * w) (mask (n * w))
        (packL (n * w) d.2.2.2.2.2.2) (lenN d.2.2.2.2.2.2) e.2.2.1) CL && clsDisj n w CL) := by
      obtain ⟨a, b, R, Bl, P, Lb, S⟩ := d
      unfold clsDisj
      simp only [Orb.strictB_eq, bAnd_eq]
      congr 1
    rw [e, Bool.and_eq_true, allC_iff] at h
    intro i j hi hj hij
    rcases i with _ | i
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j' < CL.length := by simpa using hj
      have := h.1 CL[j'] (List.getElem_mem hj')
      simpa using this
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact clsDisj_spec n w CL h.2 i j' (by simpa using hi) (by simpa using hj) (by omega)

theorem datum_facts {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat} (hA : tA = imageList gA)
    (hB : tB = imageList gB) (hsz : szOK n w = true) {mx cap : Nat} {d : ClassDatum}
    (hc : clsOneR n w tA tB mx cap d = true) (hpos : 0 < d.2.2.2.2.2.2.length)
    {r : Equiv.Perm (Fin n)} (pR : PRep n w d.2.2.1 r) :
    (CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r).ncard =
        d.2.2.2.2.2.2.length ∧ d.2.2.2.2.2.2.length ≤ cap ∧ orderOf r = mx ∧
    (∀ z, z ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r ↔
        ∃ k < d.2.2.2.2.2.2.length, PRep n w (d.2.2.2.2.2.2.getD k 0) z) ∧
    (∀ i j, i < j → j < d.2.2.2.2.2.2.length →
      d.2.2.2.2.2.2.getD i 0 < d.2.2.2.2.2.2.getD j 0) ∧
    (∀ x ∈ d.2.2.2.2.2.2, x < 2 ^ (n * w)) ∧ d.2.2.1 < 2 ^ (n * w) := by
  obtain ⟨a, b, R, BlL, P, Lb, SL⟩ := d
  simp only at hpos pR ⊢
  subst hA hB
  have hf := szOK_facts hsz
  have hn := szOK_lt hsz
  have hw := PF.w_pos hf.2
  have hwn : n < 2 ^ w := by omega
  have pA := (prep_packL (g := gA) hf.2).1
  have pB := (prep_packL (g := gB) hf.2).1
  rw [clsOneR_eq, Bool.and_eq_true, Bool.and_eq_true, allLtN_iff, allLtN_iff] at hc
  obtain ⟨⟨hBl, hS⟩, hc⟩ := hc
  have e : Nat.shiftLeft 1 (n * w) = 2 ^ (n * w) := by rw [Orb.shl_eq', Nat.one_mul]
  rw [e] at hBl hS
  have hcl := list_class hn hw pA (prep_pinvS hwn pA).1 pB (prep_pinvS hwn pB).1 hBl hS hc pR hpos
  obtain ⟨h1, h2, h3, h4, -⟩ := clsOK_facts hBl hS hc
  refine ⟨hcl.1, h1, (orderOf_of_ordC pR).trans h2, hcl.2,
    lt_of_consec (c := SL.length) (ST := fun k => SL.getD k 0) h4, hS, ?_⟩
  rw [← h3]
  exact getD_lt hBl 0

theorem chainK_reps' {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat}
    (hA : tA = imageList gA) (hB : tB = imageList gB) (hsz : szOK n w = true)
    {mx cap : Nat} {CL : List ClassDatum} {reps : List (Equiv.Perm (Fin n))} {X : List Table}
    (hcls : allC (clsOneR n w tA tB mx cap) CL = true) (hdisj : clsDisj n w CL = true)
    (hR : reps.length = CL.length ∧ ∀ j < CL.length,
      imageList (reps.getD j 1) = (unpack n w (CL.getD j (0, 0, 0, [], [], [], [])).2.2.1).toList)
    (hmx : 0 < mx) (hX : X.length = clsSize CL)
    (hne : allC (fun d => Nat.blt 0 (lenN d.2.2.2.2.2.2)) CL = true) (hcap : cap ≤ 2 ^ 32) :
    repsOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) X (reps.map toTable) cap = true ∧
      repSizes n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable) cap =
        CL.map (fun d => d.2.2.2.2.2.2.length) ∧
      (reps.map toTable).all (ordTest n mx) = true := by
  set d0 : ClassDatum := (0, 0, 0, [], [], [], [])
  have hn := szOK_lt hsz
  have hw := PF.w_pos (szOK_facts hsz).2
  rw [allC_iff] at hcls hne
  have hlen := hR.1
  have hRj : ∀ j (hj : j < reps.length), PRep n w (CL.getD j d0).2.2.1 reps[j] := fun j hj => by
    have := prep_of_imageList (hR.2 j (hlen ▸ hj))
    rwa [List.getD_eq_getElem _ 1 hj] at this
  have hmem : ∀ j (hj : j < reps.length), CL.getD j d0 ∈ CL := fun j hj => by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hj)]
    exact List.getElem_mem _
  have hpos : ∀ j (hj : j < reps.length), 0 < (CL.getD j d0).2.2.2.2.2.2.length := fun j hj => by
    have := hne _ (hmem j hj)
    rwa [Nat.blt_eq, lenN_eq'] at this
  have hF := fun j (hj : j < reps.length) =>
    datum_facts hA hB hsz (hcls _ (hmem j hj)) (hpos j hj) (hRj j hj)
  have hmap := range_map_getD (d0 := d0) (fun d : ClassDatum => d.2.2.2.2.2.2.length) hlen
  rw [clsSize_eq, ← hmap] at hX
  rw [← hmap]
  refine reps_of_classes hn (sz := fun j => (CL.getD j d0).2.2.2.2.2.2.length)
    (fun j hj => ⟨(hF j hj).1, (hF j hj).2.1, (hF j hj).2.2.1⟩) (fun i j hi hj hij hrj => ?_) hmx hX
  obtain ⟨-, hci, -, hmi, hinci, hSi, -⟩ := hF i hi
  obtain ⟨-, -, -, -, -, -, hRlt⟩ := hF j hj
  obtain ⟨k, hk, pk⟩ := (hmi _).1 hrj
  have hdj := clsDisj_spec n w CL hdisj i j (hlen ▸ hi) (hlen ▸ hj) hij
  rw [← List.getD_eq_getElem _ d0 (hlen ▸ hi), ← List.getD_eq_getElem _ d0 (hlen ▸ hj),
    lenN_eq'] at hdj
  refine bmem_complete (hci.trans hcap) (fun a b hab hb => ?_) hdj k hk ?_
  · rw [blk_packL hSi, blk_packL hSi]
    exact hinci a b hab hb
  · rw [blk_packL hSi]
    exact PF.eq_of_fields hw (shr_of_lt (getD_lt hSi k)) (shr_of_lt hRlt) fun t ht => by
      rw [pk ⟨t, ht⟩, hRj j hj ⟨t, ht⟩]

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem chainK_repsTotal' (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w (gens) words bv PS PSI LR TR TRI kS BP NS CH)
    {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat}
    (hA : tA = imageList gA) (hB : tB = imageList gB) (hk : 0 < k)
    {mx my cap : Nat} {CL : List ClassDatum} {reps : List (Equiv.Perm (Fin n))}
    {ws : List (List Nat × Nat)} (hcls : allC (clsOneR n w tA tB mx cap) CL = true)
    (hR : reps.length = CL.length ∧ ∀ j < CL.length,
      imageList (reps.getD j 1) = (unpack n w (CL.getD j (0, 0, 0, [], [], [], [])).2.2.1).toList)
    (hmy : 0 < my) {CW : List (List Nat)}
    (hCW : CW.length = CL.length ∧ ∀ j < CL.length, (CW.getD j []).length = rcnt (LR 0) ∧
      ∀ k₀ < rcnt (LR 0), cntWordK n w (mask w) (n * w) (pidn n w) LR TR k mx my ws
        (CL.getD j (0, 0, 0, [], [], [], [])).2.2.1 k₀ = (CW.getD j []).getD k₀ 0)
    (hne : allC (fun d => Nat.blt 0 (lenN d.2.2.2.2.2.2)) CL = true) :
    repsTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable)
        (orderTables (certificate hn gens words bv hbs) my) cap (wordsTest n mx my ws) =
      ((List.range CL.length).map fun j =>
        (CL.getD j (0, 0, 0, [], [], [], [])).2.2.2.2.2.2.length * (CW.getD j []).sum).sum := by
  set d0 : ClassDatum := (0, 0, 0, [], [], [], [])
  have hsz := chainK_szOK hQ
  have h32 := szOK_lt hsz
  rw [allC_iff] at hcls hne
  have hlen := hR.1
  have hRj : ∀ j (hj : j < reps.length), PRep n w (CL.getD j d0).2.2.1 reps[j] := fun j hj => by
    have := prep_of_imageList (hR.2 j (hlen ▸ hj))
    rwa [List.getD_eq_getElem _ 1 hj] at this
  have hmem : ∀ j (hj : j < reps.length), CL.getD j d0 ∈ CL := fun j hj => by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hj)]
    exact List.getElem_mem _
  have hpos : ∀ j (hj : j < reps.length), 0 < (CL.getD j d0).2.2.2.2.2.2.length := fun j hj => by
    have := hne _ (hmem j hj)
    rwa [Nat.blt_eq, lenN_eq'] at this
  have hF := fun j (hj : j < reps.length) =>
    datum_facts hA hB hsz (hcls _ (hmem j hj)) (hpos j hj) (hRj j hj)
  refine repsTotal_eq hlen (fun j hj => ?_) (fun j hj => ?_)
  · have hg := rep_pair h32 gA gB
    have hgK := genK_pair gA gB
    have hcap : (CFSG.Sporadic.SmallOddCore.conjClass (genK (pairTables gA gB)
        (fun l => if l = 0 then gA else gB)) reps[j]).ncard ≤ cap := by
      rw [hgK, (hF j hj).1]
      exact (hF j hj).2.1
    rw [conjClosure_size hg (rep_toTable h32 reps[j]) hcap, hgK, (hF j hj).1]
  · have hj' : j < CL.length := hlen ▸ hj
    exact countWord' hQ hn hbs (hRj j hj) hmy ws hk (hCW.2 j hj').1 (hCW.2 j hj').2

theorem chainK_repsTotal2' (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w (gens) words bv PS PSI LR TR TRI kS BP NS CH)
    {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat}
    (hA : tA = imageList gA) (hB : tB = imageList gB) (hk : 2 ≤ k)
    {mx my cap : Nat} {CL : List ClassDatum} {reps : List (Equiv.Perm (Fin n))}
    {ws : List (List Nat × Nat)} (hcls : allC (clsOneR n w tA tB mx cap) CL = true)
    (hR : reps.length = CL.length ∧ ∀ j < CL.length,
      imageList (reps.getD j 1) = (unpack n w (CL.getD j (0, 0, 0, [], [], [], [])).2.2.1).toList)
    (hmy : 0 < my) {CW : List (List (List Nat))}
    (hCW : CW.length = CL.length ∧ ∀ j < CL.length, Cnt2 LR (CW.getD j [])
      (cntWord2K n w (mask w) (n * w) (pidn n w) LR TR k mx my ws
        (CL.getD j (0, 0, 0, [], [], [], [])).2.2.1))
    (hne : allC (fun d => Nat.blt 0 (lenN d.2.2.2.2.2.2)) CL = true) :
    repsTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable)
        (orderTables (certificate hn gens words bv hbs) my) cap (wordsTest n mx my ws) =
      ((List.range CL.length).map fun j =>
        (CL.getD j (0, 0, 0, [], [], [], [])).2.2.2.2.2.2.length *
          ((CW.getD j []).map List.sum).sum).sum := by
  set d0 : ClassDatum := (0, 0, 0, [], [], [], [])
  have hsz := chainK_szOK hQ
  have h32 := szOK_lt hsz
  rw [allC_iff] at hcls hne
  have hlen := hR.1
  have hRj : ∀ j (hj : j < reps.length), PRep n w (CL.getD j d0).2.2.1 reps[j] := fun j hj => by
    have := prep_of_imageList (hR.2 j (hlen ▸ hj))
    rwa [List.getD_eq_getElem _ 1 hj] at this
  have hmem : ∀ j (hj : j < reps.length), CL.getD j d0 ∈ CL := fun j hj => by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hj)]
    exact List.getElem_mem _
  have hpos : ∀ j (hj : j < reps.length), 0 < (CL.getD j d0).2.2.2.2.2.2.length := fun j hj => by
    have := hne _ (hmem j hj)
    rwa [Nat.blt_eq, lenN_eq'] at this
  have hF := fun j (hj : j < reps.length) =>
    datum_facts hA hB hsz (hcls _ (hmem j hj)) (hpos j hj) (hRj j hj)
  refine repsTotal_eq hlen (fun j hj => ?_) (fun j hj => ?_)
  · have hg := rep_pair h32 gA gB
    have hgK := genK_pair gA gB
    have hcap : (CFSG.Sporadic.SmallOddCore.conjClass (genK (pairTables gA gB)
        (fun l => if l = 0 then gA else gB)) reps[j]).ncard ≤ cap := by
      rw [hgK, (hF j hj).1]
      exact (hF j hj).2.1
    rw [conjClosure_size hg (rep_toTable h32 reps[j]) hcap, hgK, (hF j hj).1]
  · have hj' : j < CL.length := hlen ▸ hj
    exact countWord2' hQ hn hbs (hRj j hj) hmy ws hk (hCW.2 j hj')

end CFSG.KS.SporSch.MOC

end
