module

public import CFSG.Certificates.Kernel.SmithL6KGSound
public import CFSG.Certificates.Kernel.SmithL6CollSound
public import Certificates.Data.Kernel.SmithL6KW
public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel CFSG.SmithL6.CollK
open CFSG.SmithE (tri applyCols)

theorem tvA_lt64 {p : Nat × Nat} (hp : TvP p) {x : Nat} (hx : x < 64) : tvA p x < 64 := by
  unfold tvA
  split
  · exact xor_lt64 hx hp.1
  · exact hx

theorem form_conjP_snd (p q : Nat × Nat) (x : Nat) :
    form (conjP p q).2 x = form q.2 (tvA p x) := by
  obtain ⟨w, ψ⟩ := p
  obtain ⟨v, φ⟩ := q
  unfold conjP tvA
  simp only
  cases hφw : form φ w <;> cases hψx : form ψ x <;>
    simp [form_xor_left, form_xor_right, hφw, hψx]

theorem setM_imgMaskK {p : Nat × Nat} (hp : TvP p) (M : Nat) :
    setM (imgMaskK (codeOf p) M) = (setM M).image (tvA p) := by
  unfold imgMaskK
  rw [codeOf_div hp, codeOf_mod hp]
  ext y
  rw [mem_setM, Finset.mem_image]
  have e := foldl_or_testBit (fun x => tvA (p.1, p.2) x) (fun x => M.testBit x) (List.range 64) 0 y
  simp only [Nat.zero_testBit, Bool.false_or] at e
  rw [e, List.any_eq_true]
  have hp' : (p.1, p.2) = p := rfl
  simp only [hp', List.mem_range, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨-, x, hx, hM, rfl⟩
    exact ⟨x, mem_setM.mpr ⟨hx, hM⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx64, hM⟩ := mem_setM.mp hx
    exact ⟨tvA_lt64 hp hx64, x, hx64, hM, rfl⟩

theorem wt_lt20K (i : Nat) : wt i < 2 ^ 20 := by
  unfold wt
  generalize wB i = p
  obtain ⟨a, b, c⟩ := p
  exact wedge3_lt20 a b c

@[expose] def Clo (k : Nat) : Prop :=
  ∀ i < 1395, ∃ j < 1395, wt j = applyCols (tvCols k) (wt i) ∧
    setM (wMask j) = (setM (wMask i)).image (tvApply k)

theorem clo_tvImg {g u : Nat} (hg : g < 1953) (hu : u < 1953) (Cg : Clo g) (Cu : Clo u) :
    Clo (tvImg g u) := by
  intro i hi
  obtain ⟨j1, hj1, w1, m1⟩ := Cg i hi
  obtain ⟨j2, hj2, w2, m2⟩ := Cu j1 hj1
  obtain ⟨j3, hj3, w3, m3⟩ := Cg j2 hj2
  refine ⟨j3, hj3, ?_, ?_⟩
  · rw [w3, w2, w1, tvCols_tvImg hg hu _ (wt_lt20K i)]
  · rw [m3, m2, m1, Finset.image_image, Finset.image_image]
    exact congrArg (fun f => Finset.image f (setM (wMask i)))
      (funext fun x => (tvApply_tvImg hg hu x).symm)

theorem clo_of_closeRowK {g R W M : Nat} (hg : g < 1953) (hW : ∀ i < 1395, fldW 20 W i = wt i)
    (hM : ∀ i < 1395, fldW 64 M i = wMask i)
    (h : closeRowK (tvCols g).toList (codeOf (tvPair g)) R W M = true) : Clo g := by
  intro i hi
  unfold closeRowK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hj, hw⟩, hm⟩ := h i hi
  refine ⟨_, hj, ?_, ?_⟩
  · rw [← hW _ hj, hw, hW i hi, ← applyCols_toArray, Array.toArray_toList]
  · rw [← hM _ hj, hm, hM i hi, setM_imgMaskK (tvP_tvPair hg)]
    exact congrArg (fun f => Finset.image f (setM (wMask i)))
      (funext fun x => (tvApply_eq_tvA g x).symm)

theorem chkTW_of {G : List Nat} (hG : ∀ s < G.length, G.getD s 0 < 1953)
    (hG0 : G.getD 0 1 = 0) (hR : Reach 1953 G.length (· == 0)
      (fun s u v => tvImg (G.getD s 0) u == v))
    (hclo : ∀ s < G.length, Clo (G.getD s 0))
    (hinj : ∀ i < 1395, ∀ j < 1395, wt i = wt j → i = j)
    (hann : ∀ j < 1395, setM (annArr[j]!) = annS (setM (wMask j))) :
    chkTW = true := by
  have hlen : 0 < G.length := by
    rcases G with _ | ⟨g, G⟩
    · simp at hG0
    · simp
  have hgd : G.getD 0 0 = 0 := by
    rcases G with _ | ⟨g, G⟩
    · simp at hlen
    · simpa using hG0
  have hall := reach_gens hR Clo (hgd ▸ hclo 0 hlen)
    fun s hs u hu hP => clo_tvImg (hG s hs) hu (hclo s hs) hP
  unfold chkTW
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc]
  intro k hk i hi
  obtain ⟨j, hj, hw, hm⟩ := hall k hk i hi
  have hpi : planeImg k i = j := by
    unfold planeImg wtIdx
    rw [tvArr_get hk, wtArr_get hi, ← hw]
    exact foldl_set_last (f := fun j => wtArr[j]!) (wt_lt20K j) hj (wtArr_get hj)
      fun j' h1 h2 e => by
        rw [wtArr_get h2] at e
        have := hinj j' h2 j hj e
        omega
  rw [hpi]
  refine ⟨hj, by rw [wtArr_get hj, tvArr_get hk, wtArr_get hi]; exact hw, ?_⟩
  rw [planePtsArr_get hi]
  unfold planePts
  rw [List.all_toArray, List.all_eq_true]
  intro a ha
  rw [List.mem_filter, List.mem_range] at ha
  obtain ⟨ha1, ha2⟩ := ha
  rw [tvTab_get hk ha1, flagArr_get hj (tvImg_lt hk ha1)]
  unfold inPlane at ha2 ⊢
  rw [maskArr_get hi] at ha2
  rw [maskArr_get hj, tvPair_tvImg hk ha1]
  rw [Bool.and_eq_true] at ha2 ⊢
  have hp := tvP_tvPair hk
  have hq := tvP_tvPair ha1
  have hv : (tvPair a).1 ∈ setM (wMask i) := mem_setM.mpr ⟨hq.1, ha2.1⟩
  have hφ : (tvPair a).2 ∈ annS (setM (wMask i)) := by
    rw [← hann i hi]
    exact mem_setM.mpr ⟨hq.2.1, ha2.2⟩
  constructor
  · have h1 : tvA (tvPair k) (tvPair a).1 ∈ setM (wMask j) := by
      rw [hm]
      exact Finset.mem_image.mpr ⟨_, hv, tvApply_eq_tvA _ _⟩
    exact (mem_setM.mp h1).2
  · have h2 : (conjP (tvPair k) (tvPair a)).2 ∈ annS (setM (wMask j)) := by
      rw [mem_annS]
      refine ⟨(conjP_tvP hp hq).2.1, fun y hy => ?_⟩
      rw [hm, Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [form_conjP_snd, ← tvApply_eq_tvA, tvApply_tvApply hk]
      exact (mem_annS.mp hφ).2 x hx
    rw [← hann j hj] at h2
    exact (mem_setM.mp h2).2

theorem fldP_eq (w m T s : Nat) (hm : m = 2 ^ w - 1) : fldP w m T s = fldW w T s := by
  unfold fldP fldW
  rw [hm]
  exact Nat.and_two_pow_sub_one_eq_mod _ w

theorem apB_eq (T : List Nat) (x : Nat) : apB T x = apK T x := by
  induction T generalizing x with
  | nil => rfl
  | cons c l ih =>
    change Bool.rec (motive := fun _ => Nat) (apB l (Nat.shiftRight x 1))
      (Nat.xor c (apB l (Nat.shiftRight x 1))) (Nat.beq (Nat.land x 1) 1) =
      (if x % 2 = 1 then c ^^^ apK l (x / 2) else apK l (x / 2))
    have e1 : Nat.shiftRight x 1 = x / 2 := Nat.shiftRight_eq_div_pow x 1
    have e2 : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
    rw [ih, e1, e2]
    cases hb : Nat.beq (x % 2) 1
    · have h : ¬ x % 2 = 1 := fun h => by rw [h] at hb; simp at hb
      simp [h]
    · simp [Nat.eq_of_beq_eq_true hb]

theorem swap_facts : ∀ b < 6, ∀ y < 64,
    (y.testBit b = false → y ^^^ 2 ^ b = 2 ^ b + y ∧ (2 ^ b ≤ y → (y - 2 ^ b).testBit b = true)) ∧
    (y.testBit b = true → 2 ^ b ≤ y ∧ y ^^^ 2 ^ b = y - 2 ^ b ∧ (y - 2 ^ b).testBit b = false) := by
  decide +kernel

theorem swp_body_testBit (b L m y : Nat) (hb : b < 6) (hy : y < 64)
    (hL : ∀ z < 64, L.testBit z = !z.testBit b) :
    (Nat.lor (Nat.land (Nat.shiftRight m (Nat.shiftLeft 1 b)) L)
      (Nat.shiftLeft (Nat.land m L) (Nat.shiftLeft 1 b))).testBit y =
      m.testBit (y ^^^ 2 ^ b) := by
  have e : Nat.shiftLeft 1 b = 2 ^ b := Nat.one_shiftLeft b
  rw [e]
  change (((m >>> 2 ^ b) &&& L) ||| ((m &&& L) <<< 2 ^ b)).testBit y = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.testBit_and, hL y hy]
  obtain ⟨hf, ht⟩ := swap_facts b hb y hy
  cases hyb : y.testBit b
  · obtain ⟨e1, e2⟩ := hf hyb
    rw [e1]
    by_cases hs : 2 ^ b ≤ y
    · rw [hL (y - 2 ^ b) (by omega), e2 hs]
      simp
    · simp [hs]
  · obtain ⟨hs, e1, e2⟩ := ht hyb
    rw [e1, hL (y - 2 ^ b) (by omega), e2]
    simp [hs]

theorem swpB_testBit (v b L m y : Nat) (hb : b < 6) (hy : y < 64)
    (hL : ∀ z < 64, L.testBit z = !z.testBit b) :
    (swpB v b L m).testBit y = m.testBit (y ^^^ vpart v b) := by
  unfold swpB vpart
  cases vbit v b
  · exact congrArg m.testBit (Nat.xor_zero y).symm
  · have e : Nat.shiftLeft 1 b = 2 ^ b := Nat.one_shiftLeft b
    change (Nat.lor (Nat.land (Nat.shiftRight m (Nat.shiftLeft 1 b)) L)
      (Nat.shiftLeft (Nat.land m L) (Nat.shiftLeft 1 b))).testBit y =
      m.testBit (y ^^^ Nat.shiftLeft 1 b)
    rw [swp_body_testBit b L m y hb hy hL, e]

theorem xor_vpart_lt {z : Nat} (hz : z < 64) (v : Nat) {b : Nat} (hb : b < 6) :
    z ^^^ vpart v b < 64 := by
  unfold vpart
  cases vbit v b
  · change z ^^^ 0 < 64
    rw [Nat.xor_zero]
    exact hz
  · have e : Nat.shiftLeft 1 b = 2 ^ b := Nat.one_shiftLeft b
    change z ^^^ Nat.shiftLeft 1 b < 64
    rw [e]
    exact xor_lt64 hz (Nat.pow_lt_pow_right (by decide : 1 < 2) hb : 2 ^ b < 2 ^ 6)

theorem vpart_sum : ∀ v < 64, vpart v 5 ^^^ (vpart v 4 ^^^ (vpart v 3 ^^^ (vpart v 2 ^^^
    (vpart v 1 ^^^ vpart v 0)))) = v := by
  decide +kernel

theorem xorMask_testBit {v : Nat} (hv : v < 64) (m : Nat) {y : Nat} (hy : y < 64) :
    (xorMask v m).testBit y = m.testBit (y ^^^ v) := by
  have L0 : ∀ z < 64, (0x5555555555555555 : Nat).testBit z = !z.testBit 0 := by decide +kernel
  have L1 : ∀ z < 64, (0x3333333333333333 : Nat).testBit z = !z.testBit 1 := by decide +kernel
  have L2 : ∀ z < 64, (0x0F0F0F0F0F0F0F0F : Nat).testBit z = !z.testBit 2 := by decide +kernel
  have L3 : ∀ z < 64, (0x00FF00FF00FF00FF : Nat).testBit z = !z.testBit 3 := by decide +kernel
  have L4 : ∀ z < 64, (0x0000FFFF0000FFFF : Nat).testBit z = !z.testBit 4 := by decide +kernel
  have L5 : ∀ z < 64, (0x00000000FFFFFFFF : Nat).testBit z = !z.testBit 5 := by decide +kernel
  have h5 := xor_vpart_lt hy v (b := 5) (by decide)
  have h4 := xor_vpart_lt h5 v (b := 4) (by decide)
  have h3 := xor_vpart_lt h4 v (b := 3) (by decide)
  have h2 := xor_vpart_lt h3 v (b := 2) (by decide)
  have h1 := xor_vpart_lt h2 v (b := 1) (by decide)
  unfold xorMask
  rw [swpB_testBit v 5 _ _ y (by decide) hy L5, swpB_testBit v 4 _ _ _ (by decide) h5 L4,
    swpB_testBit v 3 _ _ _ (by decide) h4 L3, swpB_testBit v 2 _ _ _ (by decide) h3 L2,
    swpB_testBit v 1 _ _ _ (by decide) h2 L1, swpB_testBit v 0 _ _ _ (by decide) h1 L0]
  simp only [Nat.xor_assoc, vpart_sum v hv]

theorem kerMask_testBit (φ y : Nat) : (kerMask φ).testBit y = (decide (y < 64) && !form φ y) := by
  unfold kerMask
  have e := foldl_or_testBit (fun d => d) (fun d => !form φ d) (List.range 64) 0 y
  simp only [Nat.zero_testBit, Bool.false_or] at e
  rw [e, Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, h, rfl⟩
    exact ⟨hx, h⟩
  · rintro ⟨hy, h⟩
    exact ⟨y, hy, h, rfl⟩

theorem imgMaskB_eq {p : Nat × Nat} (hp : TvP p) (M : Nat) :
    imgMaskB (codeOf p) (kerMask (codeOf p % 64)) M = imgMaskK (codeOf p) M := by
  have hv : Nat.shiftRight (codeOf p) 6 = p.1 := by
    change codeOf p >>> 6 = p.1
    rw [Nat.shiftRight_eq_div_pow]
    exact codeOf_div hp
  have hF : ∀ y, (0xFFFFFFFFFFFFFFFF : Nat).testBit y = decide (y < 64) := by
    intro y
    by_cases hy : y < 64
    · rw [decide_eq_true hy]
      revert y
      decide +kernel
    · rw [decide_eq_false hy]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
        (by decide : (0xFFFFFFFFFFFFFFFF : Nat) < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide : 2 > 0) (Nat.le_of_not_lt hy)))
  have hany : ∀ y, ((List.range 64).any fun x => M.testBit x && tvA (p.1, p.2) x == y) =
      (decide (y < 64) && M.testBit (tvA p y)) := by
    intro y
    rw [Bool.eq_iff_iff, List.any_eq_true]
    simp only [List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, hM, rfl⟩
      exact ⟨tvA_lt64 hp hx, by rw [tvA_tvA hp]; exact hM⟩
    · rintro ⟨hy, hM⟩
      exact ⟨tvA p y, tvA_lt64 hp hy, hM, tvA_tvA hp y⟩
  apply Nat.eq_of_testBit_eq
  intro y
  unfold imgMaskB
  rw [hv, codeOf_mod hp]
  unfold imgMaskK
  rw [codeOf_div hp, codeOf_mod hp]
  have e := foldl_or_testBit (fun x => tvA (p.1, p.2) x) (fun x => M.testBit x) (List.range 64) 0 y
  simp only [Nat.zero_testBit, Bool.false_or] at e
  rw [e, hany]
  change ((M &&& kerMask p.2) ||| (xorMask p.1 M &&& (kerMask p.2 ^^^ 0xFFFFFFFFFFFFFFFF))).testBit y = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, kerMask_testBit, hF]
  by_cases hy : y < 64
  · rw [xorMask_testBit hp.1 M hy]
    unfold tvA
    cases form p.2 y <;> simp [hy]
  · simp [hy]

theorem closeRowK_of_closeRowB {p : Nat × Nat} (hp : TvP p) {T : List Nat} {R W M : Nat}
    (h : closeRowB T (codeOf p) R W M = true) : closeRowK T (codeOf p) R W M = true := by
  have f11 : ∀ X s, fldP 11 2047 X s = fldW 11 X s := fun X s => fldP_eq 11 2047 X s (by decide)
  have f20 : ∀ X s, fldP 20 1048575 X s = fldW 20 X s :=
    fun X s => fldP_eq 20 1048575 X s (by decide)
  have f64 : ∀ X s, fldP 64 0xFFFFFFFFFFFFFFFF X s = fldW 64 X s :=
    fun X s => fldP_eq 64 0xFFFFFFFFFFFFFFFF X s (by decide)
  unfold closeRowB at h
  have h' := CFSG.KS.PK.allN_iff.1 h
  unfold closeRowK
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have hr := h' i hi
  unfold rowB at hr
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, f11, f20, f64, apB_eq,
    imgMaskB_eq hp] at hr
  obtain ⟨hj, hw, hm⟩ := hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hj, Nat.eq_of_beq_eq_true hw⟩, Nat.eq_of_beq_eq_true hm⟩

end CFSG.SmithL6.K
