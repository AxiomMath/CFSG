module

public import Certificates.Data.Kernel.WeylE8.TList
public import CFSG.Certificates.Kernel.LocalCompE8CentSound
public import CFSG.Certificates.Kernel.LocalCompAglSound
public import CFSG.Certificates.Kernel.LocalCompD8Sound

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.EvenSmallLie.OmegaEight

theorem allBlk_of {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_of (fun l hl => h l (Nat.lt_succ_of_lt hl))]

theorem rec_blocks_of {f : Nat → Bool} : ∀ {q : Nat},
    (∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true
  | 0, _ => rfl
  | q + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true
    rw [h q (Nat.lt_succ_self q), rec_blocks_of (fun h' hh => h h' (Nat.lt_succ_of_lt hh))]

theorem allN_of_forall {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) : allN n f = true := by
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true
  have hd := Nat.div_add_mod n 64
  rw [allBlk_of (fun l hl => h _ (by rw [e6, e64, Nat.add_eq]; rw [er] at hl; omega)),
    rec_blocks_of (fun q hq => allBlk_of (fun l hl => h _ (by
      have hl' : l < 64 := hl
      rw [e6, Nat.add_eq]; rw [e64] at hq; omega)))]

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  ⟨allN_spec, allN_of_forall⟩

theorem not_allN {n : Nat} {f : Nat → Bool} (h : notB' (allN n f) = true) :
    ∃ i < n, f i = false := by
  by_contra hc
  have : allN n f = true := allN_of_forall fun i hi => by
    cases e : f i
    · exact absurd ⟨i, hi, e⟩ hc
    · rfl
  rw [this] at h
  exact absurd h (by decide)

@[expose] noncomputable def codeL (c : ℕ) : List ℕ := (List.range 8).map (spAt c)

@[expose] def imgMaskC (l : List ℕ) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 8, if m.testBit j then 2 ^ l.getD j 0 else 0

@[expose] def compC (l l' : List ℕ) : List ℕ := (List.range 8).map fun j => l.getD (l'.getD j 0) 0

theorem spAt_eq (c j : ℕ) : spAt c j = c / 8 ^ j % 8 := by
  rw [spAt, pg3]
  rw [show (2 : ℕ) ^ (3 * j) = 8 ^ j by rw [pow_mul]; norm_num]

theorem spAt_lt (c j : ℕ) : spAt c j < 8 := by
  rw [spAt_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem spMask_eq (c : ℕ) : spMask c = c / 2 ^ 24 % 256 := by
  change (c >>> 24) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem codeL_length (c : ℕ) : (codeL c).length = 8 := by simp [codeL]

theorem codeL_getD (c : ℕ) {j : ℕ} (hj : j < 8) : (codeL c).getD j 0 = spAt c j := by
  rw [List.getD_eq_getElem _ _ (by rw [codeL_length]; exact hj)]
  simp [codeL]

theorem digit8 (v : ℕ → ℕ) (hv : ∀ j, v j < 8) (Y : ℕ) {k : ℕ} (hk : k < 8) :
    (sumN 8 (fun j => v j * 8 ^ j) + Y * 2 ^ 24) / 8 ^ k % 8 = v k := by
  rw [sumN8]
  have := hv 0
  have := hv 1
  have := hv 2
  have := hv 3
  have := hv 4
  have := hv 5
  have := hv 6
  have := hv 7
  interval_cases k <;> norm_num <;> omega

theorem high8 (v : ℕ → ℕ) (hv : ∀ j, v j < 8) (Y : ℕ) :
    (sumN 8 (fun j => v j * 8 ^ j) + Y * 2 ^ 24) / 2 ^ 24 = Y := by
  have hS : sumN 8 (fun j => v j * 8 ^ j) < 2 ^ 24 := by
    rw [sumN8]
    have := hv 0
    have := hv 1
    have := hv 2
    have := hv 3
    have := hv 4
    have := hv 5
    have := hv 6
    have := hv 7
    simp only [Nat.reducePow, pow_zero, pow_one]
    omega
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hS, zero_add]

theorem spMul_eq (a b : ℕ) : spMul a b =
    sumN 8 (fun j => spAt a (spAt b j) * 8 ^ j) +
      ((spMask a ^^^ spImgMask a (spMask b)) % 256) * 2 ^ 24 := by
  have h255 : ∀ x : ℕ, Nat.land x (nat_lit 255) = x % 256 := fun x =>
    Nat.and_two_pow_sub_one_eq_mod x 8
  have hs : ∀ x y : ℕ, Nat.shiftLeft x y = x * 2 ^ y := fun x y => Nat.shiftLeft_eq x y
  have hf : (fun j => Nat.shiftLeft (spAt a (spAt b j)) (Nat.mul (nat_lit 3) j)) =
      fun j => spAt a (spAt b j) * 8 ^ j := funext fun j => by
    rw [hs, Nat.mul_eq, pow_mul]
    norm_num
  unfold spMul
  rw [h255, hf, hs]
  rfl

theorem spAt_mul (a b : ℕ) {k : ℕ} (hk : k < 8) : spAt (spMul a b) k = spAt a (spAt b k) := by
  rw [spAt_eq (spMul a b), spMul_eq]
  exact digit8 (fun j => spAt a (spAt b j)) (fun j => spAt_lt _ _) _ hk

theorem codeL_mul (a b : ℕ) : codeL (spMul a b) = compC (codeL a) (codeL b) := by
  conv_lhs => rw [codeL]
  rw [compC]
  refine List.map_congr_left fun k hk' => ?_
  have hk : k < 8 := List.mem_range.1 hk'
  rw [spAt_mul a b hk, codeL_getD b hk, codeL_getD a (spAt_lt b k)]

theorem spImgMask_eq (a m : ℕ) : spImgMask a m = imgMaskC (codeL a) m := by
  rw [spImgMask, sumN_eq, imgMaskC]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj8 : j < 8 := Finset.mem_range.1 hj
  rw [codeL_getD a hj8]
  change Bool.rec (motive := fun _ => Nat) 0 (1 <<< spAt a j) (Nat.beq ((m >>> j) &&& 1) 1) = _
  rw [bit_eq]
  cases m.testBit j
  · rfl
  · exact Nat.one_shiftLeft _

theorem spMask_mul (a b : ℕ) :
    spMask (spMul a b) = (spMask a ^^^ imgMaskC (codeL a) (spMask b)) % 256 := by
  rw [spMask_eq (spMul a b), spMul_eq, high8 _ (fun j => spAt_lt _ _), spImgMask_eq]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))

theorem code_expand {c : ℕ} (hc : c < 2 ^ 32) :
    c = sumN 8 (fun j => spAt c j * 8 ^ j) + spMask c * 2 ^ 24 := by
  rw [sumN8]
  simp only [spAt_eq, spMask_eq]
  have h8 : ∀ x : ℕ, x / 8 ^ (1 + 1) = x / 8 / 8 := fun x => by
    rw [pow_succ, pow_one, Nat.div_div_eq_div_mul]
  simp only [pow_zero, pow_one, Nat.div_one, Nat.reducePow]
  omega

theorem eq_of_spMask_codeL {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hm : spMask a = spMask b)
    (hl : codeL a = codeL b) : a = b := by
  have hj : ∀ j < 8, spAt a j = spAt b j := fun j hj => by
    rw [← codeL_getD a hj, ← codeL_getD b hj, hl]
  rw [code_expand ha, code_expand hb, hm]
  rw [sumN8, sumN8, hj 0 (by norm_num), hj 1 (by norm_num), hj 2 (by norm_num),
    hj 3 (by norm_num), hj 4 (by norm_num), hj 5 (by norm_num), hj 6 (by norm_num),
    hj 7 (by norm_num)]

theorem permOKK_spec {c : ℕ} (h : permOKK c = true) : ∀ j < 8, j ∈ codeL c := by
  intro j hj
  have h1 := allN_spec h j hj
  obtain ⟨k, hk, hk'⟩ := not_allN h1
  rw [notB'_eq, Bool.not_eq_false'] at hk'
  rw [← Nat.eq_of_beq_eq_true hk']
  simp only [codeL, List.mem_map, List.mem_range]
  exact ⟨k, hk, rfl⟩

theorem okC_spec {c : ℕ} (h : okC c = true) :
    c < 2 ^ 32 ∧ (∀ j < 8, j ∈ codeL c) ∧ spMask c < 256 ∧ framePop (spMask c) % 2 = 0 := by
  have h' : (Nat.blt c 4294967296 && (permOKK c && evenB (spMask c))) = true := by
    simpa [okC, bAnd_eq] using h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨by simpa using h1, permOKK_spec h2, by rw [spMask_eq]; exact Nat.mod_lt _ (by norm_num), ?_⟩
  have h3' : (pop8 (spMask c) &&& 1) = 0 := Nat.eq_of_beq_eq_true h3
  rw [pop8_eq, Nat.and_one_is_mod] at h3'
  exact h3'

theorem e24_lt (P k : ℕ) : e24 P k < 2 ^ 24 := by
  change (P >>> (24 * k)) &&& (2 ^ 24 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem evenMaskK_lt {r : ℕ} (hr : r < 128) : evenMaskK r < 256 := by
  change 2 * r + (pop8 r &&& 1) < 256
  have : (pop8 r &&& 1) ≤ 1 := Nat.and_le_right
  omega

theorem tcK_eq (PP i : ℕ) : tcK PP i = e24 PP (i / 128) + evenMaskK (i % 128) * 2 ^ 24 := by
  change e24 PP (i >>> 7) + evenMaskK (i &&& (2 ^ 7 - 1)) <<< 24 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

theorem tcK_mask (PP : ℕ) {i : ℕ} : spMask (tcK PP i) = evenMaskK (i % 128) := by
  rw [spMask_eq, tcK_eq]
  have h1 := e24_lt PP (i / 128)
  have h2 := evenMaskK_lt (r := i % 128) (Nat.mod_lt _ (by norm_num))
  omega

theorem tcK_list (PP i : ℕ) : codeL (tcK PP i) = codeL (e24 PP (i / 128)) := by
  apply List.ext_getElem (by simp [codeL])
  intro k h1 _
  have hk : k < 8 := by simpa [codeL] using h1
  simp only [codeL, List.getElem_map, List.getElem_range, spAt_eq, tcK_eq]
  have h := e24_lt PP (i / 128)
  interval_cases k <;> norm_num <;> omega

theorem evenMaskK_eq (r : ℕ) : evenMaskK r = 2 * r + framePop r % 2 := by
  change 2 * r + (pop8 r &&& 1) = _
  rw [pop8_eq, Nat.and_one_is_mod]

theorem allN_eq_false {n k : Nat} {f : Nat → Bool} (hk : k < n) (h : f k = false) :
    allN n f = false :=
  Bool.eq_false_iff.2 fun e => by rw [allN_spec e k hk] at h; exact Bool.noConfusion h

theorem okC_of {c : ℕ} (h1 : c < 2 ^ 32) (h2 : ∀ j < 8, j ∈ codeL c)
    (h3 : framePop (spMask c) % 2 = 0) : okC c = true := by
  have hp : permOKK c = true := allN_of_forall fun j hj => by
    obtain ⟨k, hk, hkj⟩ : ∃ k < 8, spAt c k = j := by
      have := h2 j hj
      simp only [codeL, List.mem_map, List.mem_range] at this
      exact this
    rw [notB'_eq, Bool.not_eq_true']
    refine allN_eq_false hk ?_
    rw [notB'_eq, hkj, Nat.beq_refl]
    rfl
  have he : evenB (spMask c) = true := by
    change Nat.beq (pop8 (spMask c) &&& 1) 0 = true
    rw [pop8_eq, Nat.and_one_is_mod, h3]
    rfl
  change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (evenB (spMask c)) (permOKK c)) (Nat.blt c 4294967296) = true
  rw [hp, he]
  have : Nat.blt c 4294967296 = true := by simpa using h1
  rw [this]

theorem bitx (x y k : ℕ) :
    ((x ^^^ y) >>> k) &&& 1 = (((x >>> k) &&& 1) + ((y >>> k) &&& 1)) % 2 := by
  rw [Nat.and_one_is_mod, Nat.and_one_is_mod, Nat.and_one_is_mod, Nat.shiftRight_xor_distrib,
    Nat.xor_mod_two_eq, Nat.add_mod]

theorem bitx0 (x y : ℕ) : (x ^^^ y) &&& 1 = ((x &&& 1) + (y &&& 1)) % 2 := by
  have := bitx x y 0
  rwa [Nat.shiftRight_zero, Nat.shiftRight_zero, Nat.shiftRight_zero] at this

theorem framePop_xor (x y : ℕ) : framePop (x ^^^ y) % 2 = (framePop x + framePop y) % 2 := by
  unfold framePop
  rw [bitx0, bitx x y 1, bitx x y 2, bitx x y 3, bitx x y 4, bitx x y 5, bitx x y 6, bitx x y 7]
  have b : ∀ n : ℕ, n &&& 1 ≤ 1 := fun n => Nat.and_le_right
  generalize x &&& 1 = a0 at *
  generalize y &&& 1 = c0 at *
  generalize x >>> 1 &&& 1 = a1
  generalize y >>> 1 &&& 1 = c1
  generalize x >>> 2 &&& 1 = a2
  generalize y >>> 2 &&& 1 = c2
  generalize x >>> 3 &&& 1 = a3
  generalize y >>> 3 &&& 1 = c3
  generalize x >>> 4 &&& 1 = a4
  generalize y >>> 4 &&& 1 = c4
  generalize x >>> 5 &&& 1 = a5
  generalize y >>> 5 &&& 1 = c5
  generalize x >>> 6 &&& 1 = a6
  generalize y >>> 6 &&& 1 = c6
  generalize x >>> 7 &&& 1 = a7
  generalize y >>> 7 &&& 1 = c7
  omega

@[expose] def bitsum (c : Fin 8 → Bool) : ℕ := ∑ i : Fin 8, if c i then 2 ^ (i : ℕ) else 0

theorem bitsum_spec : ∀ c : Fin 8 → Bool, bitsum c < 256 ∧
    framePop (bitsum c) = ∑ i : Fin 8, if c i then 1 else 0 := by
  decide +kernel

theorem framePop_bits : ∀ m < 256, framePop m = ∑ i : Fin 8, if m.testBit i then 1 else 0 := by
  decide +kernel

theorem codeL_perm {c : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) :
    ∃ e : Equiv.Perm (Fin 8), ∀ j : Fin 8, (e j : ℕ) = spAt c j := by
  let f : Fin 8 → Fin 8 := fun j => ⟨spAt c j, spAt_lt c j⟩
  have hs : Function.Surjective f := fun i => by
    have := h2 i i.2
    simp only [codeL, List.mem_map, List.mem_range] at this
    obtain ⟨k, hk, hkj⟩ := this
    exact ⟨⟨k, hk⟩, Fin.ext hkj⟩
  have hb : Function.Bijective f := ⟨Finite.injective_iff_surjective.2 hs, hs⟩
  exact ⟨Equiv.ofBijective f hb, fun j => rfl⟩

theorem imgMaskC_spec {c m : ℕ} (h2 : ∀ j < 8, j ∈ codeL c) (hm : m < 256) :
    imgMaskC (codeL c) m < 256 ∧ framePop (imgMaskC (codeL c) m) = framePop m := by
  obtain ⟨e, he⟩ := codeL_perm h2
  have hI : imgMaskC (codeL c) m = bitsum fun i => m.testBit (e.symm i) := by
    rw [imgMaskC, bitsum, Finset.sum_range (fun j => if m.testBit j then 2 ^ (codeL c).getD j 0
      else 0), ← Equiv.sum_comp e (fun i => if m.testBit (e.symm i) then 2 ^ (i : ℕ) else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.symm_apply_apply, codeL_getD c j.2, he j]
  obtain ⟨hlt, hpop⟩ := bitsum_spec fun i => m.testBit (e.symm i)
  rw [hI]
  refine ⟨hlt, ?_⟩
  rw [hpop, framePop_bits m hm, ← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]

theorem okC_mul {a b : ℕ} (ha : okC a = true) (hb : okC b = true) : okC (spMul a b) = true := by
  obtain ⟨-, ha2, ha3, ha4⟩ := okC_spec ha
  obtain ⟨-, hb2, hb3, hb4⟩ := okC_spec hb
  refine okC_of ?_ ?_ ?_
  · rw [spMul_eq, sumN8]
    have hs := fun j => spAt_lt a (spAt b j)
    have := hs 0
    have := hs 1
    have := hs 2
    have := hs 3
    have := hs 4
    have := hs 5
    have := hs 6
    have := hs 7
    have := Nat.mod_lt (spMask a ^^^ spImgMask a (spMask b)) (show 0 < 256 by norm_num)
    simp only [Nat.reducePow, pow_zero, pow_one]
    omega
  · intro j hj
    rw [codeL_mul]
    obtain ⟨k, hk, hkj⟩ : ∃ k < 8, spAt a k = j := by
      have := ha2 j hj
      simp only [codeL, List.mem_map, List.mem_range] at this
      exact this
    obtain ⟨m, hm, hmk⟩ : ∃ m < 8, spAt b m = k := by
      have := hb2 k hk
      simp only [codeL, List.mem_map, List.mem_range] at this
      exact this
    simp only [compC, List.mem_map, List.mem_range]
    exact ⟨m, hm, by rw [codeL_getD b hm, hmk, codeL_getD a hk, hkj]⟩
  · obtain ⟨hlt, hpop⟩ := imgMaskC_spec ha2 hb3
    rw [spMask_mul, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 8) ha3 hlt), framePop_xor, hpop]
    omega

end CFSG.KLC.E8

end
