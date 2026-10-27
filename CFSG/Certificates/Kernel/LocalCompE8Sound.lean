module

public import Certificates.Data.Kernel.WeylE8.Roots
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

@[expose] def reflArrL (L : List (List ℤ)) (r : ℕ) : Array ℕ :=
  Array.ofFn (n := 240) fun i => L.idxOf (reflVec (L.getD r []) (L.getD i.val []))

@[expose] def negArrL (L : List (List ℤ)) : Array ℕ :=
  Array.ofFn (n := 240) fun i => L.idxOf ((L.getD i.val []).map (-·))

@[expose] def signArrL (L : List (List ℤ)) (v : FrameVec) : Array ℕ :=
  Array.ofFn (n := 240) fun i =>
    L.idxOf ((List.finRange 8).map fun k =>
      if v k = 1 then -(L.getD i.val []).getD k 0 else (L.getD i.val []).getD k 0)

end CFSG.KLC.E8

end

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.KS.Raw.Orb in
theorem cf_eq (K k : ℕ) : cf K k = K / 16 ^ k % 16 := by
  have h : cf K k = pg 4 (mask 4) K k := rfl
  rw [h, pg_eq, pow_mul]
  norm_num

public theorem cf_lt (K k : ℕ) : cf K k < 16 := by
  rw [cf_eq]
  exact Nat.mod_lt _ (by norm_num)

public theorem band_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

public theorem blt_true {a b : ℕ} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem expand_aux : ∀ n x : ℕ, x < 16 ^ n → x = ∑ k ∈ Finset.range n, x / 16 ^ k % 16 * 16 ^ k
  | 0, x, h => by simp_all
  | n + 1, x, h => by
    rw [Finset.sum_range_succ']
    have ih := expand_aux n (x / 16) (by rw [pow_succ] at h; omega)
    have e : ∀ k ∈ Finset.range n, x / 16 ^ (k + 1) % 16 * 16 ^ (k + 1) =
        16 * (x / 16 / 16 ^ k % 16 * 16 ^ k) := by
      intro k _
      rw [Nat.div_div_eq_div_mul, pow_succ']
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← ih]
    simp only [pow_zero, Nat.div_one, mul_one]
    omega

public theorem expand8 {x : ℕ} (h : x < 4294967296) :
    x = cf x 0 + 16 * cf x 1 + 256 * cf x 2 + 4096 * cf x 3 + 65536 * cf x 4 + 1048576 * cf x 5 +
      16777216 * cf x 6 + 268435456 * cf x 7 := by
  have e := expand_aux 8 x (by norm_num; omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cf_eq] at e ⊢
  norm_num at e ⊢
  omega

public theorem uniq8 {e : ℕ → ℤ} (hb : ∀ k < 8, -16 < e k ∧ e k < 16)
    (h : e 0 + 16 * e 1 + 256 * e 2 + 4096 * e 3 + 65536 * e 4 + 1048576 * e 5 +
      16777216 * e 6 + 268435456 * e 7 = 0) : ∀ k < 8, e k = 0 := by
  have h0 := hb 0 (by norm_num)
  have h1 := hb 1 (by norm_num)
  have h2 := hb 2 (by norm_num)
  have h3 := hb 3 (by norm_num)
  have h4 := hb 4 (by norm_num)
  have h5 := hb 5 (by norm_num)
  have h6 := hb 6 (by norm_num)
  have h7 := hb 7 (by norm_num)
  intro k hk
  interval_cases k <;> omega

open CFSG.KS.Raw.Orb in
theorem hiBit {W : ℕ} (h : Nat.land W HI = 0) {k : ℕ} (hk : k < 8) : cf W k < 8 := by
  have h1 : (W &&& HI).testBit (4 * k + 3) = false := by
    have e : (W &&& HI) = 0 := h
    rw [e, Nat.zero_testBit]
  have hHI : HI.testBit (4 * k + 3) = true := by
    interval_cases k <;> decide
  rw [Nat.testBit_and, hHI, Bool.and_true] at h1
  have e : cf W k = W / 2 ^ (4 * k) % 2 ^ 4 := by
    have h : cf W k = pg 4 (mask 4) W k := rfl
    rw [h, pg_eq]
  have h2 : (cf W k).testBit 3 = false := by
    rw [e, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [Nat.lt_succ_self, decide_true, Bool.true_and]
    rw [Nat.add_comm]
    exact h1
  have key : ∀ c < 16, c.testBit 3 = false → c < 8 := by decide
  exact key _ (cf_lt W k) h2

theorem small_le {Y : ℕ} (hY : Y < 4294967296) (hs : small Y = true) : ∀ k < 8, cf Y k ≤ 4 := by
  obtain ⟨h1, h2⟩ := band_true hs
  have h1' : Nat.land Y HI = 0 := Nat.eq_of_beq_eq_true h1
  generalize hZ : Nat.add Y (Nat.mul (nat_lit 3) REP) = Z at h2
  have h2' : Nat.land Z HI = 0 := Nat.eq_of_beq_eq_true h2
  have hZ' : Z = Y + 858993459 := by rw [← hZ]; rfl
  have eY := expand8 hY
  have b : ∀ k < 8, cf Y k < 8 := fun k hk => hiBit h1' hk
  have b0 := b 0 (by norm_num)
  have b1 := b 1 (by norm_num)
  have b2 := b 2 (by norm_num)
  have b3 := b 3 (by norm_num)
  have b4 := b 4 (by norm_num)
  have b5 := b 5 (by norm_num)
  have b6 := b 6 (by norm_num)
  have b7 := b 7 (by norm_num)
  have eZ := expand8 (x := Z) (by omega)
  have u := uniq8 (e := fun k => (cf Z k : ℤ) - (cf Y k + 3))
    (fun k hk => by have := cf_lt Z k; have := b k hk; omega) (by omega)
  intro k hk
  have := u k hk
  have := hiBit h2' hk
  simp only at *
  omega

@[expose] public noncomputable def vecOf (K : ℕ) : List ℤ := List.ofFn (n := 8) fun k => (cf K k.val : ℤ) - 2

theorem bindRow_aux (K : ℕ) : ∀ (v : List ℤ) (k : ℕ),
    List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k (nat_lit 8))
      (fun c _ ih k => bAnd(Int.beq' c (Int.subNatNat (cf K k) (nat_lit 2)), ih (Nat.succ k))) v k =
      true →
    k + v.length = 8 ∧ ∀ j (hj : j < v.length), v[j] = (cf K (k + j) : ℤ) - 2
  | [], k, h => by
    have : k = 8 := Nat.eq_of_beq_eq_true h
    simp [this]
  | c :: v, k, h => by
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨ih1, ih2⟩ := bindRow_aux K v (Nat.succ k) h2
    rw [Int.beq'_eq] at h1
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    intro j hj
    cases j with
    | zero => simpa [Int.subNatNat_eq_coe] using h1
    | succ j =>
      have e : k + (j + 1) = Nat.succ k + j := by omega
      simpa [e] using ih2 j (by simpa using hj)

theorem bindRow_eq {K : ℕ} {v : List ℤ} (h : bindRow K v = true) : v = vecOf K := by
  obtain ⟨h1, h2⟩ := bindRow_aux K v 0 h
  apply List.ext_getElem
  · simp [vecOf]; omega
  · intro j hj _
    simp only [vecOf, List.getElem_ofFn, h2 j hj, Nat.zero_add]

theorem bindRoots_aux (RK : ℕ → ℕ) : ∀ (L : List (List ℤ)) (i : ℕ),
    List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 240))
      (fun v _ ih i => bAnd(Nat.blt (RK i) (nat_lit 4294967296), bAnd(small (RK i),
        bAnd(bindRow (RK i) v, ih (Nat.succ i))))) L i = true →
    i + L.length = 240 ∧ ∀ j (hj : j < L.length), RK (i + j) < 4294967296 ∧
      small (RK (i + j)) = true ∧ L[j] = vecOf (RK (i + j))
  | [], i, h => by
    have : i = 240 := Nat.eq_of_beq_eq_true h
    simp [this]
  | v :: L, i, h => by
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨h2, h3⟩ := band_true h2
    obtain ⟨h3, h4⟩ := band_true h3
    obtain ⟨ih1, ih2⟩ := bindRoots_aux RK L (Nat.succ i) h4
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    intro j hj
    cases j with
    | zero => exact ⟨blt_true h1, h2, bindRow_eq h3⟩
    | succ j =>
      have e : i + (j + 1) = Nat.succ i + j := by omega
      simpa [e] using ih2 j (by simpa using hj)

public theorem getD_eq {L : List (List ℤ)} {j : ℕ} (h : j < L.length) : L.getD j [] = L[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

public theorem bind_facts {RK : ℕ → ℕ} {L : List (List ℤ)} (hb : bindRoots RK L = true) :
    L.length = 240 ∧ ∀ j < 240, RK j < 4294967296 ∧ (∀ k < 8, cf (RK j) k ≤ 4) ∧
      L.getD j [] = vecOf (RK j) := by
  obtain ⟨h1, h2⟩ := bindRoots_aux RK L 0 hb
  refine ⟨by omega, fun j hj => ?_⟩
  obtain ⟨a, b, c⟩ := h2 j (by omega)
  simp only [Nat.zero_add] at a b c
  exact ⟨a, small_le a b, by rw [getD_eq (by omega), c]⟩

public theorem key_eq_of_vec {K K' : ℕ} (hK : K < 4294967296) (hK' : K' < 4294967296)
    (h : vecOf K = vecOf K') : K = K' := by
  have hf := List.ofFn_inj.mp h
  have e : ∀ k < 8, cf K k = cf K' k := fun k hk => by
    have := congrFun hf ⟨k, hk⟩
    simp only at this
    omega
  rw [expand8 hK, expand8 hK', e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
    e 3 (by norm_num), e 4 (by norm_num), e 5 (by norm_num), e 6 (by norm_num), e 7 (by norm_num)]

open CFSG.KS.Raw.Orb in
theorem sorted_inj {RK : ℕ → ℕ} {SO : ℕ} (hs : sortedOK RK SO = true) {i j : ℕ} (hi : i < 240)
    (hj : j < 240) (h : RK i = RK j) : i = j := by
  obtain ⟨h1, h2⟩ := band_true hs
  rw [allN_iff] at h1 h2
  set f : ℕ → ℕ := fun t => pg (nat_lit 8) (nat_lit 255) SO t with hf
  have hlt : ∀ t < 240, f t < 240 := fun t ht => blt_true (h1 t ht)
  have hstep : ∀ t < 239, RK (f t) < RK (f (t + 1)) := fun t ht => blt_true (h2 t ht)
  have mono : ∀ a b, a < b → b < 240 → RK (f a) < RK (f b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact (ih h (by omega)).trans (hstep b (by omega))
      · subst h
        exact hstep a (by omega)
  have mono' : ∀ a b, a < 240 → b < 240 → RK (f a) = RK (f b) → a = b := by
    intro a b ha hb he
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd he (mono a b h hb).ne
    · exact h
    · exact absurd he (mono b a h ha).ne'
  let g : Fin 240 → Fin 240 := fun t => ⟨f t.val, hlt t.val t.isLt⟩
  have ginj : Function.Injective g := by
    intro a b hab
    have : f a.val = f b.val := congrArg Fin.val hab
    exact Fin.ext (mono' a.val b.val a.isLt b.isLt (by rw [this]))
  have gsurj := Finite.injective_iff_surjective.mp ginj
  obtain ⟨a, ha⟩ := gsurj ⟨i, hi⟩
  obtain ⟨b, hb⟩ := gsurj ⟨j, hj⟩
  have ha' : f a.val = i := congrArg Fin.val ha
  have hb' : f b.val = j := congrArg Fin.val hb
  have := mono' a.val b.val a.isLt b.isLt (by rw [ha', hb', h])
  rw [← ha', ← hb', this]

public theorem idxOf_root {RK : ℕ → ℕ} {L : List (List ℤ)} {SO : ℕ} (hb : bindRoots RK L = true)
    (hs : sortedOK RK SO = true) {e : ℕ} (he : e < 240) : L.idxOf (L.getD e []) = e := by
  obtain ⟨hl, hf⟩ := bind_facts hb
  have hnd : L.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro a b hab
    have ha := (hf a.val (by omega)).2.2
    have hb' := (hf b.val (by omega)).2.2
    rw [getD_eq a.isLt] at ha
    rw [getD_eq b.isLt] at hb'
    simp only at hab
    rw [ha, hb'] at hab
    exact Fin.ext (sorted_inj hs (by omega) (by omega)
      (key_eq_of_vec (hf a.val (by omega)).1 (hf b.val (by omega)).1 hab))
  rw [getD_eq (by omega)]
  exact hnd.idxOf_getElem e (by omega)

public theorem sumN8 (f : ℕ → ℕ) :
    sumN 8 f = f 7 + (f 6 + (f 5 + (f 4 + (f 3 + (f 2 + (f 1 + (f 0 + 0))))))) := rfl

public theorem b8 {f : ℕ → ℕ} (h : ∀ k < 8, f k ≤ 4) :
    f 0 ≤ 4 ∧ f 1 ≤ 4 ∧ f 2 ≤ 4 ∧ f 3 ≤ 4 ∧ f 4 ≤ 4 ∧ f 5 ≤ 4 ∧ f 6 ≤ 4 ∧ f 7 ≤ 4 :=
  ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num)⟩

public theorem dot_eq (x r : ℕ) : dotZ (vecOf x) (vecOf r) =
    ((sumN 8 (fun k => cf x k * cf r k) + 32 : ℕ) : ℤ) -
      ((2 * (sumN 8 (fun k => cf x k) + sumN 8 (fun k => cf r k)) : ℕ) : ℤ) := by
  rw [sumN8, sumN8, sumN8]
  push_cast
  simp only [dotZ, vecOf, List.ofFn_succ, List.ofFn_zero, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.sum_cons, List.sum_nil, Fin.val_zero, Fin.val_succ]
  ring

theorem reflVec_vecOf (x r : ℕ) {c : ℤ} (hc : dotZ (vecOf x) (vecOf r) / 4 = c) :
    reflVec (vecOf r) (vecOf x) =
      List.ofFn (n := 8) fun k => ((cf x k.val : ℤ) - 2) - c * ((cf r k.val : ℤ) - 2) := by
  rw [reflVec, hc]
  apply List.ext_getElem
  · simp only [vecOf, List.length_zipWith, List.length_ofFn, min_self]
  · intro j _ _
    simp only [vecOf, List.getElem_zipWith, List.getElem_ofFn]

theorem refl_finish {x r e : ℕ} (c : ℤ) (hc5 : c = -2 ∨ c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2)
    (hx : x < 4294967296) (hr : r < 4294967296) (he : e < 4294967296)
    (sx : ∀ k < 8, cf x k ≤ 4) (sr : ∀ k < 8, cf r k ≤ 4) (se : ∀ k < 8, cf e k ≤ 4)
    (hd : dotZ (vecOf x) (vecOf r) / 4 = c) (hsum : (e : ℤ) = x - c * r + 2 * c * 286331153) :
    reflVec (vecOf r) (vecOf x) = vecOf e := by
  rw [reflVec_vecOf x r hd]
  have ex := expand8 hx
  have er := expand8 hr
  have ee := expand8 he
  have u := uniq8 (e := fun k => (cf e k : ℤ) - (cf x k - c * cf r k + 2 * c))
    (fun k hk => by
      have := sx k hk
      have := sr k hk
      have := se k hk
      rcases hc5 with rfl | rfl | rfl | rfl | rfl <;> omega)
    (by rcases hc5 with rfl | rfl | rfl | rfl | rfl <;> omega)
  unfold vecOf
  congr 1
  funext k
  have := u k.val k.isLt
  linarith

theorem keyIf_eq {Y : ℕ} (h : keyIf Y < 4294967296) : keyIf Y = Y := by
  unfold keyIf at h ⊢
  rw [CFSG.KS.Raw.Orb.nIf_eq] at h ⊢
  split_ifs at h ⊢
  · rfl
  · exact absurd h (lt_irrefl _)

open CFSG.KS.Raw.Orb in
theorem key2_false {x r : ℕ} (h : key2 false x r < 4294967296) :
    (key2 false x r : ℤ) = ((cf x 0 : ℤ) + 4 - 2 * cf r 0) + 16 * ((cf x 1 : ℤ) + 4 - 2 * cf r 1) +
      256 * ((cf x 2 : ℤ) + 4 - 2 * cf r 2) + 4096 * ((cf x 3 : ℤ) + 4 - 2 * cf r 3) +
      65536 * ((cf x 4 : ℤ) + 4 - 2 * cf r 4) + 1048576 * ((cf x 5 : ℤ) + 4 - 2 * cf r 5) +
      16777216 * ((cf x 6 : ℤ) + 4 - 2 * cf r 6) + 268435456 * ((cf x 7 : ℤ) + 4 - 2 * cf r 7) := by
  unfold key2 at h ⊢
  simp only [nIf_eq] at h ⊢
  split_ifs at h ⊢ with hok
  · have g : ∀ k < 8, 2 * cf r k ≤ cf x k + 4 := fun k hk =>
      Nat.le_of_ble_eq_true (band_true (allN_iff.mp hok k hk)).1
    have hs : sumN (nat_lit 8) (fun k => Nat.shiftLeft (Nat.sub (Nat.add (cf x k) (nat_lit 4))
        (Nat.mul (nat_lit 2) (cf r k))) (Nat.mul (nat_lit 4) k)) =
        sumN 8 (fun k => (cf x k + 4 - 2 * cf r k) * 16 ^ k) := by
      congr 1
      funext k
      have e1 : Nat.shiftLeft (cf x k + 4 - 2 * cf r k) (4 * k) =
          (cf x k + 4 - 2 * cf r k) * 2 ^ (4 * k) := Nat.shiftLeft_eq _ _
      rw [pow_mul] at e1
      exact e1
    rw [hs, sumN8]
    push_cast [Nat.cast_sub (g 0 (by norm_num)), Nat.cast_sub (g 1 (by norm_num)),
      Nat.cast_sub (g 2 (by norm_num)), Nat.cast_sub (g 3 (by norm_num)),
      Nat.cast_sub (g 4 (by norm_num)), Nat.cast_sub (g 5 (by norm_num)),
      Nat.cast_sub (g 6 (by norm_num)), Nat.cast_sub (g 7 (by norm_num))]
    ring
  · exact absurd h (lt_irrefl _)

open CFSG.KS.Raw.Orb in
theorem key2_true {x r : ℕ} (h : key2 true x r < 4294967296) :
    (key2 true x r : ℤ) = ((cf x 0 : ℤ) + 2 * cf r 0 - 4) + 16 * ((cf x 1 : ℤ) + 2 * cf r 1 - 4) +
      256 * ((cf x 2 : ℤ) + 2 * cf r 2 - 4) + 4096 * ((cf x 3 : ℤ) + 2 * cf r 3 - 4) +
      65536 * ((cf x 4 : ℤ) + 2 * cf r 4 - 4) + 1048576 * ((cf x 5 : ℤ) + 2 * cf r 5 - 4) +
      16777216 * ((cf x 6 : ℤ) + 2 * cf r 6 - 4) + 268435456 * ((cf x 7 : ℤ) + 2 * cf r 7 - 4) := by
  unfold key2 at h ⊢
  simp only [nIf_eq] at h ⊢
  split_ifs at h ⊢ with hok
  · have g : ∀ k < 8, 4 ≤ cf x k + 2 * cf r k := fun k hk =>
      Nat.le_of_ble_eq_true (band_true (allN_iff.mp hok k hk)).1
    have hs : sumN (nat_lit 8) (fun k => Nat.shiftLeft (Nat.sub (Nat.add (cf x k)
        (Nat.mul (nat_lit 2) (cf r k))) (nat_lit 4)) (Nat.mul (nat_lit 4) k)) =
        sumN 8 (fun k => (cf x k + 2 * cf r k - 4) * 16 ^ k) := by
      congr 1
      funext k
      have e1 : Nat.shiftLeft (cf x k + 2 * cf r k - 4) (4 * k) =
          (cf x k + 2 * cf r k - 4) * 2 ^ (4 * k) := Nat.shiftLeft_eq _ _
      rw [pow_mul] at e1
      exact e1
    rw [hs, sumN8]
    push_cast [Nat.cast_sub (g 0 (by norm_num)), Nat.cast_sub (g 1 (by norm_num)),
      Nat.cast_sub (g 2 (by norm_num)), Nat.cast_sub (g 3 (by norm_num)),
      Nat.cast_sub (g 4 (by norm_num)), Nat.cast_sub (g 5 (by norm_num)),
      Nat.cast_sub (g 6 (by norm_num)), Nat.cast_sub (g 7 (by norm_num))]
    ring
  · exact absurd h (lt_irrefl _)

public theorem refl_vec {x r e : ℕ} (hx : x < 4294967296) (hr : r < 4294967296) (he : e < 4294967296)
    (sx : ∀ k < 8, cf x k ≤ 4) (sr : ∀ k < 8, cf r k ≤ 4) (se : ∀ k < 8, cf e k ≤ 4)
    (hk : e = reflKey x r) : reflVec (vecOf r) (vecOf x) = vecOf e := by
  have hdot := dot_eq x r
  have ex := expand8 hx
  have er := expand8 hr
  have he2 := he
  unfold reflKey at hk
  beta_reduce at hk
  generalize hP : Nat.add (sumN (nat_lit 8) fun k => Nat.mul (cf x k) (cf r k)) (nat_lit 32) = P
    at hk
  generalize hN : Nat.mul (nat_lit 2) (Nat.add (sumN (nat_lit 8) fun k => cf x k)
    (sumN (nat_lit 8) fun k => cf r k)) = N at hk
  have hd : dotZ (vecOf x) (vecOf r) = (P : ℤ) - N := by
    rw [← hP, ← hN]
    exact hdot
  have fin : ∀ c : ℤ, (c = -2 ∨ c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2) →
      dotZ (vecOf x) (vecOf r) / 4 = c → (e : ℤ) = x - c * r + 2 * c * 286331153 →
      reflVec (vecOf r) (vecOf x) = vecOf e :=
    fun c hc5 hdc hs => refl_finish c hc5 hx hr he sx sr se hdc hs
  cases h1 : Nat.beq P N
  · simp only [h1] at hk
    cases h2 : Nat.beq P (Nat.add N (nat_lit 4))
    · simp only [h2] at hk
      cases h3 : Nat.beq N (Nat.add P (nat_lit 4))
      · simp only [h3] at hk
        cases h4 : Nat.beq P (Nat.add N (nat_lit 8))
        · simp only [h4] at hk
          cases h5 : Nat.beq N (Nat.add P (nat_lit 8))
          · simp only [h5] at hk
            rw [hk] at he2
            exact absurd he2 (lt_irrefl _)
          · simp only [h5] at hk
            have h5' : N = P + 8 := Nat.eq_of_beq_eq_true h5
            rw [hk] at he2
            have hv := key2_true he2
            rw [← hk] at hv
            exact fin (-2) (by norm_num) (by rw [hd]; omega) (by omega)
        · simp only [h4] at hk
          have h4' : P = N + 8 := Nat.eq_of_beq_eq_true h4
          rw [hk] at he2
          have hv := key2_false he2
          rw [← hk] at hv
          exact fin 2 (by norm_num) (by rw [hd]; omega) (by omega)
      · simp only [h3] at hk
        have h3' : N = P + 4 := Nat.eq_of_beq_eq_true h3
        cases g : Nat.ble (Nat.mul (nat_lit 2) REP) (Nat.add x r)
        · simp only [g] at hk
          rw [hk] at he2
          exact absurd he2 (lt_irrefl _)
        · simp only [g] at hk
          have g' : 572662306 ≤ x + r := Nat.le_of_ble_eq_true g
          rw [hk] at he2
          have hv : e = x + r - 572662306 := hk.trans (keyIf_eq he2)
          exact fin (-1) (by norm_num) (by rw [hd]; omega) (by omega)
    · simp only [h2] at hk
      have h2' : P = N + 4 := Nat.eq_of_beq_eq_true h2
      cases g : Nat.ble r (Nat.add x (Nat.mul (nat_lit 2) REP))
      · simp only [g] at hk
        rw [hk] at he2
        exact absurd he2 (lt_irrefl _)
      · simp only [g] at hk
        have g' : r ≤ x + 572662306 := Nat.le_of_ble_eq_true g
        rw [hk] at he2
        have hv : e = x + 572662306 - r := hk.trans (keyIf_eq he2)
        exact fin 1 (by norm_num) (by rw [hd]; omega) (by omega)
  · simp only [h1] at hk
    have h1' : P = N := Nat.eq_of_beq_eq_true h1
    exact fin 0 (by norm_num) (by rw [hd]; omega) (by omega)

public theorem neg_vec {x e : ℕ} (hx : x < 4294967296) (he : e < 4294967296)
    (sx : ∀ k < 8, cf x k ≤ 4) (se : ∀ k < 8, cf e k ≤ 4) (hk : e = negKey x) :
    (vecOf x).map (-·) = vecOf e := by
  have ex := expand8 hx
  have ee := expand8 he
  obtain ⟨_, _, _, _, _, _, _, _⟩ := b8 sx
  have hk' : e = 1145324612 - x := hk
  have u := uniq8 (e := fun k => (cf e k : ℤ) - (4 - cf x k))
    (fun k hk => by
      have := sx k hk
      have := se k hk
      omega)
    (by omega)
  unfold vecOf
  rw [List.map_ofFn]
  congr 1
  funext k
  have := u k.val k.isLt
  simp only [Function.comp_apply] at this ⊢
  linarith

theorem cf_shift (K k : ℕ) : cf K k = (K >>> (4 * k)) &&& 15 := rfl

theorem cf_land (a b k : ℕ) : cf (a &&& b) k = cf a k &&& cf b k := by
  rw [cf_shift, cf_shift, cf_shift]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_shiftRight]
  cases a.testBit (4 * k + j) <;> cases b.testBit (4 * k + j) <;> cases Nat.testBit 15 j <;> rfl

theorem cf_lor (a b k : ℕ) : cf (a ||| b) k = cf a k ||| cf b k := by
  rw [cf_shift, cf_shift, cf_shift]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight]
  cases a.testBit (4 * k + j) <;> cases b.testBit (4 * k + j) <;> cases Nat.testBit 15 j <;> rfl

theorem digits_of {Y : ℕ} (hY : Y < 4294967296) (c : ℕ → ℕ) (hc : ∀ k < 8, c k < 16)
    (h : Y = c 0 + 16 * c 1 + 256 * c 2 + 4096 * c 3 + 65536 * c 4 + 1048576 * c 5 +
      16777216 * c 6 + 268435456 * c 7) : ∀ k < 8, cf Y k = c k := by
  have eY := expand8 hY
  have u := uniq8 (e := fun k => (cf Y k : ℤ) - c k)
    (fun k hk => by have := cf_lt Y k; have := hc k hk; omega) (by omega)
  intro k hk
  have := u k hk
  omega

public theorem digitsZ {Y : ℕ} (hY : Y < 4294967296) (c : ℕ → ℤ) (hc : ∀ k < 8, 0 ≤ c k ∧ c k < 16)
    (h : (Y : ℤ) = c 0 + 16 * c 1 + 256 * c 2 + 4096 * c 3 + 65536 * c 4 + 1048576 * c 5 +
      16777216 * c 6 + 268435456 * c 7) : ∀ k < 8, (cf Y k : ℤ) = c k := by
  have eY := expand8 hY
  have u := uniq8 (e := fun k => (cf Y k : ℤ) - c k)
    (fun k hk => by have := cf_lt Y k; have := hc k hk; omega) (by omega)
  intro k hk
  have := u k hk
  omega

public theorem bit01 (m k : ℕ) : Nat.land (Nat.shiftRight m k) 1 = 0 ∨ Nat.land (Nat.shiftRight m k) 1 = 1 := by
  have e : Nat.land (Nat.shiftRight m k) 1 = (m >>> k) % 2 := Nat.and_one_is_mod _
  rw [e]
  exact Nat.mod_two_eq_zero_or_one _

public theorem bit_testBit (m k : ℕ) : Nat.land (Nat.shiftRight m k) 1 = 1 ↔ m.testBit k = true := by
  have e : Nat.land (Nat.shiftRight m k) 1 = m / 2 ^ k % 2 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [e, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

theorem fieldMask_eq (m : ℕ) : fieldMask m =
    Nat.land (Nat.shiftRight m 0) 1 * 15 + 16 * (Nat.land (Nat.shiftRight m 1) 1 * 15) +
      256 * (Nat.land (Nat.shiftRight m 2) 1 * 15) + 4096 * (Nat.land (Nat.shiftRight m 3) 1 * 15) +
      65536 * (Nat.land (Nat.shiftRight m 4) 1 * 15) +
      1048576 * (Nat.land (Nat.shiftRight m 5) 1 * 15) +
      16777216 * (Nat.land (Nat.shiftRight m 6) 1 * 15) +
      268435456 * (Nat.land (Nat.shiftRight m 7) 1 * 15) := by
  unfold fieldMask
  rw [sumN8]
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.mul_eq]
  ring

theorem and15 : ∀ n < 16, n &&& 15 = n := by decide

theorem sub_cf {Y Z : ℕ} (hY : Y < 4294967296) (hZ : Z ≤ Y) (h : ∀ k < 8, cf Z k ≤ cf Y k) :
    ∀ k < 8, cf (Y - Z) k = cf Y k - cf Z k := by
  have eY := expand8 hY
  have eZ := expand8 (x := Z) (by omega)
  have u := digitsZ (Y := Y - Z) (by omega) (fun k => (cf Y k : ℤ) - cf Z k)
    (fun k hk => by have := cf_lt Y k; have := h k hk; omega) (by omega)
  intro k hk
  have := u k hk
  have := h k hk
  omega

theorem flip_cf {m x : ℕ} (hx : x < 4294967296) (sx : ∀ k < 8, cf x k ≤ 4) :
    ∀ k < 8, cf (flipKey m x) k =
      if Nat.land (Nat.shiftRight m k) 1 = 1 then 4 - cf x k else cf x k := by
  have hfk : flipKey m x = Nat.lor (Nat.sub x (Nat.land x (fieldMask m)))
      (Nat.land (negKey x) (fieldMask m)) := by
    unfold flipKey
    rw [CFSG.KS.Raw.Orb.strictN_eq]
  have hF := fieldMask_eq m
  have hb : ∀ k, Nat.land (Nat.shiftRight m k) 1 = 0 ∨ Nat.land (Nat.shiftRight m k) 1 = 1 :=
    fun k => bit01 m k
  have hl : ∀ k, Nat.land (Nat.shiftRight m k) 1 ≤ 1 := fun k => by rcases hb k with h | h <;> omega
  generalize fieldMask m = F at hfk hF
  have hF32 : F < 4294967296 := by
    have := hl 0
    have := hl 1
    have := hl 2
    have := hl 3
    have := hl 4
    have := hl 5
    have := hl 6
    have := hl 7
    omega
  have cF : ∀ k < 8, cf F k = Nat.land (Nat.shiftRight m k) 1 * 15 :=
    digits_of hF32 (fun k => Nat.land (Nat.shiftRight m k) 1 * 15)
      (fun k _ => by have := hl k; omega) hF
  have hland : ∀ c k, k < 8 → c < 16 → c &&& cf F k = Nat.land (Nat.shiftRight m k) 1 * c :=
    fun c k hk hc => by
      rw [cF k hk]
      rcases hb k with h | h
      · rw [h]
        simp
      · rw [h, one_mul, one_mul]
        exact and15 c hc
  have hA : x &&& F < 4294967296 := lt_of_le_of_lt Nat.and_le_left hx
  have cA : ∀ k < 8, cf (x &&& F) k ≤ cf x k := fun k _ => by
    rw [cf_land]
    exact Nat.and_le_left
  have cD := sub_cf hx Nat.and_le_left cA
  have hN' : negKey x = 1145324612 - x := rfl
  have ex := expand8 hx
  obtain ⟨_, _, _, _, _, _, _, _⟩ := b8 sx
  have cNZ := digitsZ (Y := negKey x) (by omega) (fun k => 4 - (cf x k : ℤ))
    (fun k hk => by have := sx k hk; omega) (by rw [hN']; omega)
  have cN : ∀ k < 8, cf (negKey x) k = 4 - cf x k := fun k hk => by
    have := cNZ k hk
    have := sx k hk
    omega
  intro k hk
  rw [hfk]
  change cf ((x - (x &&& F)) ||| (negKey x &&& F)) k = _
  rw [cf_lor, cD k hk, cf_land, cf_land, cN k hk, hland (cf x k) k hk (cf_lt x k),
    hland (4 - cf x k) k hk (by omega)]
  rcases hb k with h | h
  · rw [h]
    simp
  · rw [h]
    simp

public theorem vecOf_getD (x : ℕ) (k : Fin 8) : (vecOf x).getD k 0 = (cf x k : ℤ) - 2 := by
  rw [vecOf, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem frameDecode_one (m : ℕ) (k : Fin 8) :
    frameDecode m k = 1 ↔ Nat.land (Nat.shiftRight m k) 1 = 1 := by
  rw [bit_testBit]
  by_cases h : m.testBit k = true
  · simp [frameDecode, h]
  · simp [frameDecode, h]

public theorem flip_vec {m x e : ℕ} (hx : x < 4294967296) (sx : ∀ k < 8, cf x k ≤ 4)
    (hk : e = flipKey m x) :
    (List.finRange 8).map (fun k => if frameDecode m k = 1 then -(vecOf x).getD k 0
      else (vecOf x).getD k 0) = vecOf e := by
  conv_rhs => rw [vecOf, List.ofFn_eq_map]
  congr 1
  funext k
  subst hk
  rw [vecOf_getD, flip_cf hx sx k.val k.isLt]
  have := sx k.val k.isLt
  by_cases h : Nat.land (Nat.shiftRight m k) 1 = 1
  · have h1 : frameDecode m k = 1 := (frameDecode_one m k).2 h
    simp only [h1, h, ite_true]
    omega
  · have h1 : ¬frameDecode m k = 1 := fun h' => h ((frameDecode_one m k).1 h')
    simp only [h1, h, ite_false]

public theorem pop8_eq (m : ℕ) : pop8 m = framePop m := by
  unfold pop8 framePop
  rw [sumN8]
  have e : ∀ j, Nat.land (Nat.shiftRight m j) 1 = (m >>> j) &&& 1 := fun _ => rfl
  simp only [e, Nat.shiftRight_zero]
  omega

theorem sumN_congr {f g : ℕ → ℕ} : ∀ {n : ℕ}, (∀ i < n, f i = g i) → sumN n f = sumN n g
  | 0, _ => rfl
  | n + 1, h => by
    change f n + sumN n f = g n + sumN n g
    rw [h n (by omega), sumN_congr (fun i hi => h i (by omega))]

theorem countP_sumN (q : ℕ → Bool) :
    ∀ n, (List.range n).countP q = sumN n (fun i => if q i = true then 1 else 0)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.countP_append, countP_sumN q n]
    change _ = (if q n = true then 1 else 0) + _
    have hs : [n].countP q = if q n = true then 1 else 0 := by cases h : q n <;> simp [h]
    rw [hs, Nat.add_comm]
    rfl

end CFSG.KLC.E8

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

theorem refl_sound {L : List (List ℤ)} {RK RT : Nat → Nat} {SO : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) :
    ∀ r < 240, reflArrL L r = unpack 240 8 (RT r) :=
  fun r hr0 => by
    obtain ⟨-, hf⟩ := bind_facts hb
    have hrow := hr r hr0
    unfold reflRowOK at hrow
    simp only [CFSG.KS.Raw.Orb.strictB_eq] at hrow
    rw [CFSG.KS.Raw.Orb.allN_iff] at hrow
    unfold reflArrL unpack
    apply congrArg Array.ofFn
    funext i
    have hi := hrow i.val i.isLt
    generalize hE : pg (nat_lit 8) (nat_lit 255) (RT r) i.val = e at hi
    have hpg : pg 8 (mask 8) (RT r) i.val = e := hE
    rw [hpg]
    obtain ⟨he1, he2⟩ := band_true hi
    have he240 : e < 240 := blt_true he1
    obtain ⟨xr, sr, vr⟩ := hf r hr0
    obtain ⟨xi, si, vi⟩ := hf i.val i.isLt
    obtain ⟨xe, se, ve⟩ := hf e he240
    rw [vr, vi, refl_vec xi xr xe si sr se (Nat.eq_of_beq_eq_true he2), ← ve]
    exact idxOf_root hb hs he240

theorem tables_sound {L : List (List ℤ)} {RK RT : Nat → Nat} {SO NEG : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true) :
    (∀ r < 240, reflArrL L r = unpack 240 8 (RT r)) ∧ negArrL L = unpack 240 8 NEG := by
  obtain ⟨-, hf⟩ := bind_facts hb
  refine ⟨refl_sound hb hs hr, ?_⟩
  · unfold negTabOK at hn
    rw [CFSG.KS.Raw.Orb.allN_iff] at hn
    unfold negArrL unpack
    apply congrArg Array.ofFn
    funext i
    have hi := hn i.val i.isLt
    simp only [CFSG.KS.Raw.Orb.strictB_eq] at hi
    generalize hE : pg (nat_lit 8) (nat_lit 255) NEG i.val = e at hi
    have hpg : pg 8 (mask 8) NEG i.val = e := hE
    rw [hpg]
    obtain ⟨he1, he2⟩ := band_true hi
    obtain ⟨-, he3⟩ := band_true he2
    have he240 : e < 240 := blt_true he1
    obtain ⟨xi, si, vi⟩ := hf i.val i.isLt
    obtain ⟨xe, se, ve⟩ := hf e he240
    rw [vi, neg_vec xi xe si se (Nat.eq_of_beq_eq_true he3), ← ve]
    exact idxOf_root hb hs he240

theorem signs_sound {L : List (List ℤ)} {RK ST : Nat → Nat} {SO : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hst : ∀ m < 256, signRowOK RK m (ST m) = true) :
    ∀ m < 256, framePop m % 2 = 0 → signArrL L (frameDecode m) = unpack 240 8 (ST m) := by
  intro m hm he
  obtain ⟨-, hf⟩ := bind_facts hb
  have hrow := hst m hm
  have hp : Nat.beq (Nat.land (pop8 m) (nat_lit 1)) (nat_lit 0) = true := by
    rw [Nat.beq_eq]
    change pop8 m &&& 1 = 0
    rw [Nat.and_one_is_mod, pop8_eq, he]
  unfold signRowOK at hrow
  rw [hp] at hrow
  change allN 240 _ = true at hrow
  rw [CFSG.KS.Raw.Orb.allN_iff] at hrow
  unfold signArrL unpack
  apply congrArg Array.ofFn
  funext i
  have hi := hrow i.val i.isLt
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at hi
  generalize hE : pg (nat_lit 8) (nat_lit 255) (ST m) i.val = e at hi
  have hpg : pg 8 (mask 8) (ST m) i.val = e := hE
  rw [hpg]
  obtain ⟨he1, he2⟩ := band_true hi
  obtain ⟨-, he3⟩ := band_true he2
  have he240 : e < 240 := blt_true he1
  obtain ⟨xi, si, vi⟩ := hf i.val i.isLt
  obtain ⟨-, -, ve⟩ := hf e he240
  rw [vi, flip_vec xi si (Nat.eq_of_beq_eq_true he3), ← ve]
  exact idxOf_root hb hs he240

theorem fixCntK_sound (n w p : Nat) : fixCount n (unpack n w p) = fixCntK n w p := by
  unfold fixCount fixCntK
  rw [countP_sumN]
  apply sumN_congr
  intro i hi
  have hg : (unpack n w p)[i]! = pg w (mask w) p i := by
    rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rw [hg, CFSG.KS.Raw.Orb.nIf_eq]
  by_cases h : pg w (mask w) p i = i
  · simp [h]
  · simp [h]

theorem reflArr_eq (r : ℕ) : reflArr r = reflArrL rootList r := rfl

theorem negArr_eq : negArr = negArrL rootList := rfl

theorem signArr_eq (v : FrameVec) : signArr v = signArrL rootList v := rfl

end CFSG.KLC.E8

end
