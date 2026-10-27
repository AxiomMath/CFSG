module

public import Certificates.Data.Kernel.FzUT.Shape
public import CFSG.Certificates.Kernel.FzUT.Norm3

public section

namespace CFSG.KC.FzUT

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.FritzII
open scoped commutatorElement

@[expose] def vcode (v : FzV) : Nat := v.1.val + 2 * v.2.1.val + 4 * v.2.2.val

@[expose] def encE (x : FzElt) : Nat := enc x.1 + 64 * vcode x.2

theorem vcode_lt : ∀ v : FzV, vcode v < 8 := by decide +kernel

theorem vcode_bits : ∀ v : FzV, (vcode v &&& 1) = v.1.val ∧ ((vcode v >>> 1) &&& 1) = v.2.1.val ∧
    ((vcode v >>> 2) &&& 1) = v.2.2.val := by
  decide +kernel

theorem vcode_add : ∀ v w : FzV, vcode (v + w) = vcode v ^^^ vcode w := by decide +kernel

theorem vcode_inj : ∀ v w : FzV, vcode v = vcode w → v = w := by decide +kernel

theorem encE_lt (x : FzElt) : encE x < 512 := by
  have := enc_lt x.1
  have := vcode_lt x.2
  unfold encE
  omega

theorem encE_fst (x : FzElt) : encE x &&& 63 = enc x.1 := by
  have := enc_lt x.1
  change encE x &&& (2 ^ 6 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  unfold encE
  omega

theorem encE_snd (x : FzElt) : encE x >>> 6 = vcode x.2 := by
  have := enc_lt x.1
  rw [Nat.shiftRight_eq_div_pow]
  unfold encE
  omega

theorem encE_injective : Function.Injective encE := by
  intro x y h
  have h1 : enc x.1 = enc y.1 := by rw [← encE_fst, h, encE_fst]
  have h2 : vcode x.2 = vcode y.2 := by rw [← encE_snd, h, encE_snd]
  exact Prod.ext (enc_injective h1) (vcode_inj _ _ h2)

theorem encE_one : encE fzOneC = 0 := by decide +kernel

theorem zmod2_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide

theorem apC_eq (b : ZMod 2) (σ : MulAut FzUT) (q : FzUT) :
    apC b.val (gc σ) (enc q) = enc (fzAp b σ q) := by
  rcases zmod2_cases b with rfl | rfl
  · rfl
  · change evD (gc σ) (enc q) = enc (if (1 : ZMod 2) = 0 then q else σ q)
    rw [if_neg (by decide), evD_gc]

variable {t s l : MulAut FzUT}

theorem actP_eq (v : FzV) (q : FzUT) :
    actP (gc t) (gc s) (gc l) (vcode v) (enc q) = enc (fzAct t s l v q) := by
  obtain ⟨b0, b1, b2⟩ := vcode_bits v
  unfold actP
  rw [b0, b1, b2, apC_eq, apC_eq, apC_eq]
  rfl

theorem emP_eq (x y : FzElt) :
    emP (gc t) (gc s) (gc l) (encE x) (encE y) = encE (fzMulC t s l x y) := by
  unfold emP
  rw [encE_fst, encE_snd, encE_fst, encE_snd, actP_eq, ← enc_mul, ← vcode_add]
  rfl

section Rel

variable {T S L : Nat} {X : Type} {m : X → X → X} {one : X} {E : X → Nat}
  (hE : Function.Injective E) (hM : ∀ a b, emP T S L (E a) (E b) = E (m a b)) (h1 : E one = 0)
include hE hM h1

theorem q8_sound {a b : X} (h : q8B T S L (E a) (E b) = true) : FzQ8 m one a b := by
  unfold q8B at h
  rw [sb_eq, hM] at h
  obtain ⟨c1, h⟩ := (band_iff _ _).mp h
  obtain ⟨c2, h⟩ := (band_iff _ _).mp h
  obtain ⟨c3, c4⟩ := (band_iff _ _).mp h
  rw [hM, beq_iff, ← h1] at c1
  rw [hM, beq_iff] at c2
  rw [hM, hM, beq_iff] at c3
  refine ⟨hE c1, hE c2, hE c3, fun he => ?_⟩
  rw [he, h1, bnot_iff] at c4
  exact absurd (Nat.beq_refl 0) (by rw [c4]; decide)

omit h1 in
theorem cm_sound {u w : X} (h : cmB T S L (E u) (E w) = true) : m u w = m w u := by
  unfold cmB at h
  rw [hM, hM, beq_iff] at h
  exact hE h

theorem shapeRel_sound {G : Nat} (e : Nat → X) (hG : ∀ k < 7, fldN G 9 511 k = E (e k))
    (h : shapeRel T S L G = true)
    (hgen : ∀ x, FzReach m one {e 0, e 1, e 2, e 3, e 4, e 5, e 6} x) :
    FzShapeAt m one (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) := by
  unfold shapeRel at h
  have g0 := hG 0 (by norm_num)
  have g1 := hG 1 (by norm_num)
  have g2 := hG 2 (by norm_num)
  have g3 := hG 3 (by norm_num)
  have g4 := hG 4 (by norm_num)
  have g5 := hG 5 (by norm_num)
  have g6 := hG 6 (by norm_num)
  obtain ⟨q1, h⟩ := (band_iff _ _).mp h
  obtain ⟨q2, h⟩ := (band_iff _ _).mp h
  obtain ⟨q3, h⟩ := (band_iff _ _).mp h
  obtain ⟨hsq, h⟩ := (band_iff _ _).mp h
  obtain ⟨c12, h⟩ := (band_iff _ _).mp h
  obtain ⟨c13, h⟩ := (band_iff _ _).mp h
  obtain ⟨c23, h⟩ := (band_iff _ _).mp h
  obtain ⟨hy, h⟩ := (band_iff _ _).mp h
  obtain ⟨hy1, h⟩ := (band_iff _ _).mp h
  obtain ⟨hy2, h⟩ := (band_iff _ _).mp h
  obtain ⟨hy3, hy4⟩ := (band_iff _ _).mp h
  rw [g0, g1] at q1
  rw [g2, g3] at q2
  rw [g4, g5] at q3
  rw [g4, g0, g2, hM, hM, hM, hM, beq_iff] at hsq
  rw [g6, hM, beq_iff, ← h1] at hy
  rw [g6, g0, g2, hM, hM, beq_iff] at hy1
  rw [g6, g1, g3, hM, hM, beq_iff] at hy2
  rw [g6, g4] at hy3
  rw [g6, g5] at hy4
  rw [allN_iff] at c12 c13 c23
  have cc : ∀ {i j : Nat} (hi : i < 7) (hj : j < 7), cmB T S L (fldN G 9 511 i) (fldN G 9 511 j) =
      true → m (e i) (e j) = m (e j) (e i) := by
    intro i j hi hj hc
    rw [hG i hi, hG j hj] at hc
    exact cm_sound hE hM hc
  have p12 : ∀ i < 2, ∀ j < 2, m (e i) (e (2 + j)) = m (e (2 + j)) (e i) := fun i hi j hj =>
    cc (by omega) (by omega) ((allN_iff _ _).mp (c12 i hi) j hj)
  have p13 : ∀ i < 2, ∀ j < 2, m (e i) (e (4 + j)) = m (e (4 + j)) (e i) := fun i hi j hj =>
    cc (by omega) (by omega) ((allN_iff _ _).mp (c13 i hi) j hj)
  have p23 : ∀ i < 2, ∀ j < 2, m (e (2 + i)) (e (4 + j)) = m (e (4 + j)) (e (2 + i)) :=
    fun i hi j hj => cc (by omega) (by omega) ((allN_iff _ _).mp (c23 i hi) j hj)
  refine ⟨q8_sound hE hM h1 q1, q8_sound hE hM h1 q2, q8_sound hE hM h1 q3, hE hsq, ?_, ?_, ?_,
    hE hy, hE hy1, hE hy2, cm_sound hE hM hy3, cm_sound hE hM hy4, ?_⟩
  · intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact p12 0 (by norm_num) 0 (by norm_num)
    · exact p12 0 (by norm_num) 1 (by norm_num)
    · exact p12 1 (by norm_num) 0 (by norm_num)
    · exact p12 1 (by norm_num) 1 (by norm_num)
  · intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact p13 0 (by norm_num) 0 (by norm_num)
    · exact p13 0 (by norm_num) 1 (by norm_num)
    · exact p13 1 (by norm_num) 0 (by norm_num)
    · exact p13 1 (by norm_num) 1 (by norm_num)
  · intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact p23 0 (by norm_num) 0 (by norm_num)
    · exact p23 0 (by norm_num) 1 (by norm_num)
    · exact p23 1 (by norm_num) 0 (by norm_num)
    · exact p23 1 (by norm_num) 1 (by norm_num)
  · exact hgen

theorem wordP_sound {G : Nat} (e : Nat → X) (hG : ∀ k < 7, fldN G 9 511 k = E (e k)) (w : Nat) :
    ∃ g, FzReach m one {e 0, e 1, e 2, e 3, e 4, e 5, e 6} g ∧ wordP T S L G w = E g := by
  have key : ∀ n, ∃ g, FzReach m one {e 0, e 1, e 2, e 3, e 4, e 5, e 6} g ∧
      Nat.rec (motive := fun _ => Nat) 0
        (fun i acc => emP T S L acc (gsel G (fldN w 3 7 i))) n = E g := by
    intro n
    induction n with
    | zero => exact ⟨one, FzReach.one, h1.symm⟩
    | succ n ih =>
      obtain ⟨g, hg, eg⟩ := ih
      have hk : fldN w 3 7 n < 8 := fldN_lt w 3 n
      change ∃ g', _ ∧ emP T S L (Nat.rec (motive := fun _ => Nat) 0
        (fun i acc => emP T S L acc (gsel G (fldN w 3 7 i))) n) (gsel G (fldN w 3 7 n)) = E g'
      rw [eg]
      generalize fldN w 3 7 n = k at hk
      unfold gsel
      cases hb : Nat.beq k 7
      · have hk7 : k ≠ 7 := fun h => by rw [h] at hb; exact absurd hb (by decide)
        have hk' : k < 7 := by omega
        refine ⟨m g (e k), FzReach.mul hg (FzReach.gen ?_), ?_⟩
        · interval_cases k <;> simp
        · change emP T S L (E g) (fldN G 9 511 k) = _
          rw [hG k hk', hM]
      · refine ⟨m g one, FzReach.mul hg FzReach.one, ?_⟩
        change emP T S L (E g) 0 = _
        rw [← h1, hM]
  exact key 6

end Rel

theorem fzAct_zero (q : FzUT) : fzAct t s l 0 q = q := by
  simp [fzAct, fzAp]

theorem fzAct_one (v : FzV) : fzAct t s l v 1 = 1 := by
  simp only [fzAct, fzAp]
  split_ifs <;> simp

theorem comm_word : ⁅fzE1, fzF1⁆ = fzE1 * fzF1 * fzE1 * fzF1 ∧
    ⁅fzE1, fzFW⁆ = fzE1 * fzFW * fzE1 * fzFW := by
  decide +kernel

theorem reach_all {S : Set FzElt}
    (hg : ∀ k < 4, FzReach (fzMulC t s l) fzOneC S (genE k, 0))
    (h1 : FzReach (fzMulC t s l) fzOneC S (1, (1, 0, 0)))
    (h2 : FzReach (fzMulC t s l) fzOneC S (1, (0, 1, 0)))
    (h3 : FzReach (fzMulC t s l) fzOneC S (1, (0, 0, 1))) (x : FzElt) :
    FzReach (fzMulC t s l) fzOneC S x := by
  have hm : ∀ p q : FzUT, FzReach (fzMulC t s l) fzOneC S (p, 0) →
      FzReach (fzMulC t s l) fzOneC S (q, 0) → FzReach (fzMulC t s l) fzOneC S (p * q, 0) := by
    intro p q hp hq
    have := FzReach.mul hp hq
    have e : fzMulC t s l (p, 0) (q, 0) = (p * q, 0) := by
      simp only [fzMulC, fzAct_zero, add_zero]
    rwa [e] at this
  have h0 : FzReach (fzMulC t s l) fzOneC S (1, 0) := FzReach.one
  have hpw : ∀ (b : ZMod 2) (g : FzUT), FzReach (fzMulC t s l) fzOneC S (g, 0) →
      FzReach (fzMulC t s l) fzOneC S (fzPw b g, 0) := by
    intro b g hgr
    unfold fzPw
    split_ifs
    · exact h0
    · exact hgr
  have g0 := hg 0 (by norm_num)
  have g1 := hg 1 (by norm_num)
  have g2 := hg 2 (by norm_num)
  have g3 := hg 3 (by norm_num)
  simp only [genE] at g0 g1 g2 g3
  norm_num at g1 g2 g3
  obtain ⟨c1, c2⟩ := comm_word
  have hc1 : FzReach (fzMulC t s l) fzOneC S (⁅fzE1, fzF1⁆, 0) := by
    rw [c1]
    exact hm _ _ (hm _ _ (hm _ _ g0 g2) g0) g2
  have hc2 : FzReach (fzMulC t s l) fzOneC S (⁅fzE1, fzFW⁆, 0) := by
    rw [c2]
    exact hm _ _ (hm _ _ (hm _ _ g0 g3) g0) g3
  have hP : ∀ p : FzUT, FzReach (fzMulC t s l) fzOneC S (p, 0) := by
    intro p
    rw [fzUT_word p]
    exact hm _ _ (hm _ _ (hm _ _ (hm _ _ (hm _ _ (hpw _ _ g0) (hpw _ _ g1)) (hpw _ _ g2))
      (hpw _ _ g3)) (hpw _ _ hc1)) (hpw _ _ hc2)
  have hv : ∀ (a b : FzV), FzReach (fzMulC t s l) fzOneC S (1, a) →
      FzReach (fzMulC t s l) fzOneC S (1, b) → FzReach (fzMulC t s l) fzOneC S (1, a + b) := by
    intro a b ha hb
    have := FzReach.mul ha hb
    have e : fzMulC t s l (1, a) (1, b) = (1, a + b) := by
      simp only [fzMulC, fzAct_one, mul_one]
    rwa [e] at this
  have hb : ∀ (b : ZMod 2) (u : FzV), FzReach (fzMulC t s l) fzOneC S (1, u) →
      FzReach (fzMulC t s l) fzOneC S (1, b • u) := by
    intro b u hu
    rcases zmod2_cases b with rfl | rfl
    · rw [zero_smul]
      exact h0
    · rw [one_smul]
      exact hu
  obtain ⟨p, v0, v1, v2⟩ := x
  have hV : FzReach (fzMulC t s l) fzOneC S (1, (v0, v1, v2)) := by
    have e : ((v0, v1, v2) : FzV) = v0 • (1, 0, 0) + v1 • (0, 1, 0) + v2 • (0, 0, 1) := by
      simp
    rw [e]
    exact hv _ _ (hv _ _ (hb _ _ h1) (hb _ _ h2)) (hb _ _ h3)
  have := FzReach.mul (hP p) hV
  have e : fzMulC t s l (p, 0) (1, (v0, v1, v2)) = (p, (v0, v1, v2)) := by
    simp only [fzMulC, fzAct_zero, mul_one, zero_add]
  rwa [e] at this

theorem pwP4_eq (x : FzUT) (i : Nat) : pwP4 (enc x) i = enc (x ^ i) := by
  induction i with
  | zero => exact enc_one.symm
  | succ i ih =>
    change pmulP (pwP4 (enc x) i) (enc x) = _
    rw [ih, ← enc_mul, pow_succ]

theorem validXB_of {x₁ : FzUT} (hx : FzValidX t l x₁) : validXB (gc t) (gc l) (enc x₁) = true := by
  unfold validXB
  simp only [band_iff, beq_iff, evD_gc, pwP4_eq, ← enc_mul]
  refine ⟨by rw [hx.fix], by rw [hx.x1_four, enc_one], by rw [hx.x2_four, enc_one],
    by rw [hx.comm], ?_⟩
  rw [allN_iff]
  intro y hy
  rw [bimp_iff, beq_iff, anyN_iff]
  intro hfix
  rw [← enc_dec' hy, evD_gc] at hfix
  obtain ⟨i, j, hij⟩ := (hx.gen (dec y)).mp (enc_injective hfix)
  refine ⟨i + 4 * j, by omega, ?_⟩
  have e1 : (i.val + 4 * j.val) &&& 3 = i.val := by
    change _ &&& (2 ^ 2 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e2 : (i.val + 4 * j.val) >>> 2 = j.val := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2, beq_iff, ← hij, enc_dec' hy]

theorem fld9 {a0 a1 a2 a3 a4 a5 a6 : Nat} (h0 : a0 < 512) (h1 : a1 < 512) (h2 : a2 < 512)
    (h3 : a3 < 512) (h4 : a4 < 512) (h5 : a5 < 512) (h6 : a6 < 512) {k : Nat} (hk : k < 7) :
    fldN (a0 + 512 * a1 + 262144 * a2 + 134217728 * a3 + 68719476736 * a4 +
      35184372088832 * a5 + 18014398509481984 * a6) 9 511 k =
      [a0, a1, a2, a3, a4, a5, a6].getD k 0 := by
  have := fldN_eq (a0 + 512 * a1 + 262144 * a2 + 134217728 * a3 + 68719476736 * a4 +
      35184372088832 * a5 + 18014398509481984 * a6) 9 k
  norm_num at this
  rw [this]
  interval_cases k <;> simp <;> omega

theorem vc100 : vcode (1, 0, 0) = 1 := by decide +kernel

theorem vc010 : vcode (0, 1, 0) = 2 := by decide +kernel

theorem enc_256 : encE ((1 : FzUT), ((0, 0, 1) : FzV)) = 256 := by decide +kernel

theorem target_code {k : Nat} (hk : k < 7) :
    Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 k) (Nat.shiftLeft 64 (k - 4))
      (Nat.blt 3 k) =
    encE ([(fzE1, 0), (fzEW, 0), (fzF1, 0), (fzFW, 0), (1, (1, 0, 0)), (1, (0, 1, 0)),
      (1, (0, 0, 1))].getD k fzOneC) := by
  interval_cases k <;> decide +kernel

theorem shape_sound {SR : Nat} (hS : shapeScan (gc t) (gc s) (gc l) SR = true) (x₁ : FzUT)
    (hx : FzValidX t l x₁) : FzShape t s l x₁ := by
  rw [shapeScan, allN_iff] at hS
  have h := (bimp_iff _ _).mp (hS (enc x₁) (enc_lt x₁)) (validXB_of hx)
  generalize fldN SR 140 1393796574908163946345982392040522594123775 (enc x₁) = R at h
  unfold shapeOK at h
  rw [sb_eq] at h
  obtain ⟨hrel, hw⟩ := (band_iff _ _).mp h
  have er1 : enc (dec (fldN R 6 63 0)) = fldN R 6 63 0 := enc_dec' (fldN_lt R 6 0)
  have er3 : enc (dec (fldN R 6 63 1)) = fldN R 6 63 1 := enc_dec' (fldN_lt R 6 1)
  set r1 := dec (fldN R 6 63 0)
  set r3 := dec (fldN R 6 63 1)
  let el : List FzElt := [(x₁, (1, 0, 0)), (r1, (0, 1, 0)), (l x₁, (1, 0, 0)),
    fzMulC t s l (fzMulC t s l (1, (0, 0, 1)) (r1, (0, 1, 0))) (1, (0, 0, 1)),
    ((x₁ * l x₁)⁻¹, (1, 0, 0)), (r3, (0, 1, 0)), (1, (0, 0, 1))]
  let e : Nat → FzElt := fun k => el.getD k fzOneC
  have c0 : enc x₁ + 64 = encE (e 0) := by
    change _ = enc x₁ + 64 * vcode (1, 0, 0)
    rw [vc100]
  have c1 : fldN R 6 63 0 + 128 = encE (e 1) := by
    change _ = enc r1 + 64 * vcode (0, 1, 0)
    rw [vc010, er1]
  have c2 : evD (gc l) (enc x₁) + 64 = encE (e 2) := by
    change _ = enc (l x₁) + 64 * vcode (1, 0, 0)
    rw [vc100, evD_gc]
  have c3 : emP (gc t) (gc s) (gc l) (emP (gc t) (gc s) (gc l) 256 (fldN R 6 63 0 + 128)) 256 =
      encE (e 3) := by
    rw [← enc_256, c1, emP_eq, emP_eq]
    rfl
  have c4 : invP (pmulP (enc x₁) (evD (gc l) (enc x₁))) + 64 = encE (e 4) := by
    change _ = enc (x₁ * l x₁)⁻¹ + 64 * vcode (1, 0, 0)
    rw [vc100, evD_gc, ← enc_mul, invP_eq]
  have c5 : fldN R 6 63 1 + 128 = encE (e 5) := by
    change _ = enc r3 + 64 * vcode (0, 1, 0)
    rw [vc010, er3]
  have c6 : (256 : Nat) = encE (e 6) := enc_256.symm
  have hsh : shapeG (gc t) (gc s) (gc l) (enc x₁) R = encE (e 0) + 512 * encE (e 1) +
      262144 * encE (e 2) + 134217728 * encE (e 3) + 68719476736 * encE (e 4) +
      35184372088832 * encE (e 5) + 18014398509481984 * encE (e 6) := by
    unfold shapeG
    rw [c3, c4, c2, c1, c5, c0, c6]
  have hG : ∀ k < 7, fldN (shapeG (gc t) (gc s) (gc l) (enc x₁) R) 9 511 k = encE (e k) := by
    intro k hk
    rw [hsh, fld9 (encE_lt _) (encE_lt _) (encE_lt _) (encE_lt _) (encE_lt _) (encE_lt _)
      (encE_lt _) hk]
    interval_cases k <;> rfl
  have hM : ∀ a b, emP (gc t) (gc s) (gc l) (encE a) (encE b) = encE (fzMulC t s l a b) :=
    emP_eq
  rw [allN_iff] at hw
  have htg : ∀ k < 7, FzReach (fzMulC t s l) fzOneC {e 0, e 1, e 2, e 3, e 4, e 5, e 6}
      ([(fzE1, 0), (fzEW, 0), (fzF1, 0), (fzFW, 0), (1, (1, 0, 0)), (1, (0, 1, 0)),
        (1, (0, 0, 1))].getD k fzOneC) := by
    intro k hk
    obtain ⟨g, hg, eg⟩ := wordP_sound encE_injective hM encE_one e hG
      (fldN (R >>> 12) 18 262143 k)
    have := hw k hk
    rw [beq_iff, eg, target_code hk] at this
    rw [← encE_injective this]
    exact hg
  have hgen := reach_all (S := {e 0, e 1, e 2, e 3, e 4, e 5, e 6})
    (fun k hk => by
      interval_cases k
      exacts [htg 0 (by norm_num), htg 1 (by norm_num), htg 2 (by norm_num), htg 3 (by norm_num)])
    (htg 4 (by norm_num)) (htg 5 (by norm_num)) (htg 6 (by norm_num))
  exact ⟨r1, r3, shapeRel_sound encE_injective hM encE_one e hG hrel hgen⟩

end CFSG.KC.FzUT
