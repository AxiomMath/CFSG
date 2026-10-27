module

public import Certificates.Data.Kernel.B45Perm.RuSyl
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
import CFSG.Certificates.Kernel.Misc.RuInvCov

public section

namespace CFSG.KC.B45P.RuSylS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.KC.B45P.RuSyl
open CFSG.Quasithin.B45Exc.Tab CFSG.Monster.B.Co2 CFSG.KS.Raw.Orb

abbrev G := Equiv.Perm (Fin 4060)

abbrev p0 : Fin 4060 := ⟨0, by norm_num⟩

abbrev p1 : Fin 4060 := ⟨1, by norm_num⟩

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bIf_eq (c t e : Bool) : bIf(c, t, e) = (if c = true then t else e) := by cases c <;> rfl

theorem beq_eq (a b : Nat) : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, Nat.beq_eq.mpr⟩

theorem code_lt {c : Nat} (hc : c < 16384) : Nat.shiftRight c 3 < 2048 ∧ Nat.land c 7 < 8 := by
  refine ⟨?_, Nat.lt_succ_of_le Nat.and_le_right⟩
  change c >>> 3 < 2048
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem code_mk {a b : Nat} (hb : b < 8) : Nat.shiftRight (8 * a + b) 3 = a ∧
    Nat.land (8 * a + b) 7 = b := by
  refine ⟨?_, ?_⟩
  · change (8 * a + b) >>> 3 = a
    rw [Nat.shiftRight_eq_div_pow]
    omega
  · change (8 * a + b) &&& (2 ^ 3 - 1) = b
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega

section Base

variable {H : Subgroup G} {TR TRI CD IX : Nat → Nat} {R0 R1 o0 o1 : Nat} {T0 T1 : Nat → G}
  (hT0 : ∀ a < 2048, PRep 4060 12 (TR (Nat.add o0 a)) (T0 a))
  (hT1 : ∀ b < 8, PRep 4060 12 (TR (Nat.add o1 b)) (T1 b))
  (hgen : ∀ g ∈ H, ∃ a < 2048, ∃ b < 8, g = T0 a * T1 b)
  (hin : ∀ a < 2048, ∀ b < 8, T0 a * T1 b ∈ H)
  (hcov : ∀ c < 16384, covC R0 R1 TR TRI CD IX o0 o1 c = true)

@[expose] def sig (T0 T1 : Nat → G) (c : Nat) : G := T0 (Nat.shiftRight c 3) * T1 (Nat.land c 7)

include hT0 hT1 in
theorem img_eq {c p : Nat} (hc : c < 16384) (hp : p < 4060) :
    imgC TR o0 o1 c p = (sig T0 T1 c ⟨p, hp⟩ : Nat) := by
  obtain ⟨ha, hb⟩ := code_lt hc
  have e1 := hT1 _ hb ⟨p, hp⟩
  have e0 := hT0 _ ha (T1 (Nat.land c 7) ⟨p, hp⟩)
  change pg 12 (mask 12) (TR (Nat.add o0 (Nat.shiftRight c 3)))
    (pg 12 (mask 12) (TR (Nat.add o1 (Nat.land c 7))) p) = _
  have e1' : pg 12 (mask 12) (TR (Nat.add o1 (Nat.land c 7))) p =
      (T1 (Nat.land c 7) ⟨p, hp⟩ : Nat) := e1
  rw [e1', e0]
  rfl

include hT0 hT1 in
theorem img_lt {c p : Nat} (hc : c < 16384) (hp : p < 4060) : imgC TR o0 o1 c p < 4060 := by
  rw [img_eq hT0 hT1 hc hp]
  exact Fin.isLt _

include hcov in
theorem cov_parts {c : Nat} (hc : c < 16384) :
    decC R0 R1 TRI o0 (imgC TR o0 o1 c 0) (imgC TR o0 o1 c 1) = c ∧
      ((IX c < 495 ∧ CD (IX c) = c) ∨
        ¬ (imgC TR o0 o1 c (imgC TR o0 o1 c 0) = 0 ∧ imgC TR o0 o1 c (imgC TR o0 o1 c 1) = 1) ∨
        (imgC TR o0 o1 c 0 = 0 ∧ imgC TR o0 o1 c 1 = 1) ∨ fixC TR o0 o1 c ≠ 92) := by
  have h := hcov c hc
  unfold covC at h
  rw [strictB_eq, strictB_eq, bAnd_eq, Bool.and_eq_true, beq_eq] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  by_cases hl : IX c < 495 ∧ CD (IX c) = c
  · exact Or.inl hl
  have hl' : bAnd(Nat.blt (IX c) 495, Nat.beq (CD (IX c)) c) = false :=
    Bool.eq_false_iff.2 fun e => hl (by rwa [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, beq_eq] at e)
  rw [hl'] at h2
  dsimp only at h2
  by_cases hs : imgC TR o0 o1 c (imgC TR o0 o1 c 0) = 0 ∧
      imgC TR o0 o1 c (imgC TR o0 o1 c 1) = 1
  swap
  · exact Or.inr (Or.inl hs)
  have hs' : bAnd(Nat.beq (imgC TR o0 o1 c (imgC TR o0 o1 c 0)) 0,
      Nat.beq (imgC TR o0 o1 c (imgC TR o0 o1 c 1)) 1) = true := by
    rw [bAnd_eq, Bool.and_eq_true, beq_eq, beq_eq]
    exact hs
  rw [hs'] at h2
  dsimp only at h2
  by_cases hf : imgC TR o0 o1 c 0 = 0 ∧ imgC TR o0 o1 c 1 = 1
  · exact Or.inr (Or.inr (Or.inl hf))
  have hf' : bAnd(Nat.beq (imgC TR o0 o1 c 0) 0, Nat.beq (imgC TR o0 o1 c 1) 1) = false :=
    Bool.eq_false_iff.2 fun e => hf (by rwa [bAnd_eq, Bool.and_eq_true, beq_eq, beq_eq] at e)
  rw [hf'] at h2
  dsimp only at h2
  refine Or.inr (Or.inr (Or.inr fun e => ?_))
  have e' : Nat.beq (fixC TR o0 o1 c) (nat_lit 92) = true := Nat.beq_eq.mpr e
  rw [e'] at h2
  exact Bool.false_ne_true h2

include hT0 hT1 hgen in
theorem exists_code {g : G} (hg : g ∈ H) : ∃ c < 16384, g = sig T0 T1 c := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hgen g hg
  obtain ⟨e1, e2⟩ := code_mk (a := a) hb
  exact ⟨8 * a + b, by omega, by rw [sig, e1, e2]⟩

include hT0 hT1 hgen hcov in
theorem eq_of_base01 {g h : G} (hg : g ∈ H) (hh : h ∈ H) (e0 : g p0 = h p0) (e1 : g p1 = h p1) :
    g = h := by
  obtain ⟨c, hc, rfl⟩ := exists_code hT0 hT1 hgen hg
  obtain ⟨c', hc', rfl⟩ := exists_code hT0 hT1 hgen hh
  have d := (cov_parts hcov hc).1
  have d' := (cov_parts hcov hc').1
  rw [img_eq hT0 hT1 hc (by norm_num), img_eq hT0 hT1 hc (by norm_num)] at d
  rw [img_eq hT0 hT1 hc' (by norm_num), img_eq hT0 hT1 hc' (by norm_num)] at d'
  have : c = c' := by
    rw [← d, ← d']
    change decC R0 R1 TRI o0 (sig T0 T1 c p0) (sig T0 T1 c p1) =
      decC R0 R1 TRI o0 (sig T0 T1 c' p0) (sig T0 T1 c' p1)
    rw [e0, e1]
  rw [this]

include hin in
theorem sig_mem {c : Nat} (hc : c < 16384) : sig T0 T1 c ∈ H :=
  hin _ (code_lt hc).1 _ (code_lt hc).2

end Base

theorem count_fix {g : G} {f : Nat → Nat} (hf : ∀ x (hx : x < 4060), f x = (g ⟨x, hx⟩ : Nat)) :
    ((List.range 4060).filter fun x => Nat.beq (f x) x).length = (fixFinset g).card := by
  have hr : Rep 4060 (Array.ofFn fun i : Fin 4060 => (g i : Nat)) g := fun x => by
    rw [getElem!_ofFn_nat _ x.2]
  rw [← fixCountA_eq hr, fixCountA, List.countP_eq_length_filter]
  have e : (List.range 4060).filter (fun x => Nat.beq (f x) x) = (List.range 4060).filter
      (fun p => (Array.ofFn fun i : Fin 4060 => (g i : Nat))[p]! == p) := by
    refine List.filter_congr fun x hx => ?_
    have hx' := List.mem_range.1 hx
    rw [getElem!_ofFn_nat _ hx', hf x hx']
    exact Bool.eq_iff_iff.2 ⟨fun h => beq_iff_eq.2 (Nat.eq_of_beq_eq_true h),
      fun h => Nat.beq_eq.mpr (beq_iff_eq.1 h)⟩
  rw [e]

@[expose] def X (T0 T1 : Nat → G) (CD : Nat → Nat) (i : Nat) : G :=
  if i < 495 then sig T0 T1 (CD i) else 1

theorem inv_parts {TR CD IX K0 K1 : Nat → Nat} {o0 o1 i : Nat}
    (h : invC TR CD IX K0 K1 o0 o1 i = true) :
    CD i < 16384 ∧ IX (CD i) = i ∧ imgC TR o0 o1 (CD i) 0 = K0 i ∧
      imgC TR o0 o1 (CD i) 1 = K1 i ∧ imgC TR o0 o1 (CD i) (K0 i) = 0 ∧
      imgC TR o0 o1 (CD i) (K1 i) = 1 ∧ ¬ (K0 i = 0 ∧ K1 i = 1) := by
  unfold invC at h
  rw [strictB_eq] at h
  simp only [bAnd_eq, Bool.and_eq_true, beq_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun hk => ?_⟩
  have hk' : (Nat.beq (K0 i) 0 && Nat.beq (K1 i) 1) = true := by
    rw [Bool.and_eq_true, beq_eq, beq_eq]
    exact hk
  rw [hk'] at h7
  exact Bool.false_ne_true h7

theorem pair_parts {TR CD K0 K1 CM PR : Nat → Nat} {o0 o1 i j : Nat}
    (h : pairC TR CD K0 K1 CM PR o0 o1 i (CD i) j = true) :
    (imgC TR o0 o1 (CD i) (K0 j) = imgC TR o0 o1 (CD j) (K0 i) ∧
        imgC TR o0 o1 (CD i) (K1 j) = imgC TR o0 o1 (CD j) (K1 i) →
      Nat.testBit (CM i) j = true ∧ fld(PR i, Nat.mul 9 j, 511) ≤ 495 ∧
        K0 (fld(PR i, Nat.mul 9 j, 511)) = imgC TR o0 o1 (CD i) (K0 j) ∧
        K1 (fld(PR i, Nat.mul 9 j, 511)) = imgC TR o0 o1 (CD i) (K1 j)) ∧
    (¬ (imgC TR o0 o1 (CD i) (K0 j) = imgC TR o0 o1 (CD j) (K0 i) ∧
        imgC TR o0 o1 (CD i) (K1 j) = imgC TR o0 o1 (CD j) (K1 i)) →
      Nat.testBit (CM i) j = false) := by
  unfold pairC at h
  rw [strictB_eq, strictB_eq, strictB_eq, strictB_eq, strictB_eq] at h
  refine ⟨fun he => ?_, fun hne => ?_⟩
  · have he' : bAnd(Nat.beq (imgC TR o0 o1 (CD i) (K0 j)) (imgC TR o0 o1 (CD j) (K0 i)),
        Nat.beq (imgC TR o0 o1 (CD i) (K1 j)) (imgC TR o0 o1 (CD j) (K1 i))) = true := by
      rw [bAnd_eq, Bool.and_eq_true, beq_eq, beq_eq]
      exact he
    rw [he'] at h
    dsimp only at h
    unfold keyC at h
    simp only [bAnd_eq, Bool.and_eq_true, beq_eq, Nat.ble_eq] at h
    exact h
  · have hne' : bAnd(Nat.beq (imgC TR o0 o1 (CD i) (K0 j)) (imgC TR o0 o1 (CD j) (K0 i)),
        Nat.beq (imgC TR o0 o1 (CD i) (K1 j)) (imgC TR o0 o1 (CD j) (K1 i))) = false :=
      Bool.eq_false_iff.2 fun e => hne (by rwa [bAnd_eq, Bool.and_eq_true, beq_eq, beq_eq] at e)
    rw [hne'] at h
    dsimp only at h
    cases e : Nat.testBit (CM i) j
    · rfl
    · rw [e] at h
      exact absurd h (by decide)

section Table

variable {H : Subgroup G} {TR TRI CD IX K0 K1 CM PR : Nat → Nat} {R0 R1 o0 o1 : Nat}
  {T0 T1 : Nat → G}
  (hT0 : ∀ a < 2048, PRep 4060 12 (TR (Nat.add o0 a)) (T0 a))
  (hT1 : ∀ b < 8, PRep 4060 12 (TR (Nat.add o1 b)) (T1 b))
  (hgen : ∀ g ∈ H, ∃ a < 2048, ∃ b < 8, g = T0 a * T1 b)
  (hin : ∀ a < 2048, ∀ b < 8, T0 a * T1 b ∈ H)
  (hcov : ∀ c < 16384, covC R0 R1 TR TRI CD IX o0 o1 c = true)
  (hinv : ∀ i < 495, invC TR CD IX K0 K1 o0 o1 i = true)
  (hrow : ∀ i < 495, rowC TR CD K0 K1 CM PR o0 o1 i = true)
  (hk : K0 495 = 0 ∧ K1 495 = 1)

include hT0 hT1 hinv in
theorem x_val {i y : Nat} (hi : i < 495) (hy : y < 4060) :
    (X T0 T1 CD i ⟨y, hy⟩ : Nat) = imgC TR o0 o1 (CD i) y := by
  rw [X, if_pos hi, img_eq hT0 hT1 (inv_parts (hinv i hi)).1 hy]

include hT0 hT1 hinv hk in
theorem x_key {i : Nat} (hi : i ≤ 495) :
    (X T0 T1 CD i p0 : Nat) = K0 i ∧ (X T0 T1 CD i p1 : Nat) = K1 i := by
  rcases Nat.lt_or_ge i 495 with h | h
  · obtain ⟨-, -, h3, h4, -⟩ := inv_parts (hinv i h)
    exact ⟨(x_val hT0 hT1 hinv h _).trans h3, (x_val hT0 hT1 hinv h _).trans h4⟩
  · have : i = 495 := by omega
    subst this
    rw [X, if_neg (lt_irrefl _)]
    exact ⟨hk.1.symm, hk.2.symm⟩

include hin hinv in
theorem x_mem (i : Nat) : X T0 T1 CD i ∈ H := by
  unfold X
  split_ifs with h
  · exact sig_mem hin (inv_parts (hinv i h)).1
  · exact H.one_mem

theorem x_one {i : Nat} (hi : 495 ≤ i) : X T0 T1 CD i = 1 := by
  rw [X, if_neg (by omega)]

theorem app_of_val {g : G} {x : Fin 4060} {v : Nat} (hv : (x : Nat) = v) (hv' : v < 4060) :
    g x = g ⟨v, hv'⟩ := by
  congr 1
  exact Fin.ext hv

include hT0 hT1 hgen hin hcov hinv hk in
theorem x_sq {i : Nat} (hi : i < 495) : X T0 T1 CD i * X T0 T1 CD i = 1 := by
  obtain ⟨hc, -, h3, h4, h5, h6, -⟩ := inv_parts (hinv i hi)
  obtain ⟨k0, k1⟩ := x_key hT0 hT1 hinv hk hi.le
  have l0 : K0 i < 4060 := h3 ▸ img_lt hT0 hT1 hc (by norm_num)
  have l1 : K1 i < 4060 := h4 ▸ img_lt hT0 hT1 hc (by norm_num)
  refine eq_of_base01 hT0 hT1 hgen hcov (H.mul_mem (x_mem hin hinv i) (x_mem hin hinv i))
    H.one_mem (Fin.ext ?_) (Fin.ext ?_)
  · rw [Equiv.Perm.mul_apply, app_of_val k0 l0, x_val hT0 hT1 hinv hi, h5]
    rfl
  · rw [Equiv.Perm.mul_apply, app_of_val k1 l1, x_val hT0 hT1 hinv hi, h6]
    rfl

include hT0 hT1 hinv hk in
theorem x_ne_one {i : Nat} (hi : i < 495) : X T0 T1 CD i ≠ 1 := by
  intro h
  obtain ⟨k0, k1⟩ := x_key hT0 hT1 hinv hk hi.le
  rw [h] at k0 k1
  exact (inv_parts (hinv i hi)).2.2.2.2.2.2 ⟨k0.symm, k1.symm⟩

include hT0 hT1 hcov hinv hk in
theorem x_inj {i j : Nat} (hi : i ≤ 495) (hj : j ≤ 495) (h : X T0 T1 CD i = X T0 T1 CD j) :
    i = j := by
  rcases Nat.lt_or_ge i 495 with hi' | hi' <;> rcases Nat.lt_or_ge j 495 with hj' | hj'
  · obtain ⟨ci, xi, -⟩ := inv_parts (hinv i hi')
    obtain ⟨cj, xj, -⟩ := inv_parts (hinv j hj')
    have di := (cov_parts hcov ci).1
    have dj := (cov_parts hcov cj).1
    have e0 : imgC TR o0 o1 (CD i) 0 = imgC TR o0 o1 (CD j) 0 := by
      rw [← x_val hT0 hT1 hinv hi' (y := 0) (by norm_num),
        ← x_val hT0 hT1 hinv hj' (y := 0) (by norm_num), h]
    have e1 : imgC TR o0 o1 (CD i) 1 = imgC TR o0 o1 (CD j) 1 := by
      rw [← x_val hT0 hT1 hinv hi' (y := 1) (by norm_num),
        ← x_val hT0 hT1 hinv hj' (y := 1) (by norm_num), h]
    rw [e0, e1, dj] at di
    rw [← xi, ← xj, di]
  · exact absurd (h.trans (x_one hj')) (x_ne_one hT0 hT1 hinv hk hi')
  · exact absurd ((x_one hi').symm.trans h).symm (x_ne_one hT0 hT1 hinv hk hj')
  · omega

include hT0 hT1 hinv hrow in
theorem row_pair {i j : Nat} (hi : i < 495) (hj : j < 495) :
    pairC TR CD K0 K1 CM PR o0 o1 i (CD i) j = true := by
  have h := hrow i hi
  unfold rowC at h
  rw [strictB_eq] at h
  exact allN_spec h j hj

include hT0 hT1 hinv hk in
theorem xx_val {i j : Nat} (hi : i < 495) (hj : j < 495) :
    ((X T0 T1 CD i * X T0 T1 CD j) p0 : Nat) = imgC TR o0 o1 (CD i) (K0 j) ∧
      ((X T0 T1 CD i * X T0 T1 CD j) p1 : Nat) = imgC TR o0 o1 (CD i) (K1 j) := by
  obtain ⟨k0, k1⟩ := x_key hT0 hT1 hinv hk hj.le
  obtain ⟨hc, -, h3, h4, -⟩ := inv_parts (hinv j hj)
  have l0 : K0 j < 4060 := h3 ▸ img_lt hT0 hT1 hc (by norm_num)
  have l1 : K1 j < 4060 := h4 ▸ img_lt hT0 hT1 hc (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, app_of_val k0 l0, x_val hT0 hT1 hinv hi]
  · rw [Equiv.Perm.mul_apply, app_of_val k1 l1, x_val hT0 hT1 hinv hi]

include hT0 hT1 hgen hin hcov hinv hrow hk in
theorem x_comm (i j : Nat) :
    cK CM i j = true ↔ X T0 T1 CD i * X T0 T1 CD j = X T0 T1 CD j * X T0 T1 CD i := by
  by_cases hij : i < 495 ∧ j < 495
  · rw [cK, if_pos hij]
    obtain ⟨hi, hj⟩ := hij
    obtain ⟨a0, a1⟩ := xx_val hT0 hT1 hinv hk hi hj
    obtain ⟨b0, b1⟩ := xx_val hT0 hT1 hinv hk hj hi
    obtain ⟨hyes, hno⟩ := pair_parts (row_pair hT0 hT1 hinv hrow hi hj)
    constructor
    · intro hb
      have he : imgC TR o0 o1 (CD i) (K0 j) = imgC TR o0 o1 (CD j) (K0 i) ∧
          imgC TR o0 o1 (CD i) (K1 j) = imgC TR o0 o1 (CD j) (K1 i) := by
        by_contra hne
        rw [hno hne] at hb
        exact Bool.false_ne_true hb
      exact eq_of_base01 hT0 hT1 hgen hcov (H.mul_mem (x_mem hin hinv i) (x_mem hin hinv j))
        (H.mul_mem (x_mem hin hinv j) (x_mem hin hinv i)) (Fin.ext (by rw [a0, b0, he.1]))
        (Fin.ext (by rw [a1, b1, he.2]))
    · intro hc
      refine (hyes ⟨?_, ?_⟩).1
      · rw [← a0, ← b0, hc]
      · rw [← a1, ← b1, hc]
  · rw [cK, if_neg hij]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    rcases not_and_or.1 hij with h | h
    · rw [x_one (not_lt.1 h), one_mul, mul_one]
    · rw [x_one (not_lt.1 h), one_mul, mul_one]

include hT0 hT1 hgen hin hcov hinv hrow hk in
theorem x_prod {i j : Nat} (hi : i ≤ 495) (hj : j ≤ 495) (hc : cK CM i j = true) :
    pK PR i j ≤ 495 ∧ X T0 T1 CD i * X T0 T1 CD j = X T0 T1 CD (pK PR i j) := by
  rcases Nat.lt_or_ge i 495 with hi' | hi'
  · rcases Nat.lt_or_ge j 495 with hj' | hj'
    · rw [cK, if_pos ⟨hi', hj'⟩] at hc
      rw [pK, if_pos hi', if_pos hj']
      obtain ⟨a0, a1⟩ := xx_val hT0 hT1 hinv hk hi' hj'
      obtain ⟨hyes, hno⟩ := pair_parts (row_pair hT0 hT1 hinv hrow hi' hj')
      have he : imgC TR o0 o1 (CD i) (K0 j) = imgC TR o0 o1 (CD j) (K0 i) ∧
          imgC TR o0 o1 (CD i) (K1 j) = imgC TR o0 o1 (CD j) (K1 i) := by
        by_contra hne
        rw [hno hne] at hc
        exact Bool.false_ne_true hc
      obtain ⟨-, hle, e0, e1⟩ := hyes he
      obtain ⟨k0, k1⟩ := x_key hT0 hT1 hinv hk hle
      refine ⟨hle, eq_of_base01 hT0 hT1 hgen hcov
        (H.mul_mem (x_mem hin hinv i) (x_mem hin hinv j)) (x_mem hin hinv _)
        (Fin.ext (by rw [a0, k0, e0])) (Fin.ext (by rw [a1, k1, e1]))⟩
    · have : j = 495 := by omega
      subst this
      rw [pK, if_pos hi', if_neg (lt_irrefl _), x_one le_rfl, mul_one]
      exact ⟨hi, rfl⟩
  · have : i = 495 := by omega
    subst this
    rw [pK, if_neg (lt_irrefl _), x_one le_rfl, one_mul]
    exact ⟨hj, rfl⟩

include hT0 hT1 hgen hin hcov hinv hk in
theorem x_cover {x : G} (hx : x ∈ H) (h2 : x * x = 1) (h92 : (fixFinset x).card = 92) :
    ∃ i < 495, x = X T0 T1 CD i := by
  obtain ⟨c, hc, rfl⟩ := exists_code hT0 hT1 hgen hx
  have v0 := img_eq hT0 hT1 hc (p := 0) (by norm_num)
  have v1 := img_eq hT0 hT1 hc (p := 1) (by norm_num)
  have l0 := img_lt hT0 hT1 hc (p := 0) (by norm_num)
  have l1 := img_lt hT0 hT1 hc (p := 1) (by norm_num)
  rcases (cov_parts hcov hc).2 with ⟨hl, hcd⟩ | hs | hf | hn
  · refine ⟨IX c, hl, ?_⟩
    rw [X, if_pos hl, hcd]
  · exfalso
    apply hs
    refine ⟨?_, ?_⟩
    · rw [img_eq hT0 hT1 hc l0, ← app_of_val v0.symm l0, ← Equiv.Perm.mul_apply, h2]
      rfl
    · rw [img_eq hT0 hT1 hc l1, ← app_of_val v1.symm l1, ← Equiv.Perm.mul_apply, h2]
      rfl
  · exfalso
    have h1 : sig T0 T1 c = 1 := eq_of_base01 hT0 hT1 hgen hcov hx H.one_mem
      (Fin.ext (by rw [← v0, hf.1]; rfl)) (Fin.ext (by rw [← v1, hf.2]; rfl))
    rw [h1] at h92
    simp [fixFinset] at h92
  · exfalso
    apply hn
    have hfold : fixC TR o0 o1 c =
        ((List.range 4060).filter fun x => Nat.beq (imgC TR o0 o1 c x) x).length := by
      unfold fixC
      rw [strictN_eq, strictN_eq]
      exact CFSG.KC.Misc.RuInv.P.foldN_count (fun x => Nat.beq (imgC TR o0 o1 c x) x) 4060
    rw [hfold, count_fix (g := sig T0 T1 c) fun y hy => img_eq hT0 hT1 hc hy, h92]

end Table

end CFSG.KC.B45P.RuSylS

end
