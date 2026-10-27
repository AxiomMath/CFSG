module

public import CFSG.Certificates.Kernel.Misc.Ree2Log
public import CFSG.Certificates.Kernel.Misc.ReeSound
public import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.KC.Loop CFSG.Walter.Ree.Bombieri Polynomial

@[expose] noncomputable def toF (x : ℕ) : F3P := ⟨mpP x, mpN x⟩

@[expose] def GdB (n x : ℕ) : Prop := (toF x).Valid ∧ mpP x < 2 ^ n ∧ mpN x < 2 ^ n

theorem mpP_eq (x : ℕ) : mpP x = x &&& (2 ^ 16 - 1) := rfl

theorem mpN_eq (x : ℕ) : mpN x = x >>> 16 := rfl

theorem mpOf_eq (p n : ℕ) : mpOf p n = p ||| (n <<< 16) := rfl

theorem toF_p (x : ℕ) : (toF x).p = mpP x := rfl

theorem toF_n (x : ℕ) : (toF x).n = mpN x := rfl

theorem mpP_mpOf {p : ℕ} (hp : p < 2 ^ 16) (n : ℕ) : mpP (mpOf p n) = p := by
  rw [mpP_eq, mpOf_eq]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases ht : t < 16
  · have ht' : ¬ t ≥ 16 := by omega
    simp [ht, ht']
  · have : p.testBit t = false :=
      Nat.testBit_lt_two_pow (hp.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [ht, this]

theorem mpN_mpOf {p : ℕ} (hp : p < 2 ^ 16) (n : ℕ) : mpN (mpOf p n) = n := by
  rw [mpN_eq, mpOf_eq]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (hp.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  simp

theorem toF_mpOf {p : ℕ} (hp : p < 2 ^ 16) (n : ℕ) : toF (mpOf p n) = ⟨p, n⟩ := by
  rw [toF, mpP_mpOf hp, mpN_mpOf hp]

theorem toF_zero : toF 0 = F3P.zero := rfl

theorem toF_one : toF 1 = F3P.one := rfl

theorem GdB.mono {n n' x : ℕ} (h : GdB n x) (hn : n ≤ n') : GdB n' x :=
  ⟨h.1, h.2.1.trans_le (Nat.pow_le_pow_right (by norm_num) hn),
    h.2.2.trans_le (Nat.pow_le_pow_right (by norm_num) hn)⟩

theorem toF_addMP {n x y : ℕ} (hn : n ≤ 16) (hx : GdB n x) (hy : GdB n y) :
    toF (addMP x y) = F3P.add (toF x) (toF y) ∧ GdB n (addMP x y) := by
  have hA : Nat.xor (Nat.lor (mpN x) (mpN y)) (Nat.xor (Nat.lor (mpP x) (mpN y))
      (Nat.lor (mpN x) (mpP y))) < 2 ^ n :=
    Nat.xor_lt_two_pow (Nat.or_lt_two_pow hx.2.2 hy.2.2)
      (Nat.xor_lt_two_pow (Nat.or_lt_two_pow hx.2.1 hy.2.2) (Nat.or_lt_two_pow hx.2.2 hy.2.1))
  have hB : Nat.xor (Nat.lor (mpP x) (mpP y)) (Nat.xor (Nat.lor (mpP x) (mpN y))
      (Nat.lor (mpN x) (mpP y))) < 2 ^ n :=
    Nat.xor_lt_two_pow (Nat.or_lt_two_pow hx.2.1 hy.2.1)
      (Nat.xor_lt_two_pow (Nat.or_lt_two_pow hx.2.1 hy.2.2) (Nat.or_lt_two_pow hx.2.2 hy.2.1))
  have hA' := hA.trans_le (Nat.pow_le_pow_right (by norm_num) hn)
  have he : toF (addMP x y) = F3P.add (toF x) (toF y) := by
    unfold addMP
    rw [sN, toF_mpOf hA']
    rfl
  refine ⟨he, ?_, ?_, ?_⟩
  · rw [he]; exact F3P.valid_add hx.1 hy.1
  · rw [← toF_p, he]; exact hA
  · rw [← toF_n, he]; exact hB

theorem toF_negMP {n x : ℕ} (hn : n ≤ 16) (hx : GdB n x) :
    toF (negMP x) = F3P.neg (toF x) ∧ GdB n (negMP x) := by
  have he : toF (negMP x) = F3P.neg (toF x) := by
    unfold negMP
    rw [toF_mpOf (hx.2.2.trans_le (Nat.pow_le_pow_right (by norm_num) hn))]
    rfl
  refine ⟨he, ?_, ?_, ?_⟩
  · rw [he]; exact F3P.valid_neg hx.1
  · rw [← toF_p, he]; exact hx.2.2
  · rw [← toF_n, he]; exact hx.2.1

theorem blt_bit (v j : ℕ) :
    Nat.blt (nat_lit 0) (Nat.land v (Nat.shiftLeft (nat_lit 1) j)) = v.testBit j := by
  change Nat.blt 0 (v &&& (1 <<< j)) = _
  rw [nblt, Nat.one_shiftLeft, Nat.and_two_pow]
  cases v.testBit j <;> simp

theorem lt_of_testBit_false {x m : ℕ} (h : x < 2 ^ (m + 1)) (hb : x.testBit m = false) :
    x < 2 ^ m := by
  refine Nat.lt_pow_two_of_testBit x fun i hi => ?_
  rcases Nat.eq_or_lt_of_le hi with rfl | hi
  · exact hb
  · exact Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right (by norm_num) hi))

theorem bits_of_cf {a : F3P} (hv : a.Valid) {i : ℕ} (h : a.cf i = 0) :
    a.p.testBit i = false ∧ a.n.testBit i = false := by
  have hn := hv.not_both i
  unfold F3P.cf at h
  cases hp : a.p.testBit i <;> cases hq : a.n.testBit i <;> simp_all

@[expose] def FOK (m F : ℕ) : Prop :=
  (toF F).Valid ∧ mpP F >>> m = 1 ∧ mpN F >>> m = 0

theorem FOK.gdB {m F : ℕ} (h : FOK m F) : GdB (m + 1) F := by
  refine ⟨h.1, ?_, ?_⟩
  · have := h.2.1
    rw [Nat.shiftRight_eq_div_pow] at this
    have h2 := Nat.lt_div_mul_add (a := mpP F) (b := 2 ^ m) (by positivity)
    rw [this, pow_succ] at *
    omega
  · have := h.2.2
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at this
    rcases this with h0 | h0
    · exact absurd h0 (by positivity)
    · exact h0.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem FOK.bitP {m F : ℕ} (h : FOK m F) : (mpP F).testBit m = true := by
  have := h.2.1
  rw [Nat.shiftRight_eq_div_pow] at this
  rw [Nat.testBit_eq_decide_div_mod_eq, this]
  rfl

theorem FOK.bitN {m F : ℕ} (h : FOK m F) : (mpN F).testBit m = false := by
  have := h.2.2
  rw [Nat.shiftRight_eq_div_pow] at this
  rw [Nat.testBit_eq_decide_div_mod_eq, this]
  rfl

theorem FOK.cf {m F : ℕ} (h : FOK m F) : (toF F).cf m = 1 := by
  simp [F3P.cf, toF_p, toF_n, h.bitP, h.bitN]

theorem toF_mulXMP {m F x : ℕ} (hm : m ≤ 15) (hF : FOK m F) (hx : GdB m x) :
    toF (mulXMP m F x) = F3P.red (toF F) m (F3P.mulX (toF x)) ∧ GdB m (mulXMP m F x) := by
  have hp1 : Nat.shiftLeft (mpP x) 1 < 2 ^ (m + 1) := by
    change mpP x <<< 1 < _
    rw [Nat.shiftLeft_eq, pow_one, pow_succ]
    have := hx.2.1
    omega
  have hn1 : Nat.shiftLeft (mpN x) 1 < 2 ^ (m + 1) := by
    change mpN x <<< 1 < _
    rw [Nat.shiftLeft_eq, pow_one, pow_succ]
    have := hx.2.2
    omega
  have h16 : 2 ^ (m + 1) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
  set y := mpOf (Nat.shiftLeft (mpP x) 1) (Nat.shiftLeft (mpN x) 1) with hy
  have hyF : toF y = F3P.mulX (toF x) := by
    rw [hy, toF_mpOf (hp1.trans_le h16)]
    rfl
  have hyp : mpP y = Nat.shiftLeft (mpP x) 1 := by rw [← toF_p, hyF]; rfl
  have hyn : mpN y = Nat.shiftLeft (mpN x) 1 := by rw [← toF_n, hyF]; rfl
  have hyG : GdB (m + 1) y :=
    ⟨by rw [hyF]; exact F3P.valid_mulX hx.1, by rw [hyp]; exact hp1, by rw [hyn]; exact hn1⟩
  have hFG := hF.gdB
  obtain ⟨hnF, hnFG⟩ := toF_negMP (by omega) hFG
  unfold mulXMP
  rw [sN, ← hy, nIf_eq, nIf_eq, blt_bit, blt_bit]
  unfold F3P.red
  rw [← hyF, toF_p, toF_n]
  by_cases h1 : (mpP y).testBit m = true
  · obtain ⟨he, hg⟩ := toF_addMP (by omega) hyG hnFG
    rw [ite_eq_left h1, ite_eq_left h1, he, hnF]
    refine ⟨rfl, hg.1, ?_⟩
    have hcf : (toF (addMP y (negMP F))).cf m = 0 := by
      rw [he, F3P.cf_add hyG.1 hnFG.1, hnF, F3P.cf_neg, hF.cf]
      have hny : (mpN y).testBit m = false := by
        have := hyG.1.not_both m
        rw [toF_p, toF_n, h1] at this
        simpa using this
      simp [F3P.cf, toF_p, toF_n, h1, hny]
    obtain ⟨b1, b2⟩ := bits_of_cf hg.1 hcf
    rw [toF_p] at b1
    rw [toF_n] at b2
    exact ⟨lt_of_testBit_false hg.2.1 b1, lt_of_testBit_false hg.2.2 b2⟩
  · have h1' : (mpP y).testBit m = false := by simpa using h1
    rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : (mpN y).testBit m = true
    · obtain ⟨he, hg⟩ := toF_addMP (by omega) hyG hFG
      rw [ite_eq_left h2, ite_eq_left h2, he]
      refine ⟨rfl, hg.1, ?_⟩
      have hcf : (toF (addMP y F)).cf m = 0 := by
        rw [he, F3P.cf_add hyG.1 hFG.1, hF.cf]
        simp [F3P.cf, toF_p, toF_n, h1', h2]
      obtain ⟨b1, b2⟩ := bits_of_cf hg.1 hcf
      rw [toF_p] at b1
      rw [toF_n] at b2
      exact ⟨lt_of_testBit_false hg.2.1 b1, lt_of_testBit_false hg.2.2 b2⟩
    · have h2' : (mpN y).testBit m = false := by simpa using h2
      rw [ite_eq_right h2, ite_eq_right h2]
      exact ⟨rfl, hyG.1, lt_of_testBit_false hyG.2.1 h1', lt_of_testBit_false hyG.2.2 h2'⟩

@[expose] noncomputable def stepG (g x j a : ℕ) : ℕ :=
  nIf(Nat.blt (nat_lit 0) (Nat.land (mpP g) (Nat.shiftLeft (nat_lit 1) j)), addMP a x,
    nIf(Nat.blt (nat_lit 0) (Nat.land (mpN g) (Nat.shiftLeft (nat_lit 1) j)), addMP a (negMP x), a))

@[expose] noncomputable def mbR (m F g x : ℕ) (i : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun j ih acc => strictN (mulXMP m F acc) (fun a => strictN (stepG g x j a) ih)) i

theorem mulByG_eq (m F g dg x : ℕ) : mulByG m F g dg x = mbR m F g x (dg + 1) 0 := rfl

theorem mbR_succ (m F g x i acc : ℕ) :
    mbR m F g x (i + 1) acc = mbR m F g x i (stepG g x i (mulXMP m F acc)) := by
  change strictN (mulXMP m F acc) (fun a => strictN (stepG g x i a) (mbR m F g x i)) = _
  rw [sN, sN]

theorem toF_stepG {m g x a : ℕ} (hx : GdB m x) (ha : GdB m a) (hm : m ≤ 16) (j : ℕ) :
    toF (stepG g x j a) = F3P.smulBit (toF g) j (toF x) (toF a) ∧ GdB m (stepG g x j a) := by
  unfold stepG F3P.smulBit
  rw [nIf_eq, nIf_eq, blt_bit, blt_bit, toF_p, toF_n]
  split_ifs
  · exact toF_addMP hm ha hx
  · obtain ⟨h1, h2⟩ := toF_negMP hm hx
    obtain ⟨h3, h4⟩ := toF_addMP hm ha h2
    exact ⟨by rw [h3, h1]; rfl, h4⟩
  · exact ⟨rfl, ha⟩

theorem toF_mbR {m F g x : ℕ} (hm : m ≤ 15) (hF : FOK m F) (hx : GdB m x) :
    ∀ (i acc : ℕ), GdB m acc → toF (mbR m F g x i acc) =
      F3P.mulModAux (toF F) m (toF x) (toF g) i (toF acc) ∧ GdB m (mbR m F g x i acc)
  | 0, acc, h => ⟨rfl, h⟩
  | i + 1, acc, h => by
    obtain ⟨h1, h2⟩ := toF_mulXMP hm hF h
    obtain ⟨h3, h4⟩ := toF_stepG hx h2 (by omega) i
    obtain ⟨h5, h6⟩ := toF_mbR hm hF hx i _ h4
    rw [mbR_succ, F3P.mulModAux, h5, h3, h1]
    exact ⟨rfl, h6⟩

@[expose] def GOK (g dg : ℕ) : Prop := (toF g).Valid ∧ (mpP g ||| mpN g) >>> (dg + 1) = 0

theorem ev_mulByG {R : Type*} [CommRing R] {ι : ZMod 3 →+* R} {r : R} {m F g dg x : ℕ}
    (hm : m ≤ 15) (hF : FOK m F) (hf0 : F3P.ev ι r (toF F) = 0) (hg : GOK g dg) (hx : GdB m x) :
    F3P.ev ι r (toF (mulByG m F g dg x)) = F3P.ev ι r (toF x) * F3P.ev ι r (toF g) ∧
      GdB m (mulByG m F g dg x) := by
  have h0 : GdB m 0 := ⟨F3P.valid_zero, by positivity, by positivity⟩
  obtain ⟨h1, h2⟩ := toF_mbR (g := g) hm hF hx (dg + 1) 0 h0
  rw [mulByG_eq, h1, toF_zero, F3P.ev_mulModAux hF.1 hx.1 hg.1 hf0 _ F3P.valid_zero, F3P.ev_zero,
    zero_mul, zero_add]
  refine ⟨?_, h2⟩
  have hb := hg.2
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hb
  have hb' : (mpP g ||| mpN g) < 2 ^ (dg + 1) := by
    rcases hb with h | h
    · exact absurd h (by positivity)
    · exact h
  rw [F3P.ev_eq_sum (a := toF g) (N := dg + 1) (Nat.left_le_or.trans_lt hb')
    (Nat.right_le_or.trans_lt hb')]

theorem fld_one (a i : ℕ) : Nat.land (Nat.shiftRight a i) (nat_lit 1) = (a.testBit i).toNat := by
  change (a >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

theorem coeff_decL (x i : ℕ) :
    (CFSG.KC.Misc.Ree.decL x).coeff i = ((x / 2 ^ (32 * i) % 2 ^ 32 : ℕ) : ZMod 3) := by
  rw [CFSG.KC.Misc.Ree.decL, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have hx : x < 2 ^ (32 * i) := by
      simp only [Finset.mem_range, not_lt] at h
      calc x ≤ i := h
        _ < 2 ^ i := Nat.lt_two_pow_self
        _ ≤ 2 ^ (32 * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.div_eq_of_lt hx]
    simp

theorem decL_lanesOf {m F : ℕ} (hF : FOK m F) :
    CFSG.KC.Misc.Ree.decL (lanesOf m F) = F3P.decode (toF F) := by
  symm
  refine F3P.decode_eq_of_cf fun i => ?_
  rw [coeff_decL]
  set v : ℕ → ℕ := fun i => ((mpP F).testBit i).toNat + 2 * ((mpN F).testBit i).toNat with hv
  have hv' : ∀ i, v i < 2 ^ 32 := by
    intro i
    simp only [hv]
    cases (mpP F).testBit i <;> cases (mpN F).testBit i <;> simp
  have hL : lanesOf m F =
      loopN (m + 1) 0 (fun i L => Nat.lor L (Nat.shiftLeft (v i) (Nat.mul 32 i))) 0 := by
    unfold lanesOf
    simp only [fld_one]
    rfl
  have hlane : lanesOf m F / 2 ^ (32 * i) % 2 ^ 32 = if i ≤ m then v i else 0 := by
    rw [← fld_eq_mod, hL]
    split_ifs with h
    · exact fld_loopN_or (by norm_num) hv' (by omega) (by omega)
    · exact fld_loopN_or_out (by norm_num) hv' (by omega)
  rw [hlane]
  have hnb := hF.1.not_both i
  rw [toF_p, toF_n] at hnb
  split_ifs with h
  · simp only [hv, F3P.cf, toF_p, toF_n]
    have key : ∀ a b : Bool, ¬ (a = true ∧ b = true) →
        ((if a = true then (1 : ZMod 3) else 0) - if b = true then 1 else 0) =
          ((a.toNat + 2 * b.toNat : ℕ) : ZMod 3) := by decide
    exact key _ _ hnb
  · have hG := hF.gdB
    have h1 : (mpP F).testBit i = false :=
      Nat.testBit_lt_two_pow (hG.2.1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h2 : (mpN F).testBit i = false :=
      Nat.testBit_lt_two_pow (hG.2.2.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [F3P.cf, toF_p, toF_n, h1, h2]

theorem exists_root {m F Fl G M15 ML nb : ℕ} (hm : 1 ≤ m) (hF : FOK m F)
    (hlanes : Nat.beq Fl (lanesOf m F) = true)
    (hsetup : CFSG.KC.Misc.Ree.setupK m Fl G M15 ML = true)
    (hroot : CFSG.KC.Misc.Ree.rootK m G M15 ML nb = true) :
    ∃ r : GaloisField 3 m, F3P.ev (castThree (GaloisField 3 m)) r (toF F) = 0 := by
  obtain ⟨h1, h2⟩ := CFSG.KC.Misc.Ree.root_sound hsetup hroot
  rw [Nat.eq_of_beq_eq_true hlanes, decL_lanesOf hF] at h1 h2
  let _ : Fintype (GaloisField 3 m) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 m) = 3 ^ m := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 3 m (by omega)
  obtain ⟨r, hr⟩ := exists_root_of_dvd hm hcard h1 h2
  exact ⟨r, by rw [F3P.ev_def]; exact hr⟩

theorem field_env {m F g dg q1 hf ET ZT D Fl G M15 ML nb : ℕ}
    (hhead : headOK m F g dg q1 hf ET ZT D = true)
    (hchain : chainOK m F g dg q1 ET 0 q1 = true)
    (hzech : zechOK q1 ET ZT 0 q1 = true)
    (hlanes : Nat.beq Fl (lanesOf m F) = true)
    (hsetup : CFSG.KC.Misc.Ree.setupK m Fl G M15 ML = true)
    (hroot : CFSG.KC.Misc.Ree.rootK m G M15 ML nb = true) :
    ∃ γ : GaloisField 3 m, LogEnv q1 hf ZT γ ∧ (∀ j, 1 ≤ j → j ≤ D → γ ^ j ≠ 1) ∧ D ≤ hf := by
  unfold headOK at hhead
  simp only [bA] at hhead
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hhead
  have hm2 : 2 ≤ m := Nat.le_of_ble_eq_true h1
  have hm16 : m < 16 := by rw [Nat.blt_eq] at h2; exact h2
  have hq : q1 = 3 ^ m - 1 := Nat.eq_of_beq_eq_true h3
  have hhf : hf = q1 / 2 := Nat.eq_of_beq_eq_true h4
  have hFOK : FOK m F :=
    ⟨(F3P.valid_iff _).mpr (Nat.eq_of_beq_eq_true h5), Nat.eq_of_beq_eq_true h6,
      Nat.eq_of_beq_eq_true h7⟩
  have hdg : dg < m := by rw [Nat.blt_eq] at h9; exact h9
  have hGOK : GOK g dg :=
    ⟨(F3P.valid_iff _).mpr (Nat.eq_of_beq_eq_true h8), Nat.eq_of_beq_eq_true h10⟩
  have h0 : etAt ET 0 = 1 := Nat.eq_of_beq_eq_true h11
  have hhfv : etAt ET hf = mpOf 0 1 := Nat.eq_of_beq_eq_true h12
  have hD : D ≤ hf := Nat.le_of_ble_eq_true h13
  have h9m : 9 ≤ 3 ^ m := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hq0 : 0 < q1 := by omega
  have hhq : hf < q1 := by omega
  obtain ⟨r, hr⟩ := exists_root (by omega) hFOK hlanes hsetup hroot
  set ι := castThree (GaloisField 3 m)
  set γ : GaloisField 3 m := F3P.ev ι r (toF g) with hγ
  have hm15 : m ≤ 15 := by omega
  have hone : GdB m 1 := ⟨F3P.valid_one, Nat.one_lt_two_pow (by omega), by positivity⟩
  unfold chainOK at hchain
  rw [allFrom_iff] at hchain
  have hstep : ∀ e < q1, mulByG m F g dg (etAt ET e) = etAt ET ((e + 1) % q1) :=
    fun e he => Nat.eq_of_beq_eq_true (hchain e (Nat.zero_le _) (by omega))
  have hET : ∀ e < q1, GdB m (etAt ET e) ∧ F3P.ev ι r (toF (etAt ET e)) = γ ^ e := by
    intro e
    induction e with
    | zero => intro _; rw [h0, toF_one, F3P.ev_one, pow_zero]; exact ⟨hone, rfl⟩
    | succ e ih =>
      intro he
      have hc := hstep e (by omega)
      rw [Nat.mod_eq_of_lt he] at hc
      obtain ⟨g1, g2⟩ := ih (by omega)
      obtain ⟨g3, g4⟩ := ev_mulByG hm15 hFOK hr hGOK g1
      rw [hc] at g3 g4
      exact ⟨g4, by rw [g3, g2, pow_succ]⟩
  have hpq : γ ^ q1 = 1 := by
    have hc := hstep (q1 - 1) (by omega)
    rw [Nat.sub_add_cancel hq0, Nat.mod_self, h0] at hc
    obtain ⟨g1, g2⟩ := hET (q1 - 1) (by omega)
    obtain ⟨g3, -⟩ := ev_mulByG hm15 hFOK hr hGOK g1
    rw [hc, toF_one, F3P.ev_one, g2, ← pow_succ, Nat.sub_add_cancel hq0] at g3
    exact g3.symm
  have hph : γ ^ hf = -1 := by
    rw [← (hET hf hhq).2, hhfv, toF_mpOf (by norm_num)]
    have : (⟨0, 1⟩ : F3P) = F3P.neg F3P.one := rfl
    rw [this, F3P.ev_neg, F3P.ev_one]
  unfold zechOK at hzech
  rw [allFrom_iff] at hzech
  have hZ : ∀ d < q1, zech ZT d ≤ q1 ∧ 1 + γ ^ d = phi q1 γ (zech ZT d) := by
    intro d hd
    have hz := hzech d (Nat.zero_le _) (by omega)
    rw [sB, sB, bIf_eq] at hz
    obtain ⟨g1, g2⟩ := hET d hd
    obtain ⟨g3, -⟩ := toF_addMP (by omega) hone g1
    have hv : F3P.ev ι r (toF (addMP 1 (etAt ET d))) = 1 + γ ^ d := by
      rw [g3, toF_one, F3P.ev_add F3P.valid_one g1.1, F3P.ev_one, g2]
    split_ifs at hz with hzq
    · have e1 : zech ZT d = q1 := Nat.eq_of_beq_eq_true hzq
      have e2 : addMP 1 (etAt ET d) = 0 := Nat.eq_of_beq_eq_true hz
      rw [e2, toF_zero, F3P.ev_zero] at hv
      rw [e1, phi_q1, ← hv]
      exact ⟨le_rfl, rfl⟩
    · rw [bA] at hz
      have e1 : zech ZT d < q1 := by rw [Nat.blt_eq] at hz; exact hz.1
      have e2 : etAt ET (zech ZT d) = addMP 1 (etAt ET d) := Nat.eq_of_beq_eq_true hz.2
      refine ⟨e1.le, ?_⟩
      rw [phi_lt e1, ← (hET _ e1).2, e2, hv]
  have E : LogEnv q1 hf ZT γ :=
    ⟨hq0, hhq, hpq, hph, fun d hd => (hZ d hd).1, fun d hd => (hZ d hd).2⟩
  refine ⟨γ, E, fun j hj1 hj2 => ?_, hD⟩
  rw [allFrom_iff] at h14
  have hj := h14 j hj1 (by omega)
  rw [bNot] at hj
  have hne : zech ZT ((j + hf) % q1) ≠ q1 := Nat.ne_of_beq_eq_false hj
  have hlt : (j + hf) % q1 < q1 := Nat.mod_lt _ hq0
  have h1 := E.zech_eq _ hlt
  have h2 := E.phi_ne_zero (E.zech_le _ hlt) hne
  rw [← h1, E.pow_mod, pow_add, hph] at h2
  intro hj1'
  rw [hj1'] at h2
  exact h2 (by ring)

end CFSG.KC.Misc.Ree2

end
