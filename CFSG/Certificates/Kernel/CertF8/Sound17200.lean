module

public import Certificates.Data.Kernel.CertF8.Syl17200
public import CFSG.Certificates.Kernel.CertF8.F64Sound
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.ElemCover

public section

namespace CFSG.KC.CertF8.S17200

open CFSG.HardMathSupport.Dickson.Sec6.Gen3D4 CFSG.Open CFSG.AGLEmbedding.ChevOuter
open CFSG.KC.CertF8 CFSG.KC.CertF8.G64
open CFSG.KC.G28 (fld)
open CFSG.KC.Misc.Clos (andB_eq_true letB_eq impB_eq_true allN_iff allR_iff sort_distinct treeAt
  sortAt closedAt)

theorem fld_eq (x o m : ℕ) : fld x o m = x / 2 ^ o % 2 ^ m := by
  rw [fld, Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
  change x >>> o &&& 2 ^ m - 1 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem bitB_iff (x i : ℕ) : bitB x i = true ↔ x.testBit i = true := by
  rw [bitB, Nat.beq_eq, fld_eq, pow_one, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

theorem eqB_eq {a b : Bool} (h : eqB a b = true) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem testBit_orN (f : ℕ → ℕ) (i : ℕ) :
    ∀ m, (orN m f).testBit i = true → ∃ n < m, (f n).testBit i = true
  | 0, h => by
    change (0 : ℕ).testBit i = true at h
    simp at h
  | m + 1, h => by
    change (f m ||| orN m f).testBit i = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨m, by omega, h⟩
    · obtain ⟨n, hn, h'⟩ := testBit_orN f i m h
      exact ⟨n, by omega, h'⟩

theorem testBit_shift_one {v i : ℕ} (h : (Nat.shiftLeft 1 v).testBit i = true) : v = i := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at h
  exact of_decide_eq_true h

theorem bits_of_land {w u : ℕ} (h : Nat.beq (Nat.land w u) w = true) {i : ℕ}
    (hw : w.testBit i = true) : u.testBit i = true := by
  have e : w &&& u = w := Nat.eq_of_beq_eq_true h
  have := congrArg (fun z => z.testBit i) e
  simp only [Nat.testBit_and, hw, Bool.true_and] at this
  exact this

set_option exponentiation.threshold 400 in
theorem codeA64_lt (A : Array GF64) : codeA64 A < 2 ^ 384 := by
  have hc := CFSG.KC.Misc.G2U.pk_lt (codeA64_lt_list A)
  rw [List.length_map, List.length_range] at hc
  exact hc

set_option exponentiation.threshold 400 in
theorem keyQ_eq (c j : ℕ) : keyQ (c, j) = c + 2 ^ 384 * j := by
  have e : keyQ (c, j) = c + j <<< 384 := rfl
  rw [e, Nat.shiftLeft_eq, Nat.mul_comm j]

set_option exponentiation.threshold 400 in
theorem unkey_keyQ {c j : ℕ} (hc : c < 2 ^ 384) : unkey (keyQ (c, j)) = (c, j) := by
  rw [keyQ_eq, unkey, fld_eq, pow_zero, Nat.div_one, Nat.shiftRight_eq',
    Nat.shiftRight_eq_div_pow]
  generalize hB : (2 : ℕ) ^ 384 = B at hc ⊢
  have hB0 : 0 < B := by omega
  refine Prod.ext ?_ ?_
  · change (c + B * j) % B = c
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · change (c + B * j) / B = j
    rw [Nat.add_mul_div_left _ _ hB0, Nat.div_eq_of_lt hc, zero_add]

@[expose] noncomputable def keyP (p : Pr) : ℕ := keyQ (codePr64 p)

theorem keyP_mul (p q : Pr) : keyP (mulP p q) = mulK (keyP p) (keyP q) := by
  rw [keyP, codePr64_mulP, mulK, keyP, keyP, codePr64, codePr64, unkey_keyQ (codeA64_lt _),
    unkey_keyQ (codeA64_lt _)]

theorem keyP_inj {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64) (h : keyP p = keyP q) :
    p = q := by
  have e := congrArg unkey h
  rw [keyP, keyP, codePr64, codePr64, unkey_keyQ (codeA64_lt _), unkey_keyQ (codeA64_lt _)] at e
  exact codePr64_inj hp hq e

theorem keyP_one (h1 : codePr64 oneP = oneQ) : keyP oneP = oneK := by
  unfold keyP
  rw [h1]
  change keyQ (oneK, 0) = oneK
  rw [keyQ_eq, Nat.mul_zero, Nat.add_zero]

theorem codePr64_word (hsym : ∀ s, codePr64 (symP s) = symQ s) (h1 : codePr64 oneP = oneQ) :
    ∀ w : List ℕ, codePr64 (wordP w) = wordQ w
  | [] => h1
  | s :: w => by
    change codePr64 (mulP (symP s) (wordP w)) = mulPr64 (symQ s) (wordQ w)
    rw [codePr64_mulP, hsym, codePr64_word hsym h1 w]

theorem keyP_word (hsym : ∀ s, codePr64 (symP s) = symQ s) (h1 : codePr64 oneP = oneQ)
    (w : List ℕ) : keyP (wordP w) = keyQ (wordQ w) := by
  unfold keyP
  rw [codePr64_word hsym h1 w]

theorem snd_wordP_lt (w : List ℕ) : (wordP w).2 < 3 := by
  cases w with
  | nil => exact Nat.zero_lt_succ _
  | cons s w => exact snd_mulP_lt _ _

variable {X : Type} [Group X] (R : Realization X)

@[expose] def RK (k : ℕ) (x : X) : Prop := ∃ p : Pr, p.1.size = 64 ∧ keyP p = k ∧ R.Rep p x

theorem RK_mul {a b : ℕ} {x y : X} (ha : RK R a x) (hb : RK R b y) : RK R (mulK a b) (x * y) := by
  obtain ⟨p, hp, rfl, hpx⟩ := ha
  obtain ⟨q, hq, rfl, hqy⟩ := hb
  exact ⟨mulP p q, size_mulP _ _, keyP_mul p q, R.rep_mul hpx hqy⟩

theorem RK_one (h1 : codePr64 oneP = oneQ) : RK R oneK 1 :=
  ⟨oneP, size_oneP, keyP_one h1, R.rep_one⟩

theorem RK_ext {k : ℕ} {x y : X} (hx : RK R k x) (hy : RK R k y) : x = y := by
  obtain ⟨p, hp, hpk, hpx⟩ := hx
  obtain ⟨q, hq, hqk, hqy⟩ := hy
  exact R.rep_ext hpx hqy (keyP_inj hp hq (hpk.trans hqk.symm))

theorem RK_inj {a b : ℕ} {x : X} (ha : RK R a x) (hb : RK R b x) : a = b := by
  obtain ⟨p, -, rfl, hpx⟩ := ha
  obtain ⟨q, -, rfl, hqx⟩ := hb
  rw [R.rep_inj hpx hqx]

theorem RK_word (hsym : ∀ s, codePr64 (symP s) = symQ s) (h1 : codePr64 oneP = oneQ)
    (w : List ℕ) : RK R (keyQ (wordQ w)) (R.wordElt w) :=
  ⟨wordP w, size_wordP w, keyP_word hsym h1 w, R.rep_word w⟩

structure RowFacts (T : ℕ → ℕ) (j : ℕ) : Prop where
  root : j = 0 → E T 0 = oneK
  tree : 0 < j → fld (T j) 386 8 < j ∧ E T j = mulK (E T (fld (T j) 386 8)) (G T (fld (T j) 394 2))
  sort : sortAt 243 (E T) (SG T) j = true
  closR : ∀ l < 4, CR T (j * 4 + l) < 243 ∧ E T (CR T (j * 4 + l)) = mulK (E T j) (G T l)
  closL : ∀ l < 4, CL T (j * 4 + l) < 243 ∧ E T (CL T (j * 4 + l)) = mulKL (E T j) (G T l)
  tab0 : j = 0 → ∀ i < 243, colF (T j) i = i ∧ rowF (T j) i = i
  tabS : 0 < j → ∀ i < 243,
    colF (T j) i = fld (T (243 + fld (T j) 394 2)) (386 + 8 * colF (T (fld (T j) 386 8)) i) 8 ∧
    rowF (T j) i = rowF (T (fld (T j) 386 8)) (fld (T (243 + fld (T j) 394 2)) (2330 + 8 * i) 8)
  cube : bitB (T 247) j = Nat.beq (rowF (T j) (rowF (T j) j)) 0
  cm : ∀ i < 243, bitB (cmF (T j)) i =
    CFSG.KC.Ord.andB (bitB (T 247) i) (Nat.beq (rowF (T j) i) (colF (T j) i))

theorem pa_lo (p l : ℕ) (hp : p < 256) : Nat.land (Nat.add p (Nat.mul 16777216 l)) 16777215 = p := by
  rw [Nat.land_eq]
  change (p + 2 ^ 24 * l) &&& 2 ^ 24 - 1 = p
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem pa_hi (p l : ℕ) (hp : p < 256) : Nat.shiftRight (Nat.add p (Nat.mul 16777216 l)) 24 = l := by
  rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  change (p + 2 ^ 24 * l) / 2 ^ 24 = l
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), zero_add]

theorem fld_lt (x o m : ℕ) : fld x o m < 2 ^ m := by
  rw [fld_eq]
  exact Nat.mod_lt _ (by positivity)

theorem cr_eq (T : ℕ → ℕ) (c l : ℕ) (hl : l < 4) :
    CR T (c * 4 + l) = fld (T (243 + l)) (386 + 8 * c) 8 := by
  have h1 : (c * 4 + l) % 4 = l := by omega
  have h2 : (c * 4 + l) / 4 = c := by omega
  change fld (T (243 + (c * 4 + l) % 4)) (386 + 8 * ((c * 4 + l) / 4)) 8 = _
  rw [h1, h2]

theorem cl_eq (T : ℕ → ℕ) (c l : ℕ) (hl : l < 4) :
    CL T (c * 4 + l) = fld (T (243 + l)) (2330 + 8 * c) 8 := by
  have h1 : (c * 4 + l) % 4 = l := by omega
  have h2 : (c * 4 + l) / 4 = c := by omega
  change fld (T (243 + (c * 4 + l) % 4)) (2330 + 8 * ((c * 4 + l) / 4)) 8 = _
  rw [h1, h2]

theorem rowFacts_of {T : ℕ → ℕ} {j : ℕ} (h : rowAt T j = true) : RowFacts T j := by
  rw [rowAt] at h
  obtain ⟨htr, h⟩ := andB_eq_true h
  obtain ⟨hso, h⟩ := andB_eq_true h
  obtain ⟨hcr, h⟩ := andB_eq_true h
  obtain ⟨hcl, h⟩ := andB_eq_true h
  obtain ⟨hta, h⟩ := andB_eq_true h
  obtain ⟨hcu, hcm⟩ := andB_eq_true h
  have hclos : ∀ (M : ℕ → ℕ → ℕ) (CT : ℕ → ℕ), closedAt M (G T) 4 243 (E T) CT j = true →
      ∀ l < 4, CT (j * 4 + l) < 243 ∧ E T (CT (j * 4 + l)) = M (E T j) (G T l) := by
    intro M CT hc l hl
    have h := (allN_iff _ _).1 hc l hl
    rw [letB_eq] at h
    obtain ⟨h1, h2⟩ := andB_eq_true h
    exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩
  have hp8 : fld (T j) 386 8 < 256 := fld_lt _ _ _
  refine ⟨fun hj => ?_, fun hj => ?_, ?_, hclos _ _ hcr, hclos _ _ hcl, fun hj => ?_,
    fun hj => ?_, ?_, ?_⟩
  · subst hj
    exact Nat.eq_of_beq_eq_true htr
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    change CFSG.KC.LQT.P.letB (PA T (k + 1)) (fun r => CFSG.KC.LQT.P.letB (Nat.land r 16777215)
      fun p => CFSG.KC.LQT.P.letB (Nat.shiftRight r 24) fun l => CFSG.KC.Ord.andB (Nat.blt p (k + 1))
        (CFSG.KC.Ord.andB (Nat.blt l 4) (Nat.beq (E T (k + 1)) (mulK (E T p) (G T l))))) = true
      at htr
    rw [letB_eq, letB_eq, letB_eq, PA, pa_lo _ _ hp8, pa_hi _ _ hp8] at htr
    obtain ⟨h1, h⟩ := andB_eq_true htr
    obtain ⟨-, h3⟩ := andB_eq_true h
    exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h3⟩
  · exact hso
  · subst hj
    intro i hi
    rw [tabAt, letB_eq] at hta
    have h := (allN_iff _ _).1 hta i hi
    obtain ⟨h1, h2⟩ := andB_eq_true h
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    intro i hi
    rw [tabAt, letB_eq] at hta
    change CFSG.KC.LQT.P.letB (T (fld (T (k + 1)) 386 8)) (fun rp =>
      CFSG.KC.LQT.P.letB (T (Nat.add 243 (fld (T (k + 1)) 394 2))) fun g =>
      CFSG.KC.LQT.P.allN 243 fun i =>
        CFSG.KC.Ord.andB (Nat.beq (colF (T (k + 1)) i)
          (fld g (Nat.add 386 (Nat.mul 8 (colF rp i))) 8))
          (Nat.beq (rowF (T (k + 1)) i) (rowF rp (fld g (Nat.add 2330 (Nat.mul 8 i)) 8)))) = true
      at hta
    rw [letB_eq, letB_eq] at hta
    have h := (allN_iff _ _).1 hta i hi
    obtain ⟨h1, h2⟩ := andB_eq_true h
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
  · rw [cubeAt, letB_eq] at hcu
    exact eqB_eq hcu
  · intro i hi
    rw [cmAt, letB_eq, letB_eq, letB_eq] at hcm
    exact eqB_eq ((allN_iff _ _).1 hcm i hi)

variable [Finite X]

structure Hyp (T : ℕ → ℕ) : Prop where
  sym : ∀ s, codePr64 (symP s) = symQ s
  one : codePr64 oneP = oneQ
  row : ∀ j < 243, RowFacts T j
  gen : ∀ k < 4, G T k = keyQ (wordQ (sylowGenW.getD k []))
  misc : miscOK T = true
  h3 : ∀ x < 243, h3At T x = true

theorem gens_of {T : ℕ → ℕ} (h : miscOK T = true) :
    ∀ k < 4, G T k = keyQ (wordQ (sylowGenW.getD k [])) := by
  rw [miscOK] at h
  have h1 := (andB_eq_true h).1
  rw [genOK] at h1
  exact fun k hk => Nat.eq_of_beq_eq_true ((allN_iff _ _).1 h1 k hk)

theorem hyp_of {T : ℕ → ℕ} (hsym : ∀ s, codePr64 (symP s) = symQ s)
    (h1 : codePr64 oneP = oneQ) (hr : ∀ j < 243, rowAt T j = true) (hm : miscOK T = true)
    (h3 : ∀ x < 243, h3At T x = true) : Hyp T :=
  ⟨hsym, h1, fun j hj => rowFacts_of (hr j hj), gens_of hm, hm, h3⟩

@[expose] def gR (k : ℕ) : X := R.wordElt (sylowGenW.getD k [])

theorem RK_gen {T : ℕ → ℕ} (hT : Hyp T) {k : ℕ} (hk : k < 4) : RK R (G T k) (gR R k) := by
  rw [hT.gen k hk]
  exact RK_word R hT.sym hT.one _

theorem exists_el {T : ℕ → ℕ} (hT : Hyp T) : ∀ n < 243, ∃ x, RK R (E T n) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨1, by rw [(hT.row 0 hn).root rfl]; exact RK_one R hT.one⟩
    · obtain ⟨hp, he⟩ := (hT.row n hn).tree hpos
      obtain ⟨x, hx⟩ := ih _ hp (by omega)
      refine ⟨x * gR R (fld (T n) 394 2), ?_⟩
      rw [he]
      exact RK_mul R hx (RK_gen R hT (fld_lt _ _ _))

@[expose] noncomputable def el {T : ℕ → ℕ} (hT : Hyp T) (n : ℕ) : X :=
  if h : n < 243 then Classical.choose (exists_el R hT n h) else 1

theorem el_rk {T : ℕ → ℕ} (hT : Hyp T) {n : ℕ} (hn : n < 243) : RK R (E T n) (el R hT n) := by
  unfold el
  rw [dif_pos hn]
  exact Classical.choose_spec (exists_el R hT n hn)

theorem el_zero {T : ℕ → ℕ} (hT : Hyp T) : el R hT 0 = 1 := by
  refine RK_ext R (el_rk R hT (by norm_num)) ?_
  rw [(hT.row 0 (by norm_num)).root rfl]
  exact RK_one R hT.one

theorem el_inj {T : ℕ → ℕ} (hT : Hyp T) {i j : ℕ} (hi : i < 243) (hj : j < 243)
    (h : el R hT i = el R hT j) : i = j := by
  exact sort_distinct (fun i hi => (hT.row i hi).sort) i hi j hj
    (RK_inj R (el_rk R hT hi) (h ▸ el_rk R hT hj))

theorem el_par {T : ℕ → ℕ} (hT : Hyp T) {j : ℕ} (hj : j < 243) (hpos : 0 < j) :
    el R hT j = el R hT (fld (T j) 386 8) * gR R (fld (T j) 394 2) := by
  obtain ⟨hp, he⟩ := (hT.row j hj).tree hpos
  refine RK_ext R (el_rk R hT hj) ?_
  rw [he]
  exact RK_mul R (el_rk R hT (by omega)) (RK_gen R hT (fld_lt _ _ _))

theorem el_R {T : ℕ → ℕ} (hT : Hyp T) {c l : ℕ} (hc : c < 243) (hl : l < 4) :
    fld (T (243 + l)) (386 + 8 * c) 8 < 243 ∧
      el R hT (fld (T (243 + l)) (386 + 8 * c) 8) = el R hT c * gR R l := by
  obtain ⟨h1, h2⟩ := (hT.row c hc).closR l hl
  rw [cr_eq T c l hl] at h1 h2
  refine ⟨h1, RK_ext R (el_rk R hT h1) ?_⟩
  rw [h2]
  exact RK_mul R (el_rk R hT hc) (RK_gen R hT hl)

theorem el_L {T : ℕ → ℕ} (hT : Hyp T) {c l : ℕ} (hc : c < 243) (hl : l < 4) :
    fld (T (243 + l)) (2330 + 8 * c) 8 < 243 ∧
      el R hT (fld (T (243 + l)) (2330 + 8 * c) 8) = gR R l * el R hT c := by
  obtain ⟨h1, h2⟩ := (hT.row c hc).closL l hl
  rw [cl_eq T c l hl, mulKL] at h2
  rw [cl_eq T c l hl] at h1
  refine ⟨h1, RK_ext R (el_rk R hT h1) ?_⟩
  rw [h2]
  exact RK_mul R (RK_gen R hT hl) (el_rk R hT hc)

theorem el_tab {T : ℕ → ℕ} (hT : Hyp T) : ∀ j < 243, ∀ i < 243,
    (colF (T j) i < 243 ∧ el R hT (colF (T j) i) = el R hT i * el R hT j) ∧
      (rowF (T j) i < 243 ∧ el R hT (rowF (T j) i) = el R hT j * el R hT i) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i hi
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · obtain ⟨h1, h2⟩ := (hT.row 0 hj).tab0 rfl i hi
      rw [h1, h2, el_zero R hT, mul_one, one_mul]
      exact ⟨⟨hi, rfl⟩, ⟨hi, rfl⟩⟩
    · obtain ⟨hp, -⟩ := (hT.row j hj).tree hpos
      have hl : fld (T j) 394 2 < 4 := fld_lt _ _ _
      obtain ⟨h1, h2⟩ := (hT.row j hj).tabS hpos i hi
      have hpar := el_par R hT hj hpos
      refine ⟨?_, ?_⟩
      · obtain ⟨⟨hc, hce⟩, -⟩ := ih _ hp (by omega) i hi
        obtain ⟨hr, hre⟩ := el_R R hT hc hl
        rw [h1]
        refine ⟨hr, ?_⟩
        rw [hre, hce, hpar, mul_assoc]
      · obtain ⟨hr, hre⟩ := el_L R hT hi hl
        obtain ⟨-, ⟨hc, hce⟩⟩ := ih _ hp (by omega) _ hr
        rw [h2]
        refine ⟨hc, ?_⟩
        rw [hce, hre, hpar, mul_assoc]

theorem el_mulI {T : ℕ → ℕ} (hT : Hyp T) {x y : ℕ} (hx : x < 243) (hy : y < 243) :
    mulI T x y < 243 ∧ el R hT (mulI T x y) = el R hT x * el R hT y :=
  (el_tab R hT x hx y hy).2

theorem el_powI {T : ℕ → ℕ} (hT : Hyp T) {x : ℕ} (hx : x < 243) :
    ∀ a, powI T x a < 243 ∧ el R hT (powI T x a) = el R hT x ^ a
  | 0 => ⟨by norm_num [powI], by rw [pow_zero]; exact el_zero R hT⟩
  | a + 1 => by
    obtain ⟨h1, h2⟩ := el_powI hT hx a
    obtain ⟨h3, h4⟩ := el_mulI R hT hx h1
    change mulI T x (powI T x a) < 243 ∧ el R hT (mulI T x (powI T x a)) = _
    exact ⟨h3, by rw [h4, h2, pow_succ']⟩

theorem cube_iff {T : ℕ → ℕ} (hT : Hyp T) {j : ℕ} (hj : j < 243) :
    bitB (T 247) j = true ↔ el R hT j ^ 3 = 1 := by
  obtain ⟨⟨-, -⟩, ⟨h1, h2⟩⟩ := el_tab R hT j hj j hj
  obtain ⟨⟨-, -⟩, ⟨h3, h4⟩⟩ := el_tab R hT j hj _ h1
  rw [(hT.row j hj).cube, Nat.beq_eq]
  constructor
  · intro h
    rw [h, el_zero R hT, h2] at h4
    rw [pow_three]
    exact h4.symm
  · intro h
    apply el_inj R hT h3 (by norm_num)
    rw [h4, h2, el_zero R hT, ← pow_three, h]

theorem cm_iff {T : ℕ → ℕ} (hT : Hyp T) {j i : ℕ} (hj : j < 243) (hi : i < 243) :
    bitB (cmF (T j)) i = true ↔ el R hT i ^ 3 = 1 ∧ Commute (el R hT j) (el R hT i) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := el_tab R hT j hj i hi
  rw [(hT.row j hj).cm i hi]
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := andB_eq_true h
    refine ⟨(cube_iff R hT hi).1 ha, ?_⟩
    have e := congrArg (el R hT) (Nat.eq_of_beq_eq_true hb)
    rw [h4, h2] at e
    exact e
  · rintro ⟨ha, hb⟩
    have hc : CFSG.KC.Ord.andB (bitB (T 247) i) (Nat.beq (rowF (T j) i) (colF (T j) i)) =
        CFSG.KC.Ord.andB true true := by
      rw [(cube_iff R hT hi).2 ha, el_inj R hT h3 h1 (by rw [h4, h2]; exact hb.eq),
        Nat.beq_refl]
    rw [hc]
    rfl

@[expose] def Psub {T : ℕ → ℕ} (hT : Hyp T) : Subgroup X where
  carrier := {x | ∃ n < 243, el R hT n = x}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := el_mulI R hT hi hj
    exact ⟨_, h1, h2⟩
  one_mem' := ⟨0, by norm_num, el_zero R hT⟩
  inv_mem' := by
    rintro x ⟨n, hn, rfl⟩
    have hpos : 0 < orderOf (el R hT n) := orderOf_pos _
    obtain ⟨h1, h2⟩ := el_powI R hT hn (orderOf (el R hT n) - 1)
    refine ⟨_, h1, ?_⟩
    rw [h2]
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]

theorem card_Psub {T : ℕ → ℕ} (hT : Hyp T) : Nat.card (Psub R hT) = 3 ^ 5 := by
  have hbij : Function.Bijective (fun i : Fin 243 => (⟨el R hT i, i, i.2, rfl⟩ : Psub R hT)) := by
    constructor
    · intro i j hij
      exact Fin.ext (el_inj R hT i.2 j.2 (congrArg Subtype.val hij))
    · rintro ⟨_, n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp

theorem misc_parts {T : ℕ → ℕ} (h : miscOK T = true) :
    eKeyOK T = true ∧ (∀ c < 4, eAt T c = true) ∧ (∀ t < 10, mAt T t = true) ∧
      ∀ t < 10, h4At T t = true := by
  rw [miscOK] at h
  obtain ⟨-, h⟩ := andB_eq_true h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h4⟩ := andB_eq_true h
  exact ⟨h1, (allN_iff _ _).1 h2, (allN_iff _ _).1 h3, (allN_iff _ _).1 h4⟩

theorem eI_facts {T : ℕ → ℕ} (hT : Hyp T) {c i : ℕ} (hc : c < 4) (hi : i < 3) :
    eI T (3 * c + i) < 243 ∧ el R hT (eI T (3 * c + i)) = R.ea c i := by
  have h := (allN_iff _ _).1 (misc_parts hT.misc).1 (3 * c + i) (by omega)
  rw [letB_eq] at h
  obtain ⟨h1, h2⟩ := andB_eq_true h
  have h1' := Nat.blt_eq.mp h1
  refine ⟨h1', RK_ext R (el_rk R hT h1') ?_⟩
  rw [Nat.eq_of_beq_eq_true h2]
  have e1 : (3 * c + i) / 3 = c := by omega
  have e2 : (3 * c + i) % 3 = i := by omega
  change RK R (keyQ (wordQ (eWord ((3 * c + i) / 3) ((3 * c + i) % 3)))) _
  rw [e1, e2]
  exact RK_word R hT.sym hT.one _

theorem eEl_facts {T : ℕ → ℕ} (hT : Hyp T) {c : ℕ} (hc : c < 4) {n : ℕ} :
    eEl T c n < 243 ∧ el R hT (eEl T c n) =
      R.ea c 0 ^ (n / 9) * R.ea c 1 ^ (n / 3 % 3) * R.ea c 2 ^ (n % 3) := by
  obtain ⟨h0, e0⟩ := eI_facts R hT hc (i := 0) (by norm_num)
  obtain ⟨h1, e1⟩ := eI_facts R hT hc (i := 1) (by norm_num)
  obtain ⟨h2, e2⟩ := eI_facts R hT hc (i := 2) (by norm_num)
  rw [Nat.add_zero] at h0 e0
  obtain ⟨p0, q0⟩ := el_powI R hT h0 (n / 9)
  obtain ⟨p1, q1⟩ := el_powI R hT h1 (n / 3 % 3)
  obtain ⟨p2, q2⟩ := el_powI R hT h2 (n % 3)
  obtain ⟨m1, r1⟩ := el_mulI R hT p0 p1
  obtain ⟨m2, r2⟩ := el_mulI R hT m1 p2
  change mulI T (mulI T (powI T (eI T (3 * c)) (n / 9)) (powI T (eI T (3 * c + 1)) (n / 3 % 3)))
    (powI T (eI T (3 * c + 2)) (n % 3)) < 243 ∧ el R hT (mulI T (mulI T (powI T (eI T (3 * c))
      (n / 9)) (powI T (eI T (3 * c + 1)) (n / 3 % 3))) (powI T (eI T (3 * c + 2)) (n % 3))) = _
  refine ⟨m2, ?_⟩
  rw [r2, r1, q0, q1, q2, e0, e1, e2]

theorem Eg_facts {T : ℕ → ℕ} (hT : Hyp T) {c : ℕ} (hc : c < 4) :
    IsElemAbelian 3 (R.Eg c) ∧ Nat.card (R.Eg c) = 27 := by
  obtain ⟨h0, e0⟩ := eI_facts R hT hc (i := 0) (by norm_num)
  obtain ⟨h1, e1⟩ := eI_facts R hT hc (i := 1) (by norm_num)
  obtain ⟨h2, e2⟩ := eI_facts R hT hc (i := 2) (by norm_num)
  rw [Nat.add_zero] at h0 e0
  have h := (misc_parts hT.misc).2.1 c hc
  rw [eAt, letB_eq, letB_eq, letB_eq] at h
  obtain ⟨b01, h⟩ := andB_eq_true h
  obtain ⟨b02, h⟩ := andB_eq_true h
  obtain ⟨b12, h⟩ := andB_eq_true h
  obtain ⟨b10, hind⟩ := andB_eq_true h
  obtain ⟨c1, c01⟩ := (cm_iff R hT h0 h1).1 b01
  obtain ⟨c2, c02⟩ := (cm_iff R hT h0 h2).1 b02
  obtain ⟨-, c12⟩ := (cm_iff R hT h1 h2).1 b12
  obtain ⟨c0, -⟩ := (cm_iff R hT h1 h0).1 b10
  rw [e0, e1, e2] at *
  have hind' : ∀ a b d : ℕ, a < 3 → b < 3 → d < 3 →
      R.ea c 0 ^ a * R.ea c 1 ^ b * R.ea c 2 ^ d = 1 → a = 0 ∧ b = 0 ∧ d = 0 := by
    intro a b d ha hb hd he
    by_contra hne
    have hn : 9 * a + 3 * b + d - 1 < 26 := by omega
    have hk := (allN_iff _ _).1 hind _ hn
    have es : Nat.succ (9 * a + 3 * b + d - 1) = 9 * a + 3 * b + d := by omega
    rw [es] at hk
    obtain ⟨hl, hel⟩ := eEl_facts R hT hc (n := 9 * a + 3 * b + d)
    have q1 : (9 * a + 3 * b + d) / 9 = a := by omega
    have q2 : (9 * a + 3 * b + d) / 3 % 3 = b := by omega
    have q3 : (9 * a + 3 * b + d) % 3 = d := by omega
    rw [q1, q2, q3, he, ← el_zero R hT] at hel
    have := el_inj R hT hl (by norm_num) hel
    rw [this, Nat.beq_refl] at hk
    exact absurd hk (by decide)
  obtain ⟨hcomm, hcube, hcard⟩ := closure_triple (R.ea c 0) (R.ea c 1) (R.ea c 2) c0 c1 c2 c01
    c02 c12 hind'
  exact ⟨⟨hcomm, hcube⟩, by rw [Realization.Eg, hcard]; norm_num⟩

@[expose] noncomputable def mc (T : ℕ → ℕ) (t : ℕ) : ℕ := fld (T (Nat.add 249 t)) 0 2

@[expose] noncomputable def mg (T : ℕ → ℕ) (t : ℕ) : ℕ := fld (T (Nat.add 249 t)) 2 8

@[expose] noncomputable def Mt {T : ℕ → ℕ} (hT : Hyp T) (t : ℕ) : Subgroup X :=
  (R.Eg (mc T t)).map (MulAut.conj (el R hT (mg T t))).toMonoidHom

theorem mc_lt (T : ℕ → ℕ) (t : ℕ) : mc T t < 4 := fld_lt _ _ _

theorem card_Mt {T : ℕ → ℕ} (hT : Hyp T) (t : ℕ) : Nat.card (Mt R hT t) = 27 := by
  rw [Mt, Subgroup.card_map_of_injective (MulAut.conj _).injective]
  exact (Eg_facts R hT (mc_lt T t)).2

@[expose] noncomputable def mk (T : ℕ → ℕ) (t : ℕ) : ℕ := fld (T 259) (Nat.mul 243 t) 243

theorem mk_mem {T : ℕ → ℕ} (hT : Hyp T) {t : ℕ} (ht : t < 10) {i : ℕ}
    (hb : (mk T t).testBit i = true) : i < 243 ∧ el R hT i ∈ Mt R hT t := by
  have h := (misc_parts hT.misc).2.2.1 t ht
  rw [mAt, letB_eq, letB_eq, letB_eq, letB_eq] at h
  obtain ⟨hg, h⟩ := andB_eq_true h
  obtain ⟨hgi, h⟩ := andB_eq_true h
  obtain ⟨hinv, hm⟩ := andB_eq_true h
  have hg' : mg T t < 243 := Nat.blt_eq.mp hg
  have hgi' : fld (T (Nat.add 249 t)) 10 8 < 243 := Nat.blt_eq.mp hgi
  have hinv0 : mulI T (mg T t) (fld (T (Nat.add 249 t)) 10 8) = 0 := Nat.eq_of_beq_eq_true hinv
  have hmk : mk T t = orN 27 fun n => Nat.shiftLeft 1 (mulI T (mulI T (mg T t)
      (eEl T (mc T t) n)) (fld (T (Nat.add 249 t)) 10 8)) := Nat.eq_of_beq_eq_true hm
  rw [hmk] at hb
  obtain ⟨n, -, hn⟩ := testBit_orN _ i 27 hb
  have hv := testBit_shift_one hn
  subst hv
  obtain ⟨he1, he2⟩ := eEl_facts R hT (mc_lt T t) (n := n)
  obtain ⟨m1, r1⟩ := el_mulI R hT hg' he1
  obtain ⟨m2, r2⟩ := el_mulI R hT m1 hgi'
  refine ⟨m2, ?_⟩
  obtain ⟨-, r0⟩ := el_mulI R hT hg' hgi'
  have hinv' : el R hT (fld (T (Nat.add 249 t)) 10 8) = (el R hT (mg T t))⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← r0, hinv0, el_zero R hT]
  rw [r2, r1, hinv', he2]
  have hea : ∀ i, i < 3 → R.ea (mc T t) i ∈ R.Eg (mc T t) := fun i hi => by
    interval_cases i <;> exact Subgroup.subset_closure (by simp)
  refine ⟨R.ea (mc T t) 0 ^ (n / 9) * R.ea (mc T t) 1 ^ (n / 3 % 3) * R.ea (mc T t) 2 ^ (n % 3),
    ?_, by simp [MulAut.conj_apply]⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (hea 0 (by norm_num)) _)
    (Subgroup.pow_mem _ (hea 1 (by norm_num)) _)) (Subgroup.pow_mem _ (hea 2 (by norm_num)) _)

theorem mem_Mt_cube {T : ℕ → ℕ} (hT : Hyp T) {t : ℕ} {x : X} (hx : x ∈ Mt R hT t) : x ^ 3 = 1 := by
  obtain ⟨e, he, rfl⟩ := hx
  have := (Eg_facts R hT (mc_lt T t)).1.2 e he
  change (MulAut.conj (el R hT (mg T t)) e) ^ 3 = 1
  rw [MulAut.conj_apply, conj_pow, this, mul_one, mul_inv_cancel]

theorem psub_idx {T : ℕ → ℕ} (hT : Hyp T) {x : X} (hx : x ∈ Psub R hT) :
    ∃ n < 243, el R hT n = x := hx

theorem sylow_H4 {T : ℕ → ℕ} (hT : Hyp T) :
    ∀ t : Fin 10, ∀ w ∈ Psub R hT, w ^ 3 = 1 → (∀ m ∈ Mt R hT t, Commute w m) →
      w ∈ Mt R hT t := by
  rintro ⟨t, ht⟩ _ ⟨n, hn, rfl⟩ hw hc
  have h4 := (misc_parts hT.misc).2.2.2 t ht
  rw [h4At, letB_eq, letB_eq] at h4
  have h := impB_eq_true ((allN_iff _ _).1 h4 n hn) ((cube_iff R hT hn).2 hw)
  have hsub : Nat.beq (Nat.land (mk T t) (cmF (T n))) (mk T t) = true := by
    rw [Nat.beq_eq]
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.land_eq, Nat.testBit_and]
    cases hb : (mk T t).testBit i
    · rfl
    · obtain ⟨hi, hmem⟩ := mk_mem R hT ht hb
      have := (cm_iff R hT hn hi).2 ⟨mem_Mt_cube R hT hmem, hc _ hmem⟩
      rw [bitB_iff] at this
      rw [this]
      rfl
  have h' := impB_eq_true h hsub
  exact (mk_mem R hT ht ((bitB_iff _ _).1 h')).2

theorem uni_bit {MK x y i : ℕ} (h : (uni MK x y).testBit i = true) :
    ∃ t < 10, bitB (fld MK (Nat.mul 243 t) 243) x = true ∧
      bitB (fld MK (Nat.mul 243 t) 243) y = true ∧
        (fld MK (Nat.mul 243 t) 243).testBit i = true := by
  obtain ⟨t, ht, hb⟩ := testBit_orN _ i 10 h
  refine ⟨t, ht, ?_⟩
  change (CFSG.KC.G28.letN (fld MK (Nat.mul 243 t) 243) fun m =>
    Bool.rec (motive := fun _ => ℕ) 0 m (CFSG.KC.Ord.andB (bitB m x) (bitB m y))).testBit i = true
    at hb
  have e : ∀ (y' : ℕ) (k : ℕ → ℕ), CFSG.KC.G28.letN y' k = k y' := fun y' k => by cases y' <;> rfl
  rw [e] at hb
  cases hxy : CFSG.KC.Ord.andB (bitB (fld MK (Nat.mul 243 t) 243) x)
      (bitB (fld MK (Nat.mul 243 t) 243) y)
  · rw [hxy] at hb
    simp at hb
  · rw [hxy] at hb
    obtain ⟨h1, h2⟩ := andB_eq_true hxy
    exact ⟨h1, h2, hb⟩

theorem sylow_H3 {T : ℕ → ℕ} (hT : Hyp T) :
    ∀ x ∈ Psub R hT, ∀ y ∈ Psub R hT, ∀ z ∈ Psub R hT, x ^ 3 = 1 → y ^ 3 = 1 → z ^ 3 = 1 →
      Commute x y → Commute x z → Commute y z →
      ∃ t : Fin 10, x ∈ Mt R hT t ∧ y ∈ Mt R hT t ∧ z ∈ Mt R hT t := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hx hy hz hxy hxz hyz
  have h := hT.h3 a ha
  rw [h3At] at h
  have h := impB_eq_true h ((cube_iff R hT ha).2 hx)
  rw [letB_eq, letB_eq] at h
  have hab := (cm_iff R hT ha hb).2 ⟨hy, hxy⟩
  have h := impB_eq_true ((allN_iff _ _).1 h b hb) hab
  rw [letB_eq] at h
  have hw : (Nat.land (cmF (T a)) (cmF (T b))).testBit c = true := by
    rw [Nat.land_eq, Nat.testBit_and, Bool.and_eq_true]
    exact ⟨(bitB_iff _ _).1 ((cm_iff R hT ha hc).2 ⟨hz, hxz⟩),
      (bitB_iff _ _).1 ((cm_iff R hT hb hc).2 ⟨hz, hyz⟩)⟩
  obtain ⟨t, ht, h1, h2, h3⟩ := uni_bit (bits_of_land h hw)
  refine ⟨⟨t, ht⟩, ?_, ?_, ?_⟩
  · exact (mk_mem R hT ht ((bitB_iff _ _).1 h1)).2
  · exact (mk_mem R hT ht ((bitB_iff _ _).1 h2)).2
  · exact (mk_mem R hT ht h3).2

theorem sound17200 {T : ℕ → ℕ} (hT : Hyp T) :
    (∀ c < 4, IsElemAbelian 3 (R.Eg c) ∧ Nat.card (R.Eg c) = 27) ∧
      ∃ P : Subgroup X, Nat.card P = 3 ^ 5 ∧ ∀ B : Subgroup X, B ≤ P → IsElemAbelian 3 B →
        ∃ c < 4, ∃ g : X, B.map (MulAut.conj g).toMonoidHom ≤ R.Eg c := by
  refine ⟨fun c hc => Eg_facts R hT hc, Psub R hT, card_Psub R hT, fun B hBP hB => ?_⟩
  obtain ⟨t, ht⟩ := elem_abelian_le_cover (Psub R hT) (fun t : Fin 10 => Mt R hT t)
    (fun t => card_Mt R hT t) (sylow_H3 R hT) (sylow_H4 R hT) B hBP hB
  refine ⟨mc T t, mc_lt T t, (el R hT (mg T t))⁻¹, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨e, he, hbe⟩ := ht hb
  have hb' : b = (MulAut.conj (el R hT (mg T t))).toMonoidHom e := hbe.symm
  have : (MulAut.conj (el R hT (mg T t))⁻¹).toMonoidHom b = e := by
    rw [hb']
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact he

end CFSG.KC.CertF8.S17200

end
