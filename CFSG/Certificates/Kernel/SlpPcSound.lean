module

public import Certificates.Data.Kernel.SlpPcCl
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
public import CFSG.Certificates.Kernel.J4Hub.BlockSound
public import CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.LocalQTSecLemmas
import all CFSG.Certificates.Kernel.LocalQTSecLemmas
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.SlpPc

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.SlpPc Matrix
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

abbrev M133 := Matrix (Fin 133) (Fin 133) (ZMod 5)

abbrev M9 := Matrix (Fin 9) (Fin 9) (ZMod 5)

@[expose] noncomputable def vOf (n v : Nat) : Fin n → ZMod 5 := fun j => ((lane 13 v j.val : Nat) : ZMod 5)

@[expose] def ex (f : List ℕ) : Fin 6 → ℕ := fun t => f.getD t.val 0

@[expose] def nfP {M : Type} [Monoid M] (hs : Fin 6 → M) (a : Fin 6 → ℕ) : M :=
  hs 0 ^ a 0 * hs 1 ^ a 1 * hs 2 ^ a 2 * hs 3 ^ a 3 * hs 4 ^ a 4 * hs 5 ^ a 5

@[expose] def psi (u : Fin 133 → ZMod 5) : Fin 9 → ZMod 5 := fun l => u (Fin.castLE (by norm_num) l)

structure JFacts (MA MB : M133) (wr : List ℕ) (fus : List (List ℕ)) (ce : List (List (List ℕ)))
    (R : ℕ → M133) (hs : Fin 6 → M133) (BW : Matrix (Fin 9) (Fin 133) (ZMod 5))
    (HM : Fin 6 → M9) : Prop where
  reg : ∀ r, R r ∈ Submonoid.closure ({MA, MB} : Set M133)
  gen : ∀ i, hs i ∈ Submonoid.closure ({MA, MB} : Set M133)
  pow : ∀ i : Fin 6, ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧ hs i ^ 5 = nfP hs e
  conj : ∀ i j : Fin 6, i < j → ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧
    hs j * hs i = hs i * nfP hs e
  pow0 : hs 0 ^ 5 = 1
  pow1 : hs 1 ^ 5 = 1
  inter : ∀ i, BW * hs i = HM i * BW
  ident : ∀ k l : Fin 9, BW k (Fin.castLE (by norm_num) l) = if k = l then 1 else 0
  fus : ∀ f ∈ fus, f.getD 7 0 < 5 ∧
    nfP hs (ex f) * R (f.getD 6 0) = R (f.getD 6 0) * R (wr.getD (f.getD 7 0) 0)
  ent : ∀ k < 5, ∀ e ∈ ce.getD k [],
    R (wr.getD k 0) * R (e.getD 6 0) = R (e.getD 6 0) * nfP hs (ex e) ∧
      ∀ z ∈ e.drop 7, R z * nfP hs (ex e) = nfP hs (ex e) * R z
  seeds : ∀ k < 5,
    MA ∈ Submonoid.closure (Set.range hs ∪ {X | ∃ z ∈ (ce.getD k []).flatMap (·.drop 7), X = R z}) ∧
    MB ∈ Submonoid.closure (Set.range hs ∪ {X | ∃ z ∈ (ce.getD k []).flatMap (·.drop 7), X = R z})

structure WFacts (HM : Fin 6 → M9) (v0 : Fin 9 → ZMod 5) (D : (Fin 9 → ZMod 5) → ℕ)
    (fus oth : List (List ℕ)) : Prop where
  inj : ∀ a b : Fin 6 → ℕ, (∀ t, a t < 5) → (∀ t, b t < 5) →
    v0 ᵥ* nfP HM a = v0 ᵥ* nfP HM b → a = b
  othK : ∀ o ∈ oth, v0 ᵥ* nfP HM (ex o) ^ 5 ≠ v0
  tree : ∀ a : Fin 6 → ℕ, (∀ t, a t < 5) →
    (D (v0 ᵥ* nfP HM a) = 0 → a = 0 ∨ ∃ c ∈ fus ++ oth, a = ex c) ∧
    (D (v0 ᵥ* nfP HM a) ≠ 0 → ∃ j : Fin 6, j.val < 2 ∧
      D (v0 ᵥ* (HM j ^ 4 * nfP HM a * HM j)) + 1 = D (v0 ᵥ* nfP HM a))

section ChkW

open CFSG.KC.LQT.SecS (VCanon vecR_sound vec_inj)

theorem slw_sB (y : ℕ) (k : ℕ → Bool) : sB y k = k y := by cases y <;> rfl

theorem slw_strictN (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by cases y <;> rfl

theorem slw_and {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem slw_or {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem slw_not {a : Bool} : notB a = true ↔ a = false := by cases a <;> decide

theorem slw_nthD {α : Type} (d : α) : ∀ (l : List α) (i : ℕ), nthD d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    rw [List.getD_cons_succ, ← slw_nthD d l i]
    rfl

theorem slw_tl (c : List ℕ) (j : ℕ) : (tl c).getD j 0 = c.getD (j + 1) 0 := by
  cases c with
  | nil => rfl
  | cons a c => rw [List.getD_cons_succ]; rfl

theorem slw_ltUpTo {a : List ℕ} {b : ℕ} : ∀ n, ltUpTo a b n = true → ∀ t < n, a.getD t 0 < b
  | 0, _, t, ht => absurd ht (by omega)
  | n + 1, h, t, ht => by
    have e : ltUpTo a b (n + 1) = andB (Nat.blt (nthD 0 a n) b) (ltUpTo a b n) := rfl
    rw [e, slw_and, slw_nthD, Nat.blt_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact slw_ltUpTo n h.2 t ht
    · exact h.1

theorem slw_bitsN (x o m : ℕ) : bitsN x o m = x / 2 ^ o % 2 ^ m := by
  have e : bitsN x o m = (x >>> o) &&& (1 <<< m - 1) := rfl
  rw [e, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem slw_bit_lt (x m : ℕ) : bitsN x m 1 < 2 := by
  rw [slw_bitsN, pow_one]
  exact Nat.mod_lt _ (by norm_num)

theorem slw_bit1 {x m : ℕ} : bitsN x m 1 = 1 ↔ x.testBit m = true := by
  rw [slw_bitsN, pow_one, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

theorem slw_bit_lor {x m k : ℕ} :
    bitsN (Nat.lor x (Nat.shiftLeft 1 k)) m 1 = 1 ↔ bitsN x m 1 = 1 ∨ k = m := by
  have e : Nat.lor x (Nat.shiftLeft 1 k) = x ||| 2 ^ k :=
    congrArg (Nat.lor x) (Nat.one_shiftLeft k)
  rw [slw_bit1, slw_bit1, e, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_iff]

theorem slw_maskOf : ∀ (l : List (List ℕ)) (acc m : ℕ), bitsN (maskOf l acc) m 1 = 1 →
    bitsN acc m 1 = 1 ∨ ∃ c ∈ l, code c = m
  | [], _, _, h => Or.inl h
  | c :: l, acc, m, h => by
    have e : maskOf (c :: l) acc = maskOf l (Nat.lor acc (Nat.shiftLeft 1 (code c))) := by
      change CFSG.KC.Loop.strictN (Nat.lor acc (Nat.shiftLeft 1 (code c))) (maskOf l) = _
      rw [slw_strictN]
    rw [e] at h
    rcases slw_maskOf l _ m h with h1 | ⟨c', hc', e'⟩
    · rcases slw_bit_lor.1 h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨c, List.mem_cons_self, h2⟩
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', e'⟩

theorem slw_code (a : List ℕ) : code a = a.getD 0 0 * 3125 + a.getD 1 0 * 625 +
    a.getD 2 0 * 125 + a.getD 3 0 * 25 + a.getD 4 0 * 5 + a.getD 5 0 := by
  have e : code a = Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul
      (Nat.add (Nat.mul (Nat.add (Nat.mul 0 5) (nthD 0 a 0)) 5) (nthD 0 a 1)) 5) (nthD 0 a 2)) 5)
      (nthD 0 a 3)) 5) (nthD 0 a 4)) 5) (nthD 0 a 5) := rfl
  rw [e]
  simp only [slw_nthD, Nat.add_eq, Nat.mul_eq]
  ring

def cd5 (a : Fin 6 → ℕ) : ℕ := a 0 * 3125 + a 1 * 625 + a 2 * 125 + a 3 * 25 + a 4 * 5 + a 5

theorem slw_code_ex (c : List ℕ) : code c = cd5 (ex c) := by
  rw [slw_code]
  rfl

theorem slw_cd5_inj {a b : Fin 6 → ℕ} (ha : ∀ t, a t < 5) (hb : ∀ t, b t < 5)
    (h : cd5 a = cd5 b) : a = b := by
  have a0 := ha 0
  have a1 := ha 1
  have a2 := ha 2
  have a3 := ha 3
  have a4 := ha 4
  have a5 := ha 5
  have b0 := hb 0
  have b1 := hb 1
  have b2 := hb 2
  have b3 := hb 3
  have b4 := hb 4
  have b5 := hb 5
  unfold cd5 at h
  have e0 : a 0 = b 0 := by omega
  have e1 : a 1 = b 1 := by omega
  have e2 : a 2 = b 2 := by omega
  have e3 : a 3 = b 3 := by omega
  have e4 : a 4 = b 4 := by omega
  have e5 : a 5 = b 5 := by omega
  funext t
  obtain ⟨t, ht⟩ := t
  interval_cases t
  all_goals first | exact e0 | exact e1 | exact e2 | exact e3 | exact e4 | exact e5

theorem slw_cd5_zero {a : Fin 6 → ℕ} (h : cd5 a = 0) : a = 0 := by
  unfold cd5 at h
  have e0 : a 0 = 0 := by omega
  have e1 : a 1 = 0 := by omega
  have e2 : a 2 = 0 := by omega
  have e3 : a 3 = 0 := by omega
  have e4 : a 4 = 0 := by omega
  have e5 : a 5 = 0 := by omega
  funext t
  obtain ⟨t, ht⟩ := t
  interval_cases t
  all_goals first | exact e0 | exact e1 | exact e2 | exact e3 | exact e4 | exact e5

theorem slw_ex_of_code {a : Fin 6 → ℕ} {c : List ℕ} (ha : ∀ t, a t < 5)
    (hc : ∀ t < 6, c.getD t 0 < 5) (h : code c = cd5 a) : a = ex c := by
  rw [slw_code_ex] at h
  exact slw_cd5_inj ha (fun t => hc t.val t.isLt) h.symm

open Classical in
noncomputable def kV (keyc : List ℕ) (v : Fin 9 → ZMod 5) : ℕ :=
  if h : ∃ x, VCanon 5 9 13 x ∧ vOf 9 x = v then key keyc h.choose else 0

theorem slw_kV {keyc : List ℕ} {x : ℕ} (hx : VCanon 5 9 13 x) :
    kV keyc (vOf 9 x) = key keyc x := by
  have h : ∃ y, VCanon 5 9 13 y ∧ vOf 9 y = vOf 9 x := ⟨x, hx, rfl⟩
  unfold kV
  rw [dif_pos h, vec_inj (by norm_num) h.choose_spec.1 hx h.choose_spec.2]

abbrev VecOK (vec : ℕ → ℕ → ℕ) : Prop :=
  ∀ v M, VCanon 5 9 13 v → Canon 5 9 13 M →
    VCanon 5 9 13 (vec v M) ∧ vOf 9 (vec v M) = vOf 9 v ᵥ* ordMat 5 9 13 117 M

noncomputable def itV (vec : ℕ → ℕ → ℕ) (M u e : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) u (fun _ acc => CFSG.KC.Loop.strictN (vec acc M) id) e

theorem slw_itV {vec : ℕ → ℕ → ℕ} (hvec : VecOK vec) {M u : ℕ} (hM : Canon 5 9 13 M)
    (hu : VCanon 5 9 13 u) : ∀ e, VCanon 5 9 13 (itV vec M u e) ∧
      vOf 9 (itV vec M u e) = vOf 9 u ᵥ* ordMat 5 9 13 117 M ^ e
  | 0 => ⟨hu, by rw [pow_zero, Matrix.vecMul_one]; rfl⟩
  | e + 1 => by
    have eq : itV vec M u (e + 1) = vec (itV vec M u e) M := by
      change CFSG.KC.Loop.strictN (vec (itV vec M u e) M) id = _
      rw [slw_strictN]
      rfl
    obtain ⟨h1, h2⟩ := slw_itV hvec hM hu e
    obtain ⟨h3, h4⟩ := hvec _ _ h1 hM
    rw [eq]
    exact ⟨h3, by rw [h4, h2, Matrix.vecMul_vecMul, pow_succ]⟩

noncomputable def prodW (Ms : List ℕ) : List ℕ → M9 :=
  List.rec (motive := fun _ => List ℕ → M9) (fun _ => 1)
    (fun M _ ih a => ordMat 5 9 13 117 M ^ a.getD 0 0 * ih (tl a)) Ms

theorem slw_actW {vec : ℕ → ℕ → ℕ} (hvec : VecOK vec) : ∀ (Ms a : List ℕ) (u : ℕ),
    (∀ M ∈ Ms, Canon 5 9 13 M) → VCanon 5 9 13 u →
      VCanon 5 9 13 (actW vec Ms a u) ∧ vOf 9 (actW vec Ms a u) = vOf 9 u ᵥ* prodW Ms a
  | [], _, _, _, hu => ⟨hu, (Matrix.vecMul_one _).symm⟩
  | M :: Ms, a, u, hc, hu => by
    have e : actW vec (M :: Ms) a u = actW vec Ms (tl a) (itV vec M u (nthD 0 a 0)) := rfl
    have ep : prodW (M :: Ms) a = ordMat 5 9 13 117 M ^ a.getD 0 0 * prodW Ms (tl a) := rfl
    obtain ⟨h1, h2⟩ := slw_itV hvec (hc M List.mem_cons_self) hu (nthD 0 a 0)
    obtain ⟨h3, h4⟩ := slw_actW hvec Ms (tl a) _
      (fun M' hM' => hc M' (List.mem_cons_of_mem _ hM')) h1
    rw [e, ep]
    refine ⟨h3, ?_⟩
    rw [h4, h2, Matrix.vecMul_vecMul, slw_nthD]

noncomputable def itA (vec : ℕ → ℕ → ℕ) (Ms a : List ℕ) (u n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) u (fun _ u => CFSG.KC.Loop.strictN (actW vec Ms a u) id) n

theorem slw_itA {vec : ℕ → ℕ → ℕ} (hvec : VecOK vec) {Ms a : List ℕ} {u : ℕ}
    (hMs : ∀ M ∈ Ms, Canon 5 9 13 M) (hu : VCanon 5 9 13 u) : ∀ n,
      VCanon 5 9 13 (itA vec Ms a u n) ∧ vOf 9 (itA vec Ms a u n) = vOf 9 u ᵥ* prodW Ms a ^ n
  | 0 => ⟨hu, by rw [pow_zero, Matrix.vecMul_one]; rfl⟩
  | n + 1 => by
    have eq : itA vec Ms a u (n + 1) = actW vec Ms a (itA vec Ms a u n) := by
      change CFSG.KC.Loop.strictN (actW vec Ms a (itA vec Ms a u n)) id = _
      rw [slw_strictN]
      rfl
    obtain ⟨h1, h2⟩ := slw_itA hvec hMs hu n
    obtain ⟨h3, h4⟩ := slw_actW hvec Ms a _ hMs h1
    rw [eq]
    exact ⟨h3, by rw [h4, h2, Matrix.vecMul_vecMul, pow_succ]⟩

theorem slw_othOK {vec : ℕ → ℕ → ℕ} (hvec : VecOK vec) {Ms : List ℕ} {c0 : ℕ}
    (hc0 : VCanon 5 9 13 c0) (hMs : ∀ M ∈ Ms, Canon 5 9 13 M) :
    ∀ oth : List (List ℕ), othOK vec Ms c0 oth = true → ∀ o ∈ oth,
      (∀ t < 6, o.getD t 0 < 5) ∧ vOf 9 c0 ᵥ* prodW Ms o ^ 5 ≠ vOf 9 c0
  | [], _, _, ho => absurd ho List.not_mem_nil
  | o :: oth, h, o', ho' => by
    have e : othOK vec Ms c0 (o :: oth) = andB (andB (ltUpTo o 5 6)
        (notB (Nat.beq (itA vec Ms o c0 5) c0))) (othOK vec Ms c0 oth) := rfl
    rw [e, slw_and, slw_and, slw_not] at h
    rcases List.mem_cons.1 ho' with heq | ho'
    · rw [heq]
      refine ⟨slw_ltUpTo 6 h.1.1, fun hv => ?_⟩
      obtain ⟨h1, h2⟩ := slw_itA hvec hMs hc0 (a := o) 5
      have h3 : itA vec Ms o c0 5 = c0 := vec_inj (by norm_num) h1 hc0 (h2.trans hv)
      have h4 := h.1.2
      rw [h3, Nat.beq_refl] at h4
      exact Bool.noConfusion h4
    · exact slw_othOK hvec hc0 hMs oth h.2 o' ho'

theorem slw_fus : ∀ fus : List (List ℕ), List.rec (motive := fun _ => Bool) true
    (fun f _ ih => andB (ltUpTo f 5 6) ih) fus = true → ∀ f ∈ fus, ∀ t < 6, f.getD t 0 < 5
  | [], _, _, hf => absurd hf List.not_mem_nil
  | f :: fus, h, f', hf' => by
    have e : List.rec (motive := fun _ => Bool) true (fun f _ ih => andB (ltUpTo f 5 6) ih)
        (f :: fus) = andB (ltUpTo f 5 6) (List.rec (motive := fun _ => Bool) true
          (fun f _ ih => andB (ltUpTo f 5 6) ih) fus) := rfl
    rw [e, slw_and] at h
    rcases List.mem_cons.1 hf' with heq | hf'
    · rw [heq]
      exact slw_ltUpTo 6 h.1
    · exact slw_fus fus h.2 f' hf'

theorem slw_valid {L9 H9 CM9 RM9 ONE9 LV9 HV9 : ℕ}
    (hc : constsOK 5 13 117 9 9 L9 H9 CM9 RM9 ONE9 LV9 HV9 = true) : ∀ l : List ℕ,
    List.rec (motive := fun _ => Bool) true
      (fun M _ ih => andB (validM 5 (Nat.mul 81 13) L9 H9 M) ih) l = true →
      ∀ M ∈ l, Canon 5 9 13 M
  | [], _, _, hM => absurd hM List.not_mem_nil
  | M :: l, h, M', hM' => by
    have e : List.rec (motive := fun _ => Bool) true
        (fun M _ ih => andB (validM 5 (Nat.mul 81 13) L9 H9 M) ih) (M :: l) =
        andB (validM 5 (Nat.mul 81 13) L9 H9 M) (List.rec (motive := fun _ => Bool) true
          (fun M _ ih => andB (validM 5 (Nat.mul 81 13) L9 H9 M) ih) l) := rfl
    rw [e, slw_and] at h
    rcases List.mem_cons.1 hM' with heq | hM'
    · rw [heq]
      exact validM_canon hc h.1
    · exact slw_valid hc l h.2 M' hM'

abbrev wRel (b0 b1 b2 : Fin 9 → ZMod 5) (s0 s1 s2 : ℕ) (N : M9) : Prop :=
  VCanon 5 9 13 s0 ∧ VCanon 5 9 13 s1 ∧ VCanon 5 9 13 s2 ∧ vOf 9 s0 = b0 ᵥ* N ∧
    vOf 9 s1 = b1 ᵥ* N ∧ vOf 9 s2 = b2 ᵥ* N

def wSpec (b0 b1 b2 : Fin 9 → ZMod 5) (Ok : M9 → ℕ → Prop) (Inv : ℕ → ℕ → Prop)
    (Lf : M9 → ℕ → Prop) (F : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → Bool) → Bool)
    (T : M9 → ℕ → Prop) (c : ℕ) : Prop :=
  ∀ s0 s1 s2 m mask k N, wRel b0 b1 b2 s0 s1 s2 N → (∀ X i, T X i → Ok (N * X) (m + i)) →
    Inv m mask → F s0 s1 s2 m mask k = true →
    (∀ X i, T X i → Lf (N * X) (m + i)) ∧ ∃ mask', Inv (m + c) mask' ∧ k (m + c) mask' = true

theorem slw_rel_step {vec : ℕ → ℕ → ℕ} (hvec : VecOK vec) {b0 b1 b2 : Fin 9 → ZMod 5}
    {s0 s1 s2 M : ℕ} {N : M9} (hM : Canon 5 9 13 M) (h : wRel b0 b1 b2 s0 s1 s2 N) :
    wRel b0 b1 b2 (vec s0 M) (vec s1 M) (vec s2 M) (N * ordMat 5 9 13 117 M) := by
  obtain ⟨c0, c1, c2, e0, e1, e2⟩ := h
  obtain ⟨d0, f0⟩ := hvec _ _ c0 hM
  obtain ⟨d1, f1⟩ := hvec _ _ c1 hM
  obtain ⟨d2, f2⟩ := hvec _ _ c2 hM
  refine ⟨d0, d1, d2, ?_, ?_, ?_⟩
  · rw [f0, e0, Matrix.vecMul_vecMul]
  · rw [f1, e1, Matrix.vecMul_vecMul]
  · rw [f2, e2, Matrix.vecMul_vecMul]

noncomputable def lp5 (vec : ℕ → ℕ → ℕ) (M : ℕ)
    (ih : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → Bool) → Bool) (n : ℕ) :
    ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → Bool) → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → Bool) → Bool)
    (fun _ _ _ m mask k => k m mask)
    (fun n jh s0 s1 s2 m mask k => ih s0 s1 s2 m mask fun m' mask' =>
      Bool.rec (motive := fun _ => Bool)
        (sB (vec s0 M) fun t0 => sB (vec s1 M) fun t1 => sB (vec s2 M) fun t2 =>
          jh t0 t1 t2 m' mask' k)
        (k m' mask') (Nat.beq n 0)) n

theorem slw_lp5 {vec : ℕ → ℕ → ℕ} (hvec : VecOK vec) {b0 b1 b2 : Fin 9 → ZMod 5}
    {Ok : M9 → ℕ → Prop} {Inv : ℕ → ℕ → Prop} {Lf : M9 → ℕ → Prop} {M : ℕ}
    (hM : Canon 5 9 13 M) {ih : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → Bool) → Bool}
    {T : M9 → ℕ → Prop} {c : ℕ} (hih : wSpec b0 b1 b2 Ok Inv Lf ih T c) :
    ∀ n s0 s1 s2 m mask k N, wRel b0 b1 b2 s0 s1 s2 N →
      (∀ a < n, ∀ X i, T X i → Ok (N * (ordMat 5 9 13 117 M ^ a * X)) (m + (a * c + i))) →
      Inv m mask → lp5 vec M ih n s0 s1 s2 m mask k = true →
      (∀ a < n, ∀ X i, T X i → Lf (N * (ordMat 5 9 13 117 M ^ a * X)) (m + (a * c + i))) ∧
        ∃ mask', Inv (m + n * c) mask' ∧ k (m + n * c) mask' = true := by
  intro n
  induction n with
  | zero =>
    intro s0 s1 s2 m mask k N _ _ hI h
    refine ⟨fun a ha => absurd ha (Nat.not_lt_zero _), mask, ?_, ?_⟩
    · rw [Nat.zero_mul, Nat.add_zero]
      exact hI
    · rw [Nat.zero_mul, Nat.add_zero]
      exact h
  | succ n ihn =>
    intro s0 s1 s2 m mask k N hR hOk hI h
    have e : lp5 vec M ih (n + 1) s0 s1 s2 m mask k = ih s0 s1 s2 m mask fun m' mask' =>
        Bool.rec (motive := fun _ => Bool)
          (sB (vec s0 M) fun t0 => sB (vec s1 M) fun t1 => sB (vec s2 M) fun t2 =>
            lp5 vec M ih n t0 t1 t2 m' mask' k)
          (k m' mask') (Nat.beq n 0) := rfl
    rw [e] at h
    have hOk0 : ∀ X i, T X i → Ok (N * X) (m + i) := fun X i hT => by
      have h' := hOk 0 (Nat.succ_pos n) X i hT
      rwa [pow_zero, one_mul, Nat.zero_mul, Nat.zero_add] at h'
    obtain ⟨hL0, mask1, hI1, hk1⟩ := hih s0 s1 s2 m mask _ N hR hOk0 hI h
    have hL0' : ∀ X i, T X i →
        Lf (N * (ordMat 5 9 13 117 M ^ 0 * X)) (m + (0 * c + i)) := by
      intro X i hT
      rw [pow_zero, one_mul, Nat.zero_mul, Nat.zero_add]
      exact hL0 X i hT
    have key : ∀ (a : ℕ) (X : M9), N * (ordMat 5 9 13 117 M ^ (a + 1) * X) =
        N * ordMat 5 9 13 117 M * (ordMat 5 9 13 117 M ^ a * X) := by
      intro a X
      rw [pow_succ']
      simp only [mul_assoc]
    have keyi : ∀ a i : ℕ, m + ((a + 1) * c + i) = m + c + (a * c + i) := by
      intro a i
      ring
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e1 : m + (0 + 1) * c = m + c := by ring
      refine ⟨fun a ha X i hT => ?_, mask1, ?_, ?_⟩
      · have ha0 : a = 0 := by omega
        subst ha0
        exact hL0' X i hT
      · rw [e1]
        exact hI1
      · rw [e1]
        exact hk1
    · have hb : Nat.beq n 0 = false := Bool.eq_false_iff.2 fun e' => by
        have := Nat.eq_of_beq_eq_true e'
        omega
      rw [hb] at hk1
      simp only [slw_sB] at hk1
      obtain ⟨hL, mask2, hI2, hk2⟩ := ihn (vec s0 M) (vec s1 M) (vec s2 M) (m + c) mask1 k
        (N * ordMat 5 9 13 117 M) (slw_rel_step hvec hM hR)
        (fun a ha X i hT => by
          have h' := hOk (a + 1) (by omega) X i hT
          rwa [key, keyi] at h') hI1 hk1
      have ef : m + c + n * c = m + (n + 1) * c := by ring
      refine ⟨fun a ha X i hT => ?_, mask2, ?_, ?_⟩
      · rcases a with _ | a
        · exact hL0' X i hT
        · rw [key, keyi]
          exact hL a (by omega) X i hT
      · rw [← ef]
        exact hI2
      · rw [← ef]
        exact hk2

noncomputable abbrev nT (Ns : List ℕ) : M9 → ℕ → Prop :=
  List.rec (motive := fun _ => M9 → ℕ → Prop) (fun X i => X = 1 ∧ i = 0)
    (fun M Ns ih X i => ∃ a < 5, ∃ X' i', ih X' i' ∧ X = ordMat 5 9 13 117 M ^ a * X' ∧
      i = a * 5 ^ Ns.length + i') Ns

theorem slw_nest {vec : ℕ → ℕ → ℕ} (hvec : VecOK vec) {Ms keyc : List ℕ} {dep jb msk : ℕ}
    {b0 b1 b2 : Fin 9 → ZMod 5} {Ok : M9 → ℕ → Prop} {Inv : ℕ → ℕ → Prop}
    {Lf : M9 → ℕ → Prop}
    (hleaf : wSpec b0 b1 b2 Ok Inv Lf
      (fun s0 s1 s2 m mask k => leaf vec Ms keyc dep jb msk s0 s1 s2 m mask k)
      (fun X i => X = 1 ∧ i = 0) 1) :
    ∀ Ns : List ℕ, (∀ M ∈ Ns, Canon 5 9 13 M) →
      wSpec b0 b1 b2 Ok Inv Lf (nest vec Ms keyc dep jb msk Ns) (nT Ns) (5 ^ Ns.length)
  | [], _ => by
    rw [List.length_nil, pow_zero]
    exact hleaf
  | M :: Ns, hc => by
    have ih := slw_nest hvec hleaf Ns (fun M' hM' => hc M' (List.mem_cons_of_mem _ hM'))
    intro s0 s1 s2 m mask k N hR hOk hI h
    have e : nest vec Ms keyc dep jb msk (M :: Ns) s0 s1 s2 m mask k =
        lp5 vec M (nest vec Ms keyc dep jb msk Ns) 5 s0 s1 s2 m mask k := rfl
    rw [e] at h
    obtain ⟨hL, mask', hI', hk⟩ := slw_lp5 hvec (hc M List.mem_cons_self) ih 5 s0 s1 s2 m mask k
      N hR (fun a ha X i hT => hOk _ _ ⟨a, ha, X, i, hT, rfl, rfl⟩) hI h
    have ec : 5 ^ (M :: Ns).length = 5 * 5 ^ Ns.length := by
      rw [List.length_cons, pow_succ']
    rw [ec]
    refine ⟨fun X i hT => ?_, mask', hI', hk⟩
    obtain ⟨a, ha, X', i', hT', rfl, rfl⟩ := hT
    exact hL a ha X' i' hT'

abbrev wInv (keyc : List ℕ) (b0 : Fin 9 → ZMod 5) (Ok : M9 → ℕ → Prop) (m mask : ℕ) : Prop :=
  ∀ X i, Ok X i → i < m → bitsN mask (kV keyc (b0 ᵥ* X)) 1 = 1

abbrev wLf (Ms keyc : List ℕ) (dep jb msk : ℕ) (b0 b1 b2 : Fin 9 → ZMod 5)
    (Ok : M9 → ℕ → Prop) (N : M9) (m : ℕ) : Prop :=
  ∃ mask, wInv keyc b0 Ok m mask ∧ bitsN mask (kV keyc (b0 ᵥ* N)) 1 = 0 ∧
    (bitsN dep (Nat.mul 4 (kV keyc (b0 ᵥ* N))) 4 = 0 → m = 0 ∨ bitsN msk m 1 = 1) ∧
    (bitsN dep (Nat.mul 4 (kV keyc (b0 ᵥ* N))) 4 ≠ 0 →
      (bitsN jb m 1 = 0 ∧ Nat.succ (bitsN dep (Nat.mul 4
          (kV keyc (b1 ᵥ* N ᵥ* ordMat 5 9 13 117 (Ms.getD 0 0)))) 4) =
        bitsN dep (Nat.mul 4 (kV keyc (b0 ᵥ* N))) 4) ∨
      (bitsN jb m 1 = 1 ∧ Nat.succ (bitsN dep (Nat.mul 4
          (kV keyc (b2 ᵥ* N ᵥ* ordMat 5 9 13 117 (Ms.getD 1 0)))) 4) =
        bitsN dep (Nat.mul 4 (kV keyc (b0 ᵥ* N))) 4))

theorem slw_leaf {vec : ℕ → ℕ → ℕ} (hvec : VecOK vec) {Ms keyc : List ℕ} {dep jb msk : ℕ}
    (hMs : ∀ j < 2, Canon 5 9 13 (Ms.getD j 0)) {b0 b1 b2 : Fin 9 → ZMod 5}
    {Ok : M9 → ℕ → Prop} (hfun : ∀ X X' i, Ok X i → Ok X' i → X = X') :
    wSpec b0 b1 b2 Ok (wInv keyc b0 Ok) (wLf Ms keyc dep jb msk b0 b1 b2 Ok)
      (fun s0 s1 s2 m mask k => leaf vec Ms keyc dep jb msk s0 s1 s2 m mask k)
      (fun X i => X = 1 ∧ i = 0) 1 := by
  intro s0 s1 s2 m mask k N hR hOk hI h
  obtain ⟨c0, c1, c2, e0, e1, e2⟩ := hR
  have hN : Ok N m := by
    have h' := hOk 1 0 ⟨rfl, rfl⟩
    rwa [mul_one, Nat.add_zero] at h'
  have hk0 : key keyc s0 = kV keyc (b0 ᵥ* N) := by rw [← e0, slw_kV c0]
  have hv1 := hvec s1 (Ms.getD 0 0) c1 (hMs 0 (by norm_num))
  have hv2 := hvec s2 (Ms.getD 1 0) c2 (hMs 1 (by norm_num))
  have hk1 : key keyc (vec s1 (Ms.getD 0 0)) =
      kV keyc (b1 ᵥ* N ᵥ* ordMat 5 9 13 117 (Ms.getD 0 0)) := by
    rw [← e1, ← hv1.2, slw_kV hv1.1]
  have hk2 : key keyc (vec s2 (Ms.getD 1 0)) =
      kV keyc (b2 ᵥ* N ᵥ* ordMat 5 9 13 117 (Ms.getD 1 0)) := by
    rw [← e2, ← hv2.2, slw_kV hv2.1]
  unfold leaf at h
  simp only [slw_sB, slw_and, slw_nthD, hk0] at h
  obtain ⟨hnew, hd, hk⟩ := h
  refine ⟨fun X i hT => ?_, Nat.lor mask (Nat.shiftLeft 1 (kV keyc (b0 ᵥ* N))), ?_, hk⟩
  · obtain ⟨rfl, rfl⟩ := hT
    rw [mul_one, Nat.add_zero]
    refine ⟨mask, hI, Nat.eq_of_beq_eq_true hnew, fun hz => ?_, fun hz => ?_⟩
    · have hb : Nat.beq (bitsN dep (Nat.mul 4 (kV keyc (b0 ᵥ* N))) 4) 0 = true := by
        rw [hz]
        rfl
      rw [hb] at hd
      have hd' : orB (Nat.beq m 0) (Nat.beq (bitsN msk m 1) 1) = true := hd
      rcases slw_or.1 hd' with h1 | h1
      · exact Or.inl (Nat.eq_of_beq_eq_true h1)
      · exact Or.inr (Nat.eq_of_beq_eq_true h1)
    · have hb : Nat.beq (bitsN dep (Nat.mul 4 (kV keyc (b0 ᵥ* N))) 4) 0 = false :=
        Bool.eq_false_iff.2 fun e => hz (Nat.eq_of_beq_eq_true e)
      rw [hb] at hd
      have hj := slw_bit_lt jb m
      rcases (by omega : bitsN jb m 1 = 0 ∨ bitsN jb m 1 = 1) with hj | hj
      · rw [hj] at hd
        have hd' : Nat.beq (Nat.succ (bitsN dep (Nat.mul 4 (key keyc (vec s1 (Ms.getD 0 0)))) 4))
            (bitsN dep (Nat.mul 4 (kV keyc (b0 ᵥ* N))) 4) = true := hd
        rw [hk1] at hd'
        exact Or.inl ⟨hj, Nat.eq_of_beq_eq_true hd'⟩
      · rw [hj] at hd
        have hd' : Nat.beq (Nat.succ (bitsN dep (Nat.mul 4 (key keyc (vec s2 (Ms.getD 1 0)))) 4))
            (bitsN dep (Nat.mul 4 (kV keyc (b0 ᵥ* N))) 4) = true := hd
        rw [hk2] at hd'
        exact Or.inr ⟨hj, Nat.eq_of_beq_eq_true hd'⟩
  · intro X i hX hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact slw_bit_lor.2 (Or.inl (hI X i hX hi))
    · rw [hfun X N _ hX hN]
      exact slw_bit_lor.2 (Or.inr rfl)

abbrev wTall (Ms : List ℕ) (X : M9) (i : ℕ) : Prop :=
  ∃ a : Fin 6 → ℕ, (∀ t, a t < 5) ∧
    X = nfP (fun t => ordMat 5 9 13 117 (Ms.getD t.val 0)) a ∧ i = cd5 a

theorem slw_tall_fun {Ms : List ℕ} {X X' : M9} {i : ℕ} (h : wTall Ms X i)
    (h' : wTall Ms X' i) : X = X' := by
  obtain ⟨a, ha, rfl, rfl⟩ := h
  obtain ⟨a', ha', rfl, e⟩ := h'
  rw [slw_cd5_inj ha ha' e]

theorem slw_nT6 (h0 h1 h2 h3 h4 h5 : ℕ) (a : Fin 6 → ℕ) (ha : ∀ t, a t < 5) :
    nT [h0, h1, h2, h3, h4, h5]
      (nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0)) a) (cd5 a) := by
  refine ⟨a 0, ha 0, _, _, ⟨a 1, ha 1, _, _, ⟨a 2, ha 2, _, _, ⟨a 3, ha 3, _, _,
    ⟨a 4, ha 4, _, _, ⟨a 5, ha 5, _, _, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩,
    rfl, rfl⟩, ?_, ?_⟩
  · simp only [nfP, mul_assoc, mul_one]
    all_goals rfl
  · simp only [cd5, List.length_cons, List.length_nil]
    ring

theorem slw_tall6 {h0 h1 h2 h3 h4 h5 : ℕ} {X : M9} {i : ℕ}
    (hT : nT [h0, h1, h2, h3, h4, h5] X i) : wTall [h0, h1, h2, h3, h4, h5] X i := by
  obtain ⟨a0, ha0, X1, i1, ⟨a1, ha1, X2, i2, ⟨a2, ha2, X3, i3, ⟨a3, ha3, X4, i4,
    ⟨a4, ha4, X5, i5, ⟨a5, ha5, X6, i6, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩,
    rfl, rfl⟩, rfl, rfl⟩ := hT
  refine ⟨fun t => [a0, a1, a2, a3, a4, a5].getD t.val 0, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨t, ht⟩ := t
    interval_cases t
    all_goals first | exact ha0 | exact ha1 | exact ha2 | exact ha3 | exact ha4 | exact ha5
  · simp only [nfP, mul_assoc, mul_one]
    all_goals rfl
  · simp only [cd5, List.length_cons, List.length_nil]
    change _ = a0 * 3125 + a1 * 625 + a2 * 125 + a3 * 25 + a4 * 5 + a5
    ring

theorem slw_prodW6 (h0 h1 h2 h3 h4 h5 : ℕ) (o : List ℕ) : prodW [h0, h1, h2, h3, h4, h5] o =
    nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0)) (ex o) := by
  have e : prodW [h0, h1, h2, h3, h4, h5] o = ordMat 5 9 13 117 h0 ^ o.getD 0 0 *
      (ordMat 5 9 13 117 h1 ^ (tl o).getD 0 0 * (ordMat 5 9 13 117 h2 ^ (tl (tl o)).getD 0 0 *
      (ordMat 5 9 13 117 h3 ^ (tl (tl (tl o))).getD 0 0 *
      (ordMat 5 9 13 117 h4 ^ (tl (tl (tl (tl o)))).getD 0 0 *
      (ordMat 5 9 13 117 h5 ^ (tl (tl (tl (tl (tl o))))).getD 0 0 * 1))))) := rfl
  rw [e]
  simp only [slw_tl, nfP, ex, mul_one, mul_assoc]
  all_goals rfl

end ChkW

section ChkJ

open CFSG.KC.LQT.SecS CFSG.KS.PackFld

theorem slj_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

theorem slj_mapS {α : Type} (f : α → ℕ) : ∀ (l : List α) (k : List ℕ → Bool),
    mapS f l k = k (l.map f)
  | [], _ => rfl
  | a :: l, k => by
    have e : mapS f (a :: l) k = sB (f a) (fun x => mapS f l fun xs => k (x :: xs)) := rfl
    rw [e]
    simp only [slw_sB, slj_mapS f l, List.map_cons]

theorem slj_mapS_P {α : Type} {C : ℕ → Prop} {f : α → ℕ} (hf : ∀ a, C (f a)) (l : List α)
    (k : List ℕ → Bool) (h : mapS f l k = true) :
    ∃ xs : List ℕ, xs.length = l.length ∧ (∀ x ∈ xs, C x) ∧ k xs = true := by
  rw [slj_mapS] at h
  refine ⟨l.map f, List.length_map _, fun x hx => ?_, h⟩
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  exact hf a

theorem slj_revOnto : ∀ (l acc : List ℕ), revOnto l acc = l.reverse ++ acc
  | [], _ => rfl
  | x :: l, acc => by
    have e : revOnto (x :: l) acc = revOnto l (x :: acc) := rfl
    rw [e, slj_revOnto l]
    simp

theorem slj_lenN : ∀ l : List ℕ, lenN l = l.length
  | [] => rfl
  | _ :: l => by
    rw [List.length_cons, ← slj_lenN l]
    rfl

theorem slj_dropN : ∀ (n : ℕ) (l : List ℕ), dropN n l = l.drop n
  | 0, _ => rfl
  | n + 1, l => by
    have e : dropN (n + 1) l = tl (dropN n l) := rfl
    rw [e, slj_dropN n l, List.drop_add_one_eq_tail_drop]
    cases l.drop n <;> rfl

theorem slj_zsOf : ∀ es : List (List ℕ), zsOf es = es.flatMap (·.drop 7)
  | [] => rfl
  | e :: es => by
    have h : zsOf (e :: es) = revOnto (revOnto (dropN 7 e) []) (zsOf es) := rfl
    rw [h, slj_revOnto, slj_revOnto, slj_zsOf es, slj_dropN]
    simp

theorem slj_zeroUpTo {a : List ℕ} : ∀ n, zeroUpTo a n = true → ∀ t < n, a.getD t 0 = 0
  | 0, _, t, ht => absurd ht (by omega)
  | n + 1, h, t, ht => by
    have e : zeroUpTo a (n + 1) = andB (Nat.beq (nthD 0 a n) 0) (zeroUpTo a n) := rfl
    rw [e, slw_and, slw_nthD] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact slj_zeroUpTo n h.2 t ht
    · exact Nat.eq_of_beq_eq_true h.1

theorem slj_getD_P {α : Type} {P : α → Prop} {d : α} (hd : P d) {l : List α}
    (hl : ∀ x ∈ l, P x) (i : ℕ) : P (l.getD i d) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hl _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hd

theorem slj_getD_tail {α : Type} (l : List α) (k : ℕ) (d : α) :
    l.tail.getD k d = l.getD (k + 1) d := by
  cases l <;> simp

def sljAll (P : ℕ → Prop) (bl : List (List ℕ)) (cur : List ℕ) : Prop :=
  (∀ b ∈ bl, ∀ x ∈ b, P x) ∧ ∀ x ∈ cur, P x

theorem slj_lk_P {P : ℕ → Prop} {ONE : ℕ} (h1 : P ONE) {bl : List (List ℕ)} {cur : List ℕ}
    (h : sljAll P bl cur) (n r : ℕ) : P (lk ONE bl cur n r) := by
  unfold lk
  cases Nat.beq (Nat.shiftRight r 6) (Nat.shiftRight n 6)
  · simp only [slw_nthD]
    exact slj_getD_P h1 (slj_getD_P (P := fun b : List ℕ => ∀ x ∈ b, P x)
      (fun x hx => absurd hx List.not_mem_nil) h.1 _) _
  · simp only [slw_nthD]
    exact slj_getD_P h1 h.2 _

theorem slj_runP {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {P : ℕ → Prop} (h1 : P ONE)
    (hm : ∀ a b, P a → P b → P (mul a b)) :
    ∀ (prg : List (ℕ × ℕ)) (bl : List (List ℕ)) (cur : List ℕ) (n : ℕ)
      (k : List (List ℕ) → List ℕ → ℕ → Bool), sljAll P bl cur →
      runP mul ONE prg bl cur n k = true → ∃ bl' cur' n', sljAll P bl' cur' ∧ k bl' cur' n' = true
  | [], bl, cur, n, k, hQ, h => ⟨bl, cur, n, hQ, h⟩
  | q :: prg, bl, cur, n, k, hQ, h => by
    have e : runP mul ONE (q :: prg) bl cur n k =
        sB (mul (lk ONE bl cur n q.1) (lk ONE bl cur n q.2)) (fun x =>
          Bool.rec (motive := fun _ => Bool) (runP mul ONE prg bl (List.cons x cur) (Nat.succ n) k)
            (runP mul ONE prg (List.cons (List.cons x cur) bl) List.nil (Nat.succ n) k)
            (Nat.beq (Nat.land (Nat.succ n) 63) 0)) := rfl
    rw [e, slw_sB] at h
    have hx : P (mul (lk ONE bl cur n q.1) (lk ONE bl cur n q.2)) :=
      hm _ _ (slj_lk_P h1 hQ _ _) (slj_lk_P h1 hQ _ _)
    cases hb : Nat.beq (Nat.land (Nat.succ n) 63) 0
    · rw [hb] at h
      refine slj_runP h1 hm prg _ _ _ k ⟨hQ.1, fun x hx' => ?_⟩ h
      rcases List.mem_cons.1 hx' with rfl | hx'
      · exact hx
      · exact hQ.2 x hx'
    · rw [hb] at h
      refine slj_runP h1 hm prg _ _ _ k
        ⟨fun b hb' x hx' => ?_, fun x hx' => absurd hx' List.not_mem_nil⟩ h
      rcases List.mem_cons.1 hb' with rfl | hb'
      · rcases List.mem_cons.1 hx' with rfl | hx'
        · exact hx
        · exact hQ.2 x hx'
      · exact hQ.1 b hb' x hx'

theorem slj_wordGo {mul : ℕ → ℕ → ℕ} {C : ℕ → Prop} (hm : ∀ a b, C a → C b → C (mul a b))
    {R : ℕ → ℕ} (hR : ∀ l, C (R l)) : ∀ (w : List ℕ) (acc : ℕ), C acc → C (wordGo mul R w acc)
  | [], _, h => h
  | l :: w, acc, h => by
    have e : wordGo mul R (l :: w) acc = CFSG.KC.Loop.strictN (mul acc (R l)) (wordGo mul R w) :=
      rfl
    rw [e, slw_strictN]
    exact slj_wordGo hm hR w _ (hm _ _ h (hR l))

noncomputable def sljPw (mul : ℕ → ℕ → ℕ) (ONE h : ℕ) : List ℕ :=
  [ONE, h, mul h h, mul (mul h h) h, mul (mul (mul h h) h) h, mul (mul (mul (mul h h) h) h) h]

theorem slj_pows (mul : ℕ → ℕ → ℕ) (ONE : ℕ) : ∀ (hs : List ℕ) (k : List (List ℕ) → Bool),
    pows mul ONE hs k = k (hs.map (sljPw mul ONE))
  | [], _ => rfl
  | h :: hs, k => by
    have e : pows mul ONE (h :: hs) k = sB (mul h h) fun h2 => sB (mul h2 h) fun h3 =>
        sB (mul h3 h) fun h4 => sB (mul h4 h) fun h5 =>
          pows mul ONE hs fun ps => k ([ONE, h, h2, h3, h4, h5] :: ps) := rfl
    rw [e]
    simp only [slw_sB, slj_pows mul ONE hs, List.map_cons]
    rfl

theorem slj_pw {M : Type} [Monoid M] {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {OM : ℕ → M} {P : ℕ → Prop}
    (hm : ∀ a b, P a → P b → P (mul a b) ∧ OM (mul a b) = OM a * OM b) (h1 : P ONE ∧ OM ONE = 1)
    {h : ℕ} (hh : P h) : ∀ e ≤ 5, P ((sljPw mul ONE h).getD e 0) ∧
      OM ((sljPw mul ONE h).getD e 0) = OM h ^ e := by
  obtain ⟨c2, m2⟩ := hm _ _ hh hh
  obtain ⟨c3, m3⟩ := hm _ _ c2 hh
  obtain ⟨c4, m4⟩ := hm _ _ c3 hh
  obtain ⟨c5, m5⟩ := hm _ _ c4 hh
  intro e he
  interval_cases e
  · exact ⟨h1.1, by rw [pow_zero]; exact h1.2⟩
  · exact ⟨hh, (pow_one _).symm⟩
  · exact ⟨c2, m2.trans (pow_two _).symm⟩
  · exact ⟨c3, m3.trans (by rw [m2, pow_succ, pow_two])⟩
  · exact ⟨c4, m4.trans (by rw [m3, m2, pow_succ, pow_succ, pow_two])⟩
  · exact ⟨c5, m5.trans (by rw [m4, m3, m2, pow_succ, pow_succ, pow_succ, pow_two])⟩

noncomputable def sljProd {M : Type} [Monoid M] (OM : ℕ → M) : List ℕ → List ℕ → M
  | [], _ => 1
  | h :: hl, a => OM h ^ a.getD 0 0 * sljProd OM hl (tl a)

theorem slj_prod_nfP {M : Type} [Monoid M] (OM : ℕ → M) (hl : List ℕ) (hlen : hl.length = 6)
    (e : List ℕ) : sljProd OM hl e = nfP (fun i => OM (hl.getD i.val 0)) (ex e) := by
  match hl, hlen with
  | [s0, s1, s2, s3, s4, s5], _ =>
    simp only [sljProd, nfP, ex, slw_tl, mul_assoc, mul_one]
    rfl

def sljInv {M : Type} [Monoid M] (OM : ℕ → M) (P : ℕ → Prop) (acc : ℕ) (X : M) : Prop :=
  (acc = 0 ∧ X = 1) ∨ (P acc ∧ OM acc = X)

theorem slj_nfGo {M : Type} [Monoid M] {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {OM : ℕ → M} {P : ℕ → Prop}
    (hm : ∀ a b, P a → P b → P (mul a b) ∧ OM (mul a b) = OM a * OM b) (h1 : P ONE ∧ OM ONE = 1)
    (hz : ∀ x, P x → x ≠ 0) : ∀ (hl : List ℕ) (a : List ℕ) (acc : ℕ) (X : M),
      (∀ h ∈ hl, P h) → (∀ t < hl.length, a.getD t 0 ≤ 5) → sljInv OM P acc X →
      sljInv OM P (nfGo mul (hl.map (sljPw mul ONE)) a acc) (X * sljProd OM hl a)
  | [], _, acc, X, _, _, hI => by
    rw [sljProd, mul_one]
    exact hI
  | h :: hl, a, acc, X, hP, ha, hI => by
    have e : nfGo mul ((h :: hl).map (sljPw mul ONE)) a acc =
        CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) (mul acc (nthD 0 (sljPw mul ONE h) (nthD 0 a 0)))
            (nthD 0 (sljPw mul ONE h) (nthD 0 a 0)) (Nat.beq acc 0))
          acc (Nat.beq (nthD 0 a 0) 0)) (nfGo mul (hl.map (sljPw mul ONE)) (tl a)) := rfl
    rw [e, slw_strictN, slw_nthD, slw_nthD]
    have hpw := slj_pw hm h1 (hP h List.mem_cons_self) (a.getD 0 0) (ha 0 (by simp))
    have ih := slj_nfGo hm h1 hz hl (tl a)
    have hP' : ∀ h ∈ hl, P h := fun h' hh' => hP h' (List.mem_cons_of_mem _ hh')
    have ha' : ∀ t < hl.length, (tl a).getD t 0 ≤ 5 := fun t ht => by
      rw [slw_tl]
      exact ha (t + 1) (by simp; omega)
    have hassoc : X * sljProd OM (h :: hl) a = X * OM h ^ a.getD 0 0 * sljProd OM hl (tl a) := by
      rw [sljProd, mul_assoc]
    rw [hassoc]
    refine ih _ _ hP' ha' ?_
    by_cases he : a.getD 0 0 = 0
    · have hb : Nat.beq (a.getD 0 0) 0 = true := by rw [he]; rfl
      rw [hb, he, pow_zero, mul_one]
      exact hI
    · rw [slj_beq_false he]
      rcases hI with ⟨rfl, rfl⟩ | ⟨hPa, hOa⟩
      · right
        exact ⟨hpw.1, hpw.2.trans (one_mul _).symm⟩
      · rw [slj_beq_false (hz acc hPa)]
        obtain ⟨c, m⟩ := hm _ _ hPa hpw.1
        right
        exact ⟨c, m.trans (by rw [hOa, hpw.2])⟩

theorem slj_nfM {M : Type} [Monoid M] {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {OM : ℕ → M} {P : ℕ → Prop}
    (hm : ∀ a b, P a → P b → P (mul a b) ∧ OM (mul a b) = OM a * OM b) (h1 : P ONE ∧ OM ONE = 1)
    (hz : ∀ x, P x → x ≠ 0) (hl a : List ℕ) (hP : ∀ h ∈ hl, P h)
    (ha : ∀ t < hl.length, a.getD t 0 ≤ 5) :
    P (nfM mul ONE (hl.map (sljPw mul ONE)) a) ∧
      OM (nfM mul ONE (hl.map (sljPw mul ONE)) a) = sljProd OM hl a := by
  have hI := slj_nfGo hm h1 hz hl a 0 1 hP ha (Or.inl ⟨rfl, rfl⟩)
  rw [one_mul] at hI
  have e : nfM mul ONE (hl.map (sljPw mul ONE)) a =
      Bool.rec (motive := fun _ => ℕ) (nfGo mul (hl.map (sljPw mul ONE)) a 0) ONE
        (Nat.beq (nfGo mul (hl.map (sljPw mul ONE)) a 0) 0) := rfl
  rw [e]
  rcases hI with ⟨h0, hX⟩ | ⟨hPr, hOr⟩
  · rw [h0]
    exact ⟨h1.1, h1.2.trans hX.symm⟩
  · rw [slj_beq_false (hz _ hPr)]
    exact ⟨hPr, hOr⟩

theorem slj_relOK {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {hs : List ℕ} {pw : List (List ℕ)} {i j : ℕ}
    {e : List ℕ} (h : CFSG.KC.SlpPc.relOK mul ONE hs pw i j e = true) :
    (∀ t < 6, e.getD t 0 < 5) ∧ (∀ t ≤ i, e.getD t 0 = 0) ∧
      (i = j → (pw.getD i []).getD 5 0 = nfM mul ONE pw e) ∧
      (i ≠ j → mul (hs.getD j 0) (hs.getD i 0) = mul (hs.getD i 0) (nfM mul ONE pw e)) := by
  unfold CFSG.KC.SlpPc.relOK at h
  rw [slw_and, slw_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨slw_ltUpTo 6 h1, fun t ht => slj_zeroUpTo (i + 1) h2 t (by omega), fun hij => ?_,
    fun hij => ?_⟩
  · subst hij
    rw [Nat.beq_refl] at h3
    have := Nat.eq_of_beq_eq_true h3
    rwa [slw_nthD, slw_nthD] at this
  · rw [slj_beq_false hij] at h3
    have := Nat.eq_of_beq_eq_true h3
    rwa [slw_nthD, slw_nthD] at this

theorem slj_relsOK {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {hs : List ℕ} {pw : List (List ℕ)} :
    ∀ (rel : List (List ℕ)) (i j : ℕ), relsOK mul ONE hs pw rel i j = true →
      ∀ i' j', i' ≤ j' → j' < 6 → (i < i' ∨ (i = i' ∧ j ≤ j')) →
        ∃ r ∈ rel, CFSG.KC.SlpPc.relOK mul ONE hs pw i' j' (tl (tl r)) = true
  | [], i, j, h, i', j', h1, h2, h3 => by
    have e : relsOK mul ONE hs pw [] i j = Nat.beq i 6 := rfl
    rw [e] at h
    have := Nat.eq_of_beq_eq_true h
    omega
  | r :: rel, i, j, h, i', j', h1, h2, h3 => by
    have e : relsOK mul ONE hs pw (r :: rel) i j = andB (Nat.beq (nthD 0 r 0) i)
        (andB (Nat.beq (nthD 0 r 1) j) (andB (CFSG.KC.SlpPc.relOK mul ONE hs pw i j (tl (tl r)))
          (Bool.rec (motive := fun _ => Bool) (relsOK mul ONE hs pw rel i (Nat.succ j))
            (relsOK mul ONE hs pw rel (Nat.succ i) (Nat.succ i)) (Nat.beq j 5)))) := rfl
    rw [e, slw_and, slw_and, slw_and] at h
    obtain ⟨-, -, hr, hn⟩ := h
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij
      exact ⟨r, List.mem_cons_self, hr⟩
    by_cases hj5 : j = 5
    · rw [hj5, Nat.beq_refl] at hn
      obtain ⟨r', hr', h'⟩ := slj_relsOK rel _ _ hn i' j' h1 h2 (by omega)
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩
    · rw [slj_beq_false hj5] at hn
      obtain ⟨r', hr', h'⟩ := slj_relsOK rel _ _ hn i' j' h1 h2 (by omega)
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem slj_rels_step {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {hs : List ℕ} {pw : List (List ℕ)}
    {rel : List (List ℕ)} {i j : ℕ} (h : relsOK mul ONE hs pw rel i j = true) (hi : i < 6) :
    CFSG.KC.SlpPc.relOK mul ONE hs pw i j (tl (tl (rel.getD 0 []))) = true ∧
      Bool.rec (motive := fun _ => Bool) (relsOK mul ONE hs pw rel.tail i (Nat.succ j))
        (relsOK mul ONE hs pw rel.tail (Nat.succ i) (Nat.succ i)) (Nat.beq j 5) = true := by
  cases rel with
  | nil =>
    have e : relsOK mul ONE hs pw [] i j = Nat.beq i 6 := rfl
    rw [e] at h
    have := Nat.eq_of_beq_eq_true h
    omega
  | cons r rel =>
    have e : relsOK mul ONE hs pw (r :: rel) i j = andB (Nat.beq (nthD 0 r 0) i)
        (andB (Nat.beq (nthD 0 r 1) j) (andB (CFSG.KC.SlpPc.relOK mul ONE hs pw i j (tl (tl r)))
          (Bool.rec (motive := fun _ => Bool) (relsOK mul ONE hs pw rel i (Nat.succ j))
            (relsOK mul ONE hs pw rel (Nat.succ i) (Nat.succ i)) (Nat.beq j 5)))) := rfl
    rw [e, slw_and, slw_and, slw_and] at h
    rw [List.getD_cons_zero, List.tail_cons]
    exact ⟨h.2.2.1, h.2.2.2⟩

theorem slj_commOK {mul : ℕ → ℕ → ℕ} {R : ℕ → ℕ} {y : ℕ} : ∀ zs : List ℕ,
    commOK mul R y zs = true → ∀ z ∈ zs, mul (R z) y = mul y (R z)
  | [], _, z, hz => absurd hz List.not_mem_nil
  | z :: zs, h, z', hz' => by
    have e : commOK mul R y (z :: zs) =
        andB (Nat.beq (mul (R z) y) (mul y (R z))) (commOK mul R y zs) := rfl
    rw [e, slw_and] at h
    rcases List.mem_cons.1 hz' with rfl | hz'
    · exact Nat.eq_of_beq_eq_true h.1
    · exact slj_commOK zs h.2 z' hz'

theorem slj_entOK {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {R : ℕ → ℕ} {pw : List (List ℕ)} {X : ℕ}
    {e : List ℕ} (h : entOK mul ONE R pw X e = true) :
    (∀ t < 6, e.getD t 0 < 5) ∧ mul X (R (e.getD 6 0)) = mul (R (e.getD 6 0)) (nfM mul ONE pw e) ∧
      commOK mul R (nfM mul ONE pw e) (e.drop 7) = true := by
  unfold entOK at h
  simp only [slw_and, slw_sB, slw_nthD, slj_dropN] at h
  exact ⟨slw_ltUpTo 6 h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2⟩

theorem slj_ents {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {R : ℕ → ℕ} {pw : List (List ℕ)} {X : ℕ} :
    ∀ es : List (List ℕ), List.rec (motive := fun _ => Bool) true
      (fun e _ ih => andB (entOK mul ONE R pw X e) ih) es = true →
      ∀ e ∈ es, entOK mul ONE R pw X e = true
  | [], _, e, he => absurd he List.not_mem_nil
  | e :: es, h, e', he' => by
    have eq : List.rec (motive := fun _ => Bool) true
        (fun e _ ih => andB (entOK mul ONE R pw X e) ih) (e :: es) =
        andB (entOK mul ONE R pw X e) (List.rec (motive := fun _ => Bool) true
          (fun e _ ih => andB (entOK mul ONE R pw X e) ih) es) := rfl
    rw [eq, slw_and] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact slj_ents es h.2 e' he'

theorem slj_fusOK {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {R : ℕ → ℕ} {pw : List (List ℕ)} {wr : List ℕ} :
    ∀ fus : List (List ℕ), fusOK mul ONE R pw wr fus = true → ∀ f ∈ fus,
      (∀ t < 6, f.getD t 0 < 5) ∧ f.getD 7 0 < 5 ∧
        mul (nfM mul ONE pw f) (R (f.getD 6 0)) = mul (R (f.getD 6 0)) (R (wr.getD (f.getD 7 0) 0))
  | [], _, f, hf => absurd hf List.not_mem_nil
  | f :: fus, h, f', hf' => by
    have e : fusOK mul ONE R pw wr (f :: fus) = andB (andB (ltUpTo f 5 6)
        (andB (Nat.blt (nthD 0 f 7) 5) (Nat.beq (mul (nfM mul ONE pw f) (R (nthD 0 f 6)))
          (mul (R (nthD 0 f 6)) (R (nthD 0 wr (nthD 0 f 7)))))))
        (fusOK mul ONE R pw wr fus) := rfl
    rw [e, slw_and, slw_and, slw_and] at h
    rcases List.mem_cons.1 hf' with rfl | hf'
    · simp only [slw_nthD, Nat.blt_eq] at h
      exact ⟨slw_ltUpTo 6 h.1.1, h.1.2.1, Nat.eq_of_beq_eq_true h.1.2.2⟩
    · exact slj_fusOK fus h.2 f' hf'

theorem slj_clsOK {mul : ℕ → ℕ → ℕ} {ONE A B : ℕ} {R : ℕ → ℕ} {pw : List (List ℕ)}
    {hs wr : List ℕ} {lp : List (List (ℕ × ℕ))} {lab : List (List ℕ)} :
    ∀ (ce : List (List (List ℕ))) (k : ℕ), clsOK mul ONE A B R pw hs wr lp lab ce k = true →
      ce.length + k = 5 ∧ ∀ m < ce.length, clK mul ONE A B R pw hs (R (wr.getD (k + m) 0))
        (ce.getD m []) (lp.getD (k + m) []) (lab.getD (k + m) []) = true
  | [], k, h => by
    have e : clsOK mul ONE A B R pw hs wr lp lab [] k = Nat.beq k 5 := rfl
    rw [e] at h
    refine ⟨?_, fun m hm => absurd hm (by simp)⟩
    rw [List.length_nil, Nat.zero_add]
    exact Nat.eq_of_beq_eq_true h
  | es :: ce, k, h => by
    have e : clsOK mul ONE A B R pw hs wr lp lab (es :: ce) k = andB (sB (R (nthD 0 wr k))
        fun X => clK mul ONE A B R pw hs X es (nthD [] lp k) (nthD [] lab k))
        (clsOK mul ONE A B R pw hs wr lp lab ce (Nat.succ k)) := rfl
    rw [e] at h
    simp only [slw_and, slw_sB, slw_nthD] at h
    obtain ⟨h1, h2⟩ := slj_clsOK ce (k + 1) h.2
    refine ⟨by rw [List.length_cons]; omega, fun m hm => ?_⟩
    cases m with
    | zero =>
      simp only [Nat.add_zero, List.getD_cons_zero]
      exact h.1
    | succ m =>
      have h3 := h2 m (by simpa using hm)
      have e2 : k + (m + 1) = k + 1 + m := by omega
      rw [e2, List.getD_cons_succ]
      exact h3

theorem slj_recAll {f : ℕ → Bool} : ∀ m, Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB (f k) ih) m = true → ∀ k < m, f k = true
  | 0, _, k, hk => absurd hk (by omega)
  | m + 1, h, k, hk => by
    have e : Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (f k) ih) (m + 1) =
        andB (f m) (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (f k) ih) m) := rfl
    rw [e, slw_and] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact slj_recAll m h.2 k hk
    · exact h.1

theorem slj_rowK (S k M : ℕ) : rowK S k M = (M >>> (S * k)) &&& (2 ^ S - 1) := by
  unfold rowK rowsOf
  change (M >>> (S * k)) &&& ((1 <<< (S * 1)) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mul_one]

theorem slj_idx {r h i j : ℕ} (hi : i < h) (hj : j < r) : r * i + j < r * h := by
  have := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  omega

theorem slj_bound {d : ℕ} {u v : ℕ → ℕ} (hu : ∀ k < d, u k < 5) (hv : ∀ k < d, v k < 5) :
    ∑ k ∈ Finset.range d, u k * v k ≤ 16 * d := by
  calc _ ≤ ∑ _k ∈ Finset.range d, 16 := Finset.sum_le_sum fun k hk => by
          have h1 := hu k (Finset.mem_range.1 hk)
          have h2 := hv k (Finset.mem_range.1 hk)
          have h3 : u k * v k ≤ 4 * 4 := Nat.mul_le_mul (by omega) (by omega)
          omega
    _ = 16 * d := by simp [Nat.mul_comm]

theorem slj_lane_and {w n X l : ℕ} (hl : l < n) :
    lane w (X &&& (2 ^ (w * n) - 1)) l = lane w X l := by
  unfold lane
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < w
  · have h1 : i + w * l < w * n := by
      have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hl)
      rw [Nat.mul_succ] at this
      omega
    simp [hi, h1]
  · simp [hi]

theorem slj_lane_unit {w d k l : ℕ} (hw : 0 < w) (hk : k < d) (hl : l < d) :
    lane w (2 ^ (w * k)) l = if l = k then 1 else 0 := by
  have h2 : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) hw
    simpa using this
  have e : 2 ^ (w * k) = pk w d (fun j => if j = k then 1 else 0) := by
    unfold pk
    simp [hk]
  rw [e, lane_pk (fun t _ => by split <;> omega) hl]

private theorem slj_validM_pk {w n p nb X : ℕ} (hw : 0 < w) (hnb : nb = w * n)
    (hp : p ≤ 2 ^ (w - 1))
    (h : validM p nb (pk w n (fun _ => 1)) (pk w n (fun _ => 2 ^ (w - 1))) X = true) :
    X < 2 ^ (w * n) ∧ ∀ t < n, lane w X t < p := by
  subst hnb
  unfold validM at h
  rw [slw_and, slw_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e2 := two_pow_pred hw
  have hlt : X < 2 ^ (w * n) := by
    have h1' : X >>> (w * n) = 0 := Nat.eq_of_beq_eq_true h1
    rw [Nat.shiftRight_eq_div_pow] at h1'
    rcases Nat.div_eq_zero_iff.1 h1' with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · exact h
  obtain ⟨a, ha_eq, ha⟩ : ∃ a, X = pk w n a ∧ ∀ t < n, a t < 2 ^ w :=
    ⟨lane w X, pk_lane hw hlt, fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  rw [ha_eq] at h2 h3 ⊢
  have h0 := Nat.two_pow_pos (w - 1)
  have hHb : ∀ t < n, (2 : ℕ) ^ (w - 1) < 2 ^ w := fun _ _ => by omega
  have htop : ∀ t < n, a t < 2 ^ (w - 1) := by
    intro t ht
    have h2' : pk w n a &&& pk w n (fun _ => 2 ^ (w - 1)) = 0 := Nat.eq_of_beq_eq_true h2
    have hF := fld_and (fld_pk ha) (fld_pk hHb)
    rw [h2'] at hF
    have hb := hF t (w - 1) (by omega)
    rw [Nat.zero_testBit] at hb
    simp only [ht, ↓reduceIte] at hb
    have ha2 : a t < 2 * 2 ^ (w - 1) := by have := ha t ht; omega
    rw [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, testBit_top ha2] at hb
    simpa using hb
  have h3' : ((pk w n a ||| pk w n (fun _ => 2 ^ (w - 1))) - p * pk w n (fun _ => 1)) &&&
      pk w n (fun _ => 2 ^ (w - 1)) = 0 := Nat.eq_of_beq_eq_true h3
  rw [top_H hw htop hp] at h3'
  unfold pk at h3'
  refine ⟨pk_lt ha, fun t ht => ?_⟩
  rw [lane_pk ha ht]
  by_contra hn
  have hz := Finset.sum_eq_zero_iff.1 h3' t (Finset.mem_range.2 ht)
  have hn' : p ≤ a t := Nat.le_of_not_lt hn
  simp only [hn', ↓reduceIte] at hz
  exact absurd hz (Nat.mul_ne_zero (Nat.two_pow_pos _).ne' (Nat.two_pow_pos _).ne')

private theorem slj_row {w r m k : ℕ} {b : ℕ → ℕ} (hw : 0 < w) (hb : ∀ t < r * m, b t < 2 ^ w)
    (hk : k < m) :
    (pk w (r * m) b >>> (w * r * k)) &&& (2 ^ (w * r) - 1) = pk w r (fun j => b (r * k + j)) := by
  rw [Nat.mul_assoc]
  refine pk_of_fld hw (fld_congr (fld_and (fld_shr (r * k) (fld_pk hb)) (fld_RM w r)) fun t => ?_)
    fun t ht => hb _ (slj_idx hk ht)
  by_cases ht : t < r
  · have h3 : t + r * k < r * m := by have := slj_idx hk ht; omega
    simp only [ht, h3, ↓reduceIte]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hb _ h3), Nat.add_comm]
  · simp [ht]

private theorem slj_vec_core {w r m d T : ℕ} {v b : ℕ → ℕ} (hw : 0 < w) (h5 : 5 ≤ 2 ^ w)
    (hv : ∀ k < d, v k < 5) (hb : ∀ t < r * m, b t < 5) (hdm : d ≤ m)
    (hT : 5 * 2 ^ T ≤ 2 ^ (w - 1)) (hB : 16 * d < 2 ^ (w - 1)) (hB2 : 16 * d < 5 * 2 ^ (T + 1)) :
    redP w (pk w r (fun _ => 1)) (pk w r (fun _ => 2 ^ (w - 1))) 5 T
      (vecU w (w * r) d (2 ^ (w * r) - 1) (pk w d v) (pk w (r * m) b)) =
    pk w r (fun j => (∑ k ∈ Finset.range d, v k * b (r * k + j)) % 5) := by
  have hv' : ∀ k < d, v k < 2 ^ w := fun k hk => lt_of_lt_of_le (hv k hk) h5
  have hb' : ∀ t < r * m, b t < 2 ^ w := fun t ht => lt_of_lt_of_le (hb t ht) h5
  have hsum : vecU w (w * r) d (2 ^ (w * r) - 1) (pk w d v) (pk w (r * m) b) =
      pk w r (fun j => ∑ k ∈ Finset.range d, v k * b (r * k + j)) := by
    rw [vecU_eq]
    calc _ = ∑ k ∈ Finset.range d, v k * pk w r (fun j => b (r * k + j)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := Finset.mem_range.1 hk
          rw [bitsN_lane, slj_row hw hb' (by omega : k < m), lane_pk hv' hk']
      _ = _ := by
          unfold pk
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  rw [hsum]
  have hbd : ∀ j < r, ∑ k ∈ Finset.range d, v k * b (r * k + j) ≤ 16 * d :=
    fun j hj => slj_bound (fun k hk => hv k hk) (fun k hk => hb _ (slj_idx (by omega) hj))
  exact redP_pk hw hT (fun t ht => by have := hbd t ht; omega)
    (fun t ht => by have := hbd t ht; omega)

private theorem slj_invRow {L H CM RM ONE LV HV : ℕ}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) {b : ℕ → ℕ}
    (hb : ∀ t < 133 * 9, b t < 5) {h h' k : ℕ} (hh : Canon 5 133 13 h) (hh' : Canon 5 9 13 h')
    (hk : k < 9)
    (e : vecR 5 13 1729 133 9 LV HV RM (rowK 1729 k (pk 13 (133 * 9) b)) h =
      redP 13 LV HV 5 9 (vecU 13 1729 9 RM (rowK 117 k h') (pk 13 (133 * 9) b))) :
    vOf 133 (rowK 1729 k (pk 13 (133 * 9) b)) ᵥ* ordMat 5 133 13 1729 h = fun j =>
      ∑ l : Fin 9, ordMat 5 9 13 117 h' ⟨k, hk⟩ l * vOf 133 (rowK 1729 l.val (pk 13 (133 * 9) b)) j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRM, -⟩ := consts_facts hc
  obtain ⟨hLV, hHV⟩ := consts_v hc (by norm_num)
  have hb' : ∀ t < 133 * 9, b t < 2 ^ 13 := fun t ht => lt_of_lt_of_le (hb t ht) (by norm_num)
  have hrow : ∀ l < 9, rowK 1729 l (pk 13 (133 * 9) b) = pk 13 133 (fun j => b (133 * l + j)) := by
    intro l hl
    have e1 : (1729 : ℕ) = 13 * 133 := by norm_num
    rw [slj_rowK, e1]
    exact slj_row (by norm_num) hb' hl
  obtain ⟨c, hceq, hcl⟩ : ∃ c, h' = pk 13 (9 * 9) c ∧ ∀ t < 9 * 9, c t < 5 :=
    ⟨lane 13 h', pk_lane (w := 13) (n := 9 * 9) (by norm_num) hh'.1, hh'.2⟩
  rw [hceq] at e ⊢
  have hc' : ∀ t < 9 * 9, c t < 2 ^ 13 := fun t ht => lt_of_lt_of_le (hcl t ht) (by norm_num)
  have hr9 : rowK 117 k (pk 13 (9 * 9) c) = pk 13 9 (fun l => c (9 * k + l)) := by
    have e1 : 117 * k = 9 * 13 * k := by norm_num
    have e2 : (2 : ℕ) ^ 117 = 2 ^ (13 * 9) := by norm_num
    rw [slj_rowK, e1, e2]
    exact row_eq (by norm_num) hc' hk
  have hR : redP 13 LV HV 5 9 (vecU 13 1729 9 RM (rowK 117 k (pk 13 (9 * 9) c))
      (pk 13 (133 * 9) b)) =
      pk 13 133 (fun j => (∑ l ∈ Finset.range 9, c (9 * k + l) * b (133 * l + j)) % 5) := by
    have e1 : (1729 : ℕ) = 13 * 133 := by norm_num
    rw [hr9, hRM, hLV, hHV, e1]
    exact slj_vec_core (w := 13) (r := 133) (m := 9) (T := 9) (by norm_num) (by norm_num)
      (fun l hl => hcl _ (slj_idx hk hl)) hb le_rfl (by norm_num) (by norm_num) (by norm_num)
  have hbk : ∀ j < 133, b (133 * k + j) < 5 := fun j hj => hb _ (slj_idx hk hj)
  have hv := vecR_sound hc (vcanon_pk hbk (by norm_num)) hh
  rw [← hrow k hk] at hv
  have hvt : ∀ v, vOf 133 v = toVec 5 133 13 v := fun v => rfl
  rw [hvt, ← hv.2, e, hR]
  funext j
  have hS : ∀ t < 133, (∑ l ∈ Finset.range 9, c (9 * k + l) * b (133 * l + t)) % 5 < 2 ^ 13 :=
    fun t _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  simp only [toVec]
  rw [lane_pk hS j.isLt, ZMod.natCast_mod, Nat.cast_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e117 : ordMat 5 9 13 117 = ordMat 5 9 13 (9 * 13) := rfl
  rw [Nat.cast_mul, e117, ordMat_pk hc' ⟨k, hk⟩ l, hvt, hrow l.val l.isLt]
  simp only [toVec]
  rw [lane_pk (fun t ht => hb' _ (slj_idx l.isLt ht)) j.isLt]

end ChkJ

theorem chkJCl_sound {L H CM RM ONE LV HV L9 H9 CM9 RM9 ONE9 LV9 HV9 A B : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hc9 : constsOK 5 13 117 9 9 L9 H9 CM9 RM9 ONE9 LV9 HV9 = true)
    (hA : Canon 5 133 13 A) (hB : Canon 5 133 13 B)
    (hAu : IsUnit (ordMat 5 133 13 1729 A)) (hBu : IsUnit (ordMat 5 133 13 1729 B))
    {prg px : List (Nat × Nat)} {wg wr : List Nat} {hw rel fus : List (List Nat)} {bw : Nat}
    {hwm : List Nat} {ce : List (List (List Nat))} {lp : List (List (Nat × Nat))}
    {lab : List (List Nat)}
    (hr0 : rel.getD 0 [] = [0, 0, 0, 0, 0, 0, 0, 0]) (hr6 : rel.getD 6 [] = [1, 1, 0, 0, 0, 0, 0, 0])
    (h : chkJCl (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) A B ONE L LV HV RM
      L9 H9 prg px wg wr hw rel fus bw hwm ce lp lab = true) :
    ∃ R hs BW, JFacts (ordMat 5 133 13 1729 A) (ordMat 5 133 13 1729 B) wr fus ce R hs BW
      (fun i => ordMat 5 9 13 117 (hwm.getD i.val 0)) := by
  set M := mulR 5 13 1729 133 9 L H CM RM with hM
  set OM := ordMat 5 133 13 1729 with hOM
  have hone : Canon 5 133 13 ONE ∧ OM ONE = 1 := one_sound hc
  have hmulC : ∀ a b, Canon 5 133 13 a → Canon 5 133 13 b →
      Canon 5 133 13 (M a b) ∧ OM (M a b) = OM a * OM b := fun a b ha hb => mulR_sound hc ha hb
  let P : ℕ → Prop := fun x => Canon 5 133 13 x ∧
    OM x ∈ Submonoid.closure ({OM A, OM B} : Set M133)
  have hP1 : P ONE := ⟨hone.1, by rw [hone.2]; exact Submonoid.one_mem _⟩
  have hPm : ∀ a b, P a → P b → P (M a b) := fun a b ha hb =>
    ⟨(hmulC a b ha.1 hb.1).1, by rw [(hmulC a b ha.1 hb.1).2]; exact Submonoid.mul_mem _ ha.2 hb.2⟩
  have hPmul : ∀ a b, P a → P b → P (M a b) ∧ OM (M a b) = OM a * OM b :=
    fun a b ha hb => ⟨hPm a b ha hb, (hmulC a b ha.1 hb.1).2⟩
  have hz : ∀ x, P x → x ≠ 0 := by
    intro x hx h0
    have hle : Submonoid.closure ({OM A, OM B} : Set M133) ≤ IsUnit.submonoid M133 := by
      rw [Submonoid.closure_le]
      rintro _ (rfl | rfl)
      · exact hAu
      · exact hBu
    have hu : IsUnit (OM x) := (IsUnit.mem_submonoid_iff _).1 (hle hx.2)
    rw [h0] at hu
    have e0 : OM 0 = 0 := by
      funext i j
      simp [hOM, ordMat]
    rw [e0] at hu
    have h01 : (0 : M133) 0 0 = (1 : M133) 0 0 := by rw [isUnit_zero_iff.1 hu]
    rw [Matrix.zero_apply, Matrix.one_apply_eq] at h01
    exact absurd h01 (by decide)
  unfold chkJCl at h
  obtain ⟨bl0, cur0, n0, hall0, h⟩ := slj_runP hP1 hPm prg [] [B, A, ONE] 3 _
    ⟨fun b hb => absurd hb List.not_mem_nil, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hB, Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
      · exact ⟨hA, Submonoid.subset_closure (Set.mem_insert _ _)⟩
      · exact hP1⟩ h
  obtain ⟨bl, cur, n, hall, hk⟩ := slj_runP hP1 hPm px bl0 cur0 n0 _ hall0 h
  have hPl : ∀ r, P (lk ONE bl cur n r) := fun r => slj_lk_P hP1 hall n r
  have hwP : ∀ w, P (wordP M ONE (fun l => lk ONE bl cur n (nthD 0 wg l)) w) := fun w =>
    slj_wordGo hPm (R := fun l => lk ONE bl cur n (nthD 0 wg l)) (fun l => hPl _) w ONE hP1
  obtain ⟨hsL, -, hsP, hk⟩ := slj_mapS_P (C := P) hwP hw _ hk
  simp only [slj_pows, slw_and] at hk
  obtain ⟨hlen, hrel, hwmok, hbw, hinv, hfus, hcls⟩ := hk
  have hlen6 : hsL.length = 6 := Nat.eq_of_beq_eq_true hlen
  have hsPi : ∀ i : Fin 6, P (hsL.getD i.val 0) := fun i => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen6]; exact i.isLt)]
    exact hsP _ (List.getElem_mem _)
  have hnf : ∀ e : List ℕ, (∀ t < 6, e.getD t 0 < 5) →
      P (nfM M ONE (hsL.map (sljPw M ONE)) e) ∧ OM (nfM M ONE (hsL.map (sljPw M ONE)) e) =
        nfP (fun i : Fin 6 => OM (hsL.getD i.val 0)) (ex e) := by
    intro e he
    have hnfM := @slj_nfM M133 _
    obtain ⟨h1, h2⟩ := hnfM hPmul ⟨hP1, hone.2⟩ hz hsL e hsP
      (fun t ht => by have := he t (by rw [hlen6] at ht; exact ht); omega)
    exact ⟨h1, h2.trans (slj_prod_nfP OM hsL hlen6 e)⟩
  have hpwi : ∀ i : Fin 6, P (((hsL.map (sljPw M ONE)).getD i.val []).getD 5 0) ∧
      OM (((hsL.map (sljPw M ONE)).getD i.val []).getD 5 0) = OM (hsL.getD i.val 0) ^ 5 := by
    intro i
    have hi : i.val < hsL.length := by rw [hlen6]; exact i.isLt
    rw [List.getD_eq_getElem (hsL.map (sljPw M ONE)) [] (by simpa using hi), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hi]
    have hpwM := @slj_pw M133 _
    exact hpwM hPmul ⟨hP1, hone.2⟩ (hsPi i) 5 (by norm_num)
  have r0 := slj_rels_step hrel (by norm_num)
  have t1 : relsOK M ONE hsL (hsL.map (sljPw M ONE)) rel.tail 0 1 = true := r0.2
  have r1 := slj_rels_step t1 (by norm_num)
  have t2 : relsOK M ONE hsL (hsL.map (sljPw M ONE)) rel.tail.tail 0 2 = true := r1.2
  have r2 := slj_rels_step t2 (by norm_num)
  have t3 : relsOK M ONE hsL (hsL.map (sljPw M ONE)) rel.tail.tail.tail 0 3 = true := r2.2
  have r3 := slj_rels_step t3 (by norm_num)
  have t4 : relsOK M ONE hsL (hsL.map (sljPw M ONE)) rel.tail.tail.tail.tail 0 4 = true := r3.2
  have r4 := slj_rels_step t4 (by norm_num)
  have t5 : relsOK M ONE hsL (hsL.map (sljPw M ONE)) rel.tail.tail.tail.tail.tail 0 5 = true :=
    r4.2
  have r5 := slj_rels_step t5 (by norm_num)
  have t6 : relsOK M ONE hsL (hsL.map (sljPw M ONE)) rel.tail.tail.tail.tail.tail.tail 1 1 =
    true := r5.2
  have r6 := slj_rels_step t6 (by norm_num)
  have e6 : rel.tail.tail.tail.tail.tail.tail.getD 0 [] = rel.getD 6 [] := by
    simp only [slj_getD_tail, Nat.reduceAdd, Nat.zero_add]
  have hex : ex (tl (tl [0, 0, 0, 0, 0, 0, 0, 0])) = fun _ => 0 := by
    funext t
    fin_cases t <;> rfl
  have hex1 : ex (tl (tl [1, 1, 0, 0, 0, 0, 0, 0])) = fun _ => 0 := by
    funext t
    fin_cases t <;> rfl
  unfold hwmOK at hwmok
  rw [slw_and] at hwmok
  have hCan := slw_valid hc9 hwm hwmok.2
  have hwlen : hwm.length = 6 := Nat.eq_of_beq_eq_true hwmok.1
  have hwmi : ∀ i < 6, Canon 5 9 13 (hwm.getD i 0) := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hCan _ (List.getElem_mem _)
  unfold bwOK at hbw
  beta_reduce at hbw
  have e : Nat.sub (Nat.shiftLeft 1 (Nat.mul 9 1729)) 1 = 2 ^ (13 * (133 * 9)) - 1 := by
    have e' : Nat.mul 9 1729 = 13 * (133 * 9) := rfl
    have hsub : ∀ s : ℕ, Nat.sub (Nat.shiftLeft 1 s) 1 = 2 ^ s - 1 := fun s => by
      change 1 <<< s - 1 = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [e', hsub]
  have hand : ∀ X Y : ℕ, Nat.land X Y = X &&& Y := fun X Y => rfl
  have hsh : ∀ X : ℕ, Nat.shiftLeft X 12 = X * 2 ^ 12 := fun X => Nat.shiftLeft_eq X 12
  rw [e, hand L, hsh] at hbw
  obtain ⟨-, -, -, -, -, -, hL, -⟩ := consts_facts hc
  have hLb : L &&& (2 ^ (13 * (133 * 9)) - 1) = pk 13 (133 * 9) (fun _ => 1) := by
    rw [hL]
    refine pk_of_fld (by norm_num) (CFSG.KS.PackFld.fld_congr (fld_and (fld_pk (fun _ _ => by norm_num))
      (fld_RM 13 (133 * 9))) fun t => ?_) (fun _ _ => by norm_num)
    by_cases ht : t < 133 * 9
    · have ht' : t < 133 * 133 := by omega
      simp only [ht, ht', ↓reduceIte]
      decide
    · simp [ht]
  have hHb : pk 13 (133 * 9) (fun _ => 1) * 2 ^ 12 = pk 13 (133 * 9) (fun _ => 2 ^ (13 - 1)) := by
    rw [pk_mul]
    exact pk_congr fun _ _ => by norm_num
  rw [hLb, hHb, slw_and] at hbw
  obtain ⟨hbw1, hbw2⟩ := slj_validM_pk (w := 13) (n := 133 * 9) (nb := Nat.mul 9 1729)
    (by norm_num) rfl (by norm_num) hbw.1
  obtain ⟨b, hbeq, hb⟩ : ∃ b, bw = pk 13 (133 * 9) b ∧ ∀ t < 133 * 9, b t < 5 :=
    ⟨lane 13 bw, pk_lane (w := 13) (n := 133 * 9) (by norm_num) hbw1, hbw2⟩
  rw [hbeq] at hbw hinv
  obtain ⟨hcl5, hcl⟩ := slj_clsOK ce 0 hcls
  have hclass : ∀ k < 5, clK M ONE A B (lk ONE bl cur n) (hsL.map (sljPw M ONE)) hsL
      (lk ONE bl cur n (wr.getD k 0)) (ce.getD k []) (lp.getD k []) (lab.getD k []) = true := by
    intro k hk
    have h' := hcl k (by omega)
    rwa [Nat.zero_add] at h'
  refine ⟨fun r => OM (lk ONE bl cur n r), fun i => OM (hsL.getD i.val 0),
    fun k => vOf 133 (rowK 1729 k.val (pk 13 (133 * 9) b)),
    ⟨fun r => (hPl r).2, fun i => (hsPi i).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro i
    obtain ⟨r, -, hr⟩ := slj_relsOK _ 0 0 hrel i.val i.val le_rfl i.isLt (by omega)
    obtain ⟨he5, he0, hpow, -⟩ := slj_relOK hr
    refine ⟨ex (tl (tl r)), fun t ht => he0 t.val (by have := Fin.le_def.1 ht; omega), ?_⟩
    rw [← (hnf _ he5).2, ← hpow rfl, (hpwi i).2]
  ·
    intro i j hij
    have hij' : i.val < j.val := hij
    obtain ⟨r, -, hr⟩ := slj_relsOK _ 0 0 hrel i.val j.val hij'.le j.isLt (by omega)
    obtain ⟨he5, he0, -, hconj⟩ := slj_relOK hr
    refine ⟨ex (tl (tl r)), fun t ht => he0 t.val (by have := Fin.le_def.1 ht; omega), ?_⟩
    have e := hconj (by omega)
    beta_reduce
    rw [← (hnf _ he5).2, ← (hmulC _ _ (hsPi j).1 (hsPi i).1).2,
      ← (hmulC _ _ (hsPi i).1 (hnf _ he5).1.1).2, e]
  ·
    have e0 := r0.1
    rw [hr0] at e0
    obtain ⟨he5, -, hpow, -⟩ := slj_relOK e0
    calc OM (hsL.getD 0 0) ^ 5 = OM (((hsL.map (sljPw M ONE)).getD 0 []).getD 5 0) :=
          (hpwi 0).2.symm
      _ = OM (nfM M ONE (hsL.map (sljPw M ONE)) (tl (tl [0, 0, 0, 0, 0, 0, 0, 0]))) :=
          congrArg OM (hpow rfl)
      _ = 1 := by
          rw [(hnf _ he5).2, hex]
          simp [nfP]
  ·
    have e1 := r6.1
    rw [e6, hr6] at e1
    obtain ⟨he5, -, hpow, -⟩ := slj_relOK e1
    calc OM (hsL.getD 1 0) ^ 5 = OM (((hsL.map (sljPw M ONE)).getD 1 []).getD 5 0) :=
          (hpwi 1).2.symm
      _ = OM (nfM M ONE (hsL.map (sljPw M ONE)) (tl (tl [1, 1, 0, 0, 0, 0, 0, 0]))) :=
          congrArg OM (hpow rfl)
      _ = 1 := by
          rw [(hnf _ he5).2, hex1]
          simp [nfP]
  ·
    intro i
    unfold invOK at hinv
    have hi6 : ∀ i < 6, invOne (vecR 5 13 1729 133 9 LV HV RM) LV HV RM (pk 13 (133 * 9) b)
        (nthD 0 hsL i) (nthD 0 hwm i) = true := slj_recAll 6 hinv
    have hi1 := hi6 i.val i.isLt
    rw [slw_nthD, slw_nthD] at hi1
    unfold invOne at hi1
    have hi9 : ∀ k < 9, Nat.beq (vecR 5 13 1729 133 9 LV HV RM (rowK 1729 k (pk 13 (133 * 9) b))
        (hsL.getD i.val 0)) (redP 13 LV HV 5 9 (vecU 13 1729 9 RM (rowK 117 k (hwm.getD i.val 0))
          (pk 13 (133 * 9) b))) = true := slj_recAll 9 hi1
    funext k j
    have hrow := congrFun (slj_invRow hc hb (hsPi i).1 (hwmi i.val i.isLt) k.isLt
      (Nat.eq_of_beq_eq_true (hi9 k.val k.isLt))) j
    simp only [Matrix.vecMul, dotProduct] at hrow
    change ∑ l, vOf 133 (rowK 1729 k.val (pk 13 (133 * 9) b)) l * OM (hsL.getD i.val 0) l j =
      ∑ l, ordMat 5 9 13 117 (hwm.getD i.val 0) k l * vOf 133 (rowK 1729 l.val (pk 13 (133 * 9) b)) j
    exact hrow
  ·
    intro k l
    have hid9 : ∀ k < 9, Nat.beq (Nat.land (rowK 1729 k (pk 13 (133 * 9) b))
        (Nat.sub (Nat.shiftLeft 1 117) 1)) (Nat.shiftLeft 1 (Nat.mul 13 k)) = true :=
      slj_recAll 9 hbw.2
    have hid := hid9 k.val k.isLt
    have e3 : rowK 1729 k.val (pk 13 (133 * 9) b) &&& (2 ^ (13 * 9) - 1) = 2 ^ (13 * k.val) := by
      have h3 := Nat.eq_of_beq_eq_true hid
      have e4 : Nat.shiftLeft 1 (Nat.mul 13 k.val) = 2 ^ (13 * k.val) := by
        change 1 <<< (13 * k.val) = _
        rw [Nat.shiftLeft_eq, Nat.one_mul]
      have e5 : Nat.sub (Nat.shiftLeft 1 117) 1 = 2 ^ (13 * 9) - 1 := by
        change 1 <<< 117 - 1 = _
        rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [e4, e5] at h3
      exact h3
    change ((lane 13 (rowK 1729 k.val (pk 13 (133 * 9) b)) l.val : ℕ) : ZMod 5) = _
    rw [← slj_lane_and (w := 13) (n := 9) (X := rowK 1729 k.val (pk 13 (133 * 9) b)) l.isLt, e3,
      slj_lane_unit (d := 9) (by norm_num) k.isLt l.isLt]
    by_cases hkl : k = l
    · subst hkl
      simp
    · have hlk : l.val ≠ k.val := fun e => hkl (Fin.ext e.symm)
      simp [hkl, hlk]
  ·
    intro f hf
    obtain ⟨hf5, hf7, hfe⟩ := slj_fusOK fus hfus f hf
    refine ⟨hf7, ?_⟩
    have hy := hnf f hf5
    beta_reduce
    rw [← hy.2, ← (hmulC _ _ hy.1.1 (hPl _).1).2, hfe, (hmulC _ _ (hPl _).1 (hPl _).1).2]
  ·
    intro k hk e he
    have h' := hclass k hk
    unfold clK at h'
    rw [slw_and] at h'
    obtain ⟨he5, h1, h2⟩ := slj_entOK (slj_ents _ h'.1 e he)
    have hy := hnf e he5
    beta_reduce
    rw [← hy.2]
    refine ⟨?_, fun z hz' => ?_⟩
    · rw [← (hmulC _ _ (hPl _).1 (hPl _).1).2, ← (hmulC _ _ (hPl _).1 hy.1.1).2, h1]
    · rw [← (hmulC _ _ (hPl _).1 hy.1.1).2, ← (hmulC _ _ hy.1.1 (hPl _).1).2,
        slj_commOK _ h2 z hz']
  ·
    intro k hk
    have h' := hclass k hk
    unfold clK at h'
    simp only [slw_and, slj_mapS, slj_revOnto, slj_zsOf, slj_lenN] at h'
    obtain ⟨-, hlp⟩ := h'
    let P2 : ℕ → Prop := fun x => Canon 5 133 13 x ∧ OM x ∈ Submonoid.closure
      (Set.range (fun i : Fin 6 => OM (hsL.getD i.val 0)) ∪
        {Y | ∃ z ∈ (ce.getD k []).flatMap (·.drop 7), Y = OM (lk ONE bl cur n z)})
    have hP21 : P2 ONE := ⟨hone.1, by rw [hone.2]; exact Submonoid.one_mem _⟩
    have hP2m : ∀ a b, P2 a → P2 b → P2 (M a b) := fun a b ha hb =>
      ⟨(hmulC a b ha.1 hb.1).1, by rw [(hmulC a b ha.1 hb.1).2]; exact Submonoid.mul_mem _ ha.2 hb.2⟩
    have hinit : sljAll P2 [] ((((ce.getD k []).flatMap (·.drop 7)).map (lk ONE bl cur n)).reverse ++
        (hsL.reverse ++ [ONE])) := by
      refine ⟨fun b hb => absurd hb List.not_mem_nil, fun x hx => ?_⟩
      simp only [List.mem_append, List.mem_reverse, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨z, hz, rfl⟩ | hs' | rfl
      · exact ⟨(hPl z).1, Submonoid.subset_closure (Or.inr ⟨z, hz, rfl⟩)⟩
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs'
        refine ⟨(hsP _ (List.getElem_mem hj)).1,
          Submonoid.subset_closure (Or.inl ⟨⟨j, by omega⟩, ?_⟩)⟩
        beta_reduce
        rw [List.getD_eq_getElem _ _ hj]
      · exact hP21
    obtain ⟨bl', cur', n', hall', hk'⟩ := slj_runP hP21 hP2m _ [] _ _ _ hinit hlp
    rw [slw_and] at hk'
    obtain ⟨ha, hb⟩ := hk'
    have hA2 := (slj_lk_P hP21 hall' n' (nthD 0 (lab.getD k []) 0)).2
    have hB2 := (slj_lk_P hP21 hall' n' (nthD 0 (lab.getD k []) 1)).2
    rw [Nat.eq_of_beq_eq_true ha] at hA2
    rw [Nat.eq_of_beq_eq_true hb] at hB2
    exact ⟨hA2, hB2⟩

theorem chkW_sound {L9 H9 CM9 RM9 ONE9 LV9 HV9 : Nat} {hwm : List Nat} {c0 : Nat}
    {keyc : List Nat} {dep jb : Nat} {fus oth : List (List Nat)}
    (h : chkW (vecR 5 13 117 9 9 LV9 HV9 RM9) L9 H9 CM9 RM9 ONE9 LV9 HV9 hwm c0 keyc dep jb fus oth =
      true) :
    ∃ D, WFacts (fun i => ordMat 5 9 13 117 (hwm.getD i.val 0)) (vOf 9 c0) D fus oth := by
  unfold chkW at h
  simp only [slw_and, slw_sB] at h
  obtain ⟨hc9, hW, hc0, hfus, hoth, hnest⟩ := h
  have hvec : VecOK (vecR 5 13 117 9 9 LV9 HV9 RM9) := fun v M hv hM =>
    CFSG.KC.LQT.SecS.vecR_sound hc9 hv hM
  unfold hwmOK at hW
  rw [slw_and] at hW
  have hCan := slw_valid hc9 hwm hW.2
  have hc0' : CFSG.KC.LQT.SecS.VCanon 5 9 13 c0 := CFSG.KS.J4Hub.validV_canon hc9 hc0
  have hfus' := slw_fus fus hfus
  have hoth' := slw_othOK hvec hc0' hCan oth hoth
  have hlen : hwm.length = 6 := Nat.eq_of_beq_eq_true hW.1
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ :
      ∃ h0 h1 h2 h3 h4 h5 : ℕ, hwm = [h0, h1, h2, h3, h4, h5] := by
    match hwm, hlen with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨h0, h1, h2, h3, h4, h5, rfl⟩
  have hc1 : CFSG.KC.LQT.SecS.VCanon 5 9 13
      (pow4 (vecR 5 13 117 9 9 LV9 HV9 RM9) (nthD 0 [h0, h1, h2, h3, h4, h5] 0) c0) ∧
      vOf 9 (pow4 (vecR 5 13 117 9 9 LV9 HV9 RM9) (nthD 0 [h0, h1, h2, h3, h4, h5] 0) c0) =
        vOf 9 c0 ᵥ* ordMat 5 9 13 117 (nthD 0 [h0, h1, h2, h3, h4, h5] 0) ^ 4 :=
    slw_itV hvec (hCan h0 (by simp)) hc0' 4
  have hc2 : CFSG.KC.LQT.SecS.VCanon 5 9 13
      (pow4 (vecR 5 13 117 9 9 LV9 HV9 RM9) (nthD 0 [h0, h1, h2, h3, h4, h5] 1) c0) ∧
      vOf 9 (pow4 (vecR 5 13 117 9 9 LV9 HV9 RM9) (nthD 0 [h0, h1, h2, h3, h4, h5] 1) c0) =
        vOf 9 c0 ᵥ* ordMat 5 9 13 117 (nthD 0 [h0, h1, h2, h3, h4, h5] 1) ^ 4 :=
    slw_itV hvec (hCan h1 (by simp)) hc0' 4
  generalize pow4 (vecR 5 13 117 9 9 LV9 HV9 RM9) (nthD 0 [h0, h1, h2, h3, h4, h5] 0) c0 =
    c1 at hnest hc1
  generalize pow4 (vecR 5 13 117 9 9 LV9 HV9 RM9) (nthD 0 [h0, h1, h2, h3, h4, h5] 1) c0 =
    c2 at hnest hc2
  have hMs : ∀ j < 2, Canon 5 9 13 ([h0, h1, h2, h3, h4, h5].getD j 0) := by
    intro j hj
    interval_cases j
    · exact hCan h0 (by simp)
    · exact hCan h1 (by simp)
  have hR : wRel (vOf 9 c0) (vOf 9 c1) (vOf 9 c2) c0 c1 c2 1 :=
    ⟨hc0', hc1.1, hc2.1, (Matrix.vecMul_one _).symm, (Matrix.vecMul_one _).symm,
      (Matrix.vecMul_one _).symm⟩
  obtain ⟨hLf, -⟩ := slw_nest hvec (slw_leaf hvec hMs (keyc := keyc) (dep := dep) (jb := jb)
    (msk := maskOf oth (maskOf fus 0)) (b0 := vOf 9 c0) (b1 := vOf 9 c1) (b2 := vOf 9 c2)
    (Ok := wTall [h0, h1, h2, h3, h4, h5]) (fun _ _ _ h h' => slw_tall_fun h h'))
    [h0, h1, h2, h3, h4, h5] hCan c0 c1 c2 0 0 _ 1 hR
    (fun X i hT => by
      rw [one_mul, Nat.zero_add]
      exact slw_tall6 hT)
    (fun X i _ hi => absurd hi (Nat.not_lt_zero _)) hnest
  have hA : ∀ a : Fin 6 → ℕ, (∀ t, a t < 5) →
      wLf [h0, h1, h2, h3, h4, h5] keyc dep jb (maskOf oth (maskOf fus 0)) (vOf 9 c0)
        (vOf 9 c1) (vOf 9 c2) (wTall [h0, h1, h2, h3, h4, h5])
        (nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0)) a)
        (cd5 a) := by
    intro a ha
    have h' := hLf _ _ (slw_nT6 h0 h1 h2 h3 h4 h5 a ha)
    rwa [one_mul, Nat.zero_add] at h'
  refine ⟨fun v => bitsN dep (Nat.mul 4 (kV keyc v)) 4, ⟨?_, ?_, ?_⟩⟩
  ·
    intro a b ha hb hab
    by_contra hne
    have key : ∀ x y : Fin 6 → ℕ, (∀ t, x t < 5) → (∀ t, y t < 5) → cd5 x < cd5 y →
        vOf 9 c0 ᵥ* nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0)) x ≠
          vOf 9 c0 ᵥ* nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0))
            y := by
      intro x y hx hy hlt heq
      obtain ⟨mask, hIm, hnew, -, -⟩ := hA y hy
      have h1' := hIm _ _ ⟨x, hx, rfl, rfl⟩ hlt
      rw [heq, hnew] at h1'
      exact absurd h1' (by norm_num)
    rcases Nat.lt_or_gt_of_ne (fun e => hne (slw_cd5_inj ha hb e)) with hlt | hlt
    · exact key a b ha hb hlt hab
    · exact key b a hb ha hlt hab.symm
  ·
    intro o ho
    have hne := (hoth' o ho).2
    rwa [slw_prodW6] at hne
  ·
    intro a ha
    obtain ⟨mask, -, -, hz, hnz⟩ := hA a ha
    refine ⟨fun hd0 => ?_, fun hd0 => ?_⟩
    · rcases hz hd0 with hm | hm
      · exact Or.inl (slw_cd5_zero hm)
      · right
        rcases slw_maskOf oth _ _ hm with hm' | ⟨c, hc, hce⟩
        · rcases slw_maskOf fus 0 _ hm' with hm'' | ⟨c, hc, hce⟩
          · exfalso
            rw [slw_bitsN, Nat.zero_div, Nat.zero_mod] at hm''
            exact absurd hm'' (by norm_num)
          · exact ⟨c, List.mem_append_left _ hc, slw_ex_of_code ha (hfus' c hc) hce⟩
        · exact ⟨c, List.mem_append_right _ hc, slw_ex_of_code ha (hoth' c hc).1 hce⟩
    · rcases hnz hd0 with ⟨-, hd⟩ | ⟨-, hd⟩
      · refine ⟨0, by decide, ?_⟩
        have heq : vOf 9 c1 ᵥ*
            nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0)) a ᵥ*
              ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD 0 0) =
            vOf 9 c0 ᵥ* (ordMat 5 9 13 117 h0 ^ 4 *
              nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0)) a *
                ordMat 5 9 13 117 h0) := by
          rw [hc1.2]
          simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
          all_goals rfl
        rw [heq] at hd
        exact hd
      · refine ⟨1, by decide, ?_⟩
        have heq : vOf 9 c2 ᵥ*
            nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0)) a ᵥ*
              ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD 1 0) =
            vOf 9 c0 ᵥ* (ordMat 5 9 13 117 h1 ^ 4 *
              nfP (fun t => ordMat 5 9 13 117 ([h0, h1, h2, h3, h4, h5].getD t.val 0)) a *
                ordMat 5 9 13 117 h1) := by
          rw [hc2.2]
          simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
          all_goals rfl
        rw [heq] at hd
        exact hd

section Models

theorem nfP_map {M N : Type} [Monoid M] [Monoid N] (f : M →* N) (hs : Fin 6 → M) (a : Fin 6 → ℕ) :
    f (nfP hs a) = nfP (fun i => f (hs i)) a := by
  simp only [nfP, map_mul, map_pow]

theorem nfP_zero {M : Type} [Monoid M] (hs : Fin 6 → M) : nfP hs 0 = 1 := by
  simp [nfP]

variable {BW : Matrix (Fin 9) (Fin 133) (ZMod 5)}

theorem inter_mul {X Y : M133} {X' Y' : M9} (hX : BW * X = X' * BW) (hY : BW * Y = Y' * BW) :
    BW * (X * Y) = X' * Y' * BW := by
  rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, hY, Matrix.mul_assoc]

theorem inter_pow {X : M133} {X' : M9} (hX : BW * X = X' * BW) :
    ∀ n : ℕ, BW * X ^ n = X' ^ n * BW
  | 0 => by rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
  | n + 1 => by rw [pow_succ, pow_succ]; exact inter_mul (inter_pow hX n) hX

theorem inter_nfP {hs : Fin 6 → M133} {HM : Fin 6 → M9} (h : ∀ i, BW * hs i = HM i * BW)
    (a : Fin 6 → ℕ) : BW * nfP hs a = nfP HM a * BW := by
  unfold nfP
  exact inter_mul (inter_mul (inter_mul (inter_mul (inter_mul (inter_pow (h 0) _)
    (inter_pow (h 1) _)) (inter_pow (h 2) _)) (inter_pow (h 3) _)) (inter_pow (h 4) _))
    (inter_pow (h 5) _)

theorem psi_vecMul (hid : ∀ k l : Fin 9, BW k (Fin.castLE (by norm_num) l) = if k = l then 1 else 0)
    (u : Fin 9 → ZMod 5) : psi (u ᵥ* BW) = u := by
  funext l
  simp only [psi, Matrix.vecMul, dotProduct, hid, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem psi_inter (hid : ∀ k l : Fin 9, BW k (Fin.castLE (by norm_num) l) = if k = l then 1 else 0)
    {X : M133} {X' : M9} (hX : BW * X = X' * BW) (v0 : Fin 9 → ZMod 5) :
    psi ((v0 ᵥ* BW) ᵥ* X) = v0 ᵥ* X' := by
  rw [Matrix.vecMul_vecMul, hX, ← Matrix.vecMul_vecMul, psi_vecMul hid]

end Models

section Group

variable {G : Type} [Group G]

theorem exists_of_mclosure {M : Type} [Monoid M] (ρ : G →* M) (a b : G) {X : M}
    (hX : X ∈ Submonoid.closure ({ρ a, ρ b} : Set M)) : ∃ g, ρ g = X := by
  have hle : Submonoid.closure ({ρ a, ρ b} : Set M) ≤ MonoidHom.mrange ρ := by
    rw [Submonoid.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨a, rfl⟩
    · exact ⟨b, rfl⟩
  exact hle hX

theorem mem_of_mclosure {M : Type} [Monoid M] (ρ : G →* M) (hρ : Function.Injective ρ)
    (T : Subgroup G) {S : Set M} (hS : ∀ X ∈ S, ∃ t ∈ T, ρ t = X) {g : G}
    (hg : ρ g ∈ Submonoid.closure S) : g ∈ T := by
  have hle : Submonoid.closure S ≤ T.toSubmonoid.map ρ := by
    rw [Submonoid.closure_le]
    intro X hX
    obtain ⟨t, ht, e⟩ := hS X hX
    exact ⟨t, ht, e⟩
  obtain ⟨t, ht, e⟩ := hle hg
  rw [← hρ e]
  exact ht

variable (g : Fin 6 → G)

theorem nfP_mem_pcSub {i : Fin 6} {e : Fin 6 → ℕ} (he : ∀ t, t ≤ i → e t = 0) :
    nfP g e ∈ pcSub (fun t => (g t)⁻¹) (i.val + 1) := by
  have hf : ∀ t : Fin 6, g t ^ e t ∈ pcSub (fun t => (g t)⁻¹) (i.val + 1) := by
    intro t
    by_cases ht : t ≤ i
    · rw [he t ht, pow_zero]
      exact Subgroup.one_mem _
    · have hlt : i.val + 1 ≤ t.val := by
        rw [Fin.not_le] at ht
        exact ht
      have hm : (g t)⁻¹ ∈ pcSub (fun t => (g t)⁻¹) (i.val + 1) :=
        Subgroup.subset_closure ⟨t, hlt, rfl⟩
      exact Subgroup.pow_mem _ (by simpa using Subgroup.inv_mem _ hm) _
  unfold nfP
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (hf 0) (hf 1)) (hf 2)) (hf 3)) (hf 4)) (hf 5)

theorem nfP_mem (e : Fin 6 → ℕ) : nfP g e ∈ pcSub (fun t => (g t)⁻¹) 0 := by
  have hf : ∀ t : Fin 6, g t ^ e t ∈ pcSub (fun t => (g t)⁻¹) 0 := by
    intro t
    have hm : (g t)⁻¹ ∈ pcSub (fun t => (g t)⁻¹) 0 := Subgroup.subset_closure ⟨t, Nat.zero_le _, rfl⟩
    exact Subgroup.pow_mem _ (by simpa using Subgroup.inv_mem _ hm) _
  unfold nfP
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (hf 0) (hf 1)) (hf 2)) (hf 3)) (hf 4)) (hf 5)

theorem gen_mem (i : Fin 6) : g i ∈ pcSub (fun t => (g t)⁻¹) 0 := by
  have hm : (g i)⁻¹ ∈ pcSub (fun t => (g t)⁻¹) 0 := Subgroup.subset_closure ⟨i, Nat.zero_le _, rfl⟩
  simpa using Subgroup.inv_mem _ hm

theorem pc_card [Finite G]
    (hpow : ∀ i : Fin 6, ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧ g i ^ 5 = nfP g e)
    (hconj : ∀ i j : Fin 6, i < j → ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧
      g j * g i = g i * nfP g e) :
    Nat.card (pcSub (fun t => (g t)⁻¹) 0) ≤ 5 ^ 6 := by
  set q : Fin 6 → G := fun t => (g t)⁻¹ with hq
  have hp : ∀ i : Fin 6, q i ^ 5 ∈ pcSub q (i.val + 1) := by
    intro i
    obtain ⟨e, he, h⟩ := hpow i
    rw [hq, inv_pow, h]
    exact Subgroup.inv_mem _ (nfP_mem_pcSub g he)
  have hc : ∀ i j : Fin 6, i < j → q i * q j * (q i)⁻¹ ∈ pcSub q (i.val + 1) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := hconj i j hij
    have e1 : q i * q j * (q i)⁻¹ = ((g i)⁻¹ * g j * g i)⁻¹ := by
      rw [hq]
      group
    have e2 : (g i)⁻¹ * g j * g i = nfP g e := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e1, e2]
    exact Subgroup.inv_mem _ (nfP_mem_pcSub g he)
  have key : ∀ m : ℕ, m ≤ 6 → Nat.card (pcSub q (6 - m)) ≤ 5 ^ m := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.sub_zero, pcSub_n, pow_zero]
      simp
    | succ m ih =>
      intro hm
      have hi : 6 - (m + 1) < 6 := by omega
      have e : (6 - (m + 1)) + 1 = 6 - m := by omega
      have hf' : Finite (pcSub q (6 - (m + 1) + 1)) := inferInstance
      have h := pcSub_card_step (by norm_num : 0 < 5) q ⟨6 - (m + 1), hi⟩ hf' (hp ⟨6 - (m + 1), hi⟩)
        (fun j hj => hc ⟨6 - (m + 1), hi⟩ j hj)
      have h3 : Nat.card (pcSub q (6 - (m + 1))) ≤ 5 * Nat.card (pcSub q (6 - (m + 1) + 1)) := h.2
      rw [e] at h3
      calc Nat.card (pcSub q (6 - (m + 1))) ≤ 5 * Nat.card (pcSub q (6 - m)) := h3
        _ ≤ 5 * 5 ^ m := Nat.mul_le_mul_left _ (ih (by omega))
        _ = 5 ^ (m + 1) := by ring
  exact key 6 le_rfl

end Group

section Classes

variable {G : Type} [Group G] [Finite G] (ρ : G →* M133) (hρ : Function.Injective ρ)
include hρ

theorem classes_of_facts (a b : G) {m : ℕ} (hG : Nat.card G = 5 ^ 6 * m) (hm : ¬ 5 ∣ m)
    {wr : List ℕ} {fus oth : List (List ℕ)} {ce : List (List (List ℕ))} {R : ℕ → M133}
    {hs : Fin 6 → M133} {BW : Matrix (Fin 9) (Fin 133) (ZMod 5)} {HM : Fin 6 → M9}
    {v0 : Fin 9 → ZMod 5} {D : (Fin 9 → ZMod 5) → ℕ}
    (hJ : JFacts (ρ a) (ρ b) wr fus ce R hs BW HM) (hW : WFacts HM v0 D fus oth) :
    ∃ (S₀ : Subgroup G) (X : ℕ → G), IsPGroup 5 S₀ ∧
      (∀ s : G, orderOf s = 5 → ∃ k < 5, IsConj (X k) s) ∧
      ∀ k < 5, ∃ Z : Set G, (∀ z ∈ Z, ∃ h y : G, y ∈ S₀ ∧ h⁻¹ * X k * h = y ∧ z * y = y * z) ∧
        a ∈ Subgroup.closure ((S₀ : Set G) ∪ Z) ∧ b ∈ Subgroup.closure ((S₀ : Set G) ∪ Z) := by
  choose rr hrr using fun r => exists_of_mclosure ρ a b (hJ.reg r)
  choose g hg using fun i => exists_of_mclosure ρ a b (hJ.gen i)
  have hgs : (fun i => ρ (g i)) = hs := funext hg
  have nfρ : ∀ e, ρ (nfP g e) = nfP hs e := fun e => by rw [nfP_map, hgs]
  set P : Subgroup G := pcSub (fun t => (g t)⁻¹) 0 with hP
  set w0 : Fin 133 → ZMod 5 := v0 ᵥ* BW with hw0
  have hvec : ∀ e, psi (w0 ᵥ* ρ (nfP g e)) = v0 ᵥ* nfP HM e := fun e => by
    rw [nfρ]
    exact psi_inter hJ.ident (inter_nfP hJ.inter e) v0
  have hpowG : ∀ i : Fin 6, ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧ g i ^ 5 = nfP g e := by
    intro i
    obtain ⟨e, he, h⟩ := hJ.pow i
    exact ⟨e, he, hρ (by rw [map_pow, hg, nfρ, h])⟩
  have hconjG : ∀ i j : Fin 6, i < j → ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧
      g j * g i = g i * nfP g e := by
    intro i j hij
    obtain ⟨e, he, h⟩ := hJ.conj i j hij
    exact ⟨e, he, hρ (by rw [map_mul, map_mul, hg, hg, nfρ, h])⟩
  have hcard_le := pc_card g hpowG hconjG
  let Y : (Fin 6 → Fin 5) → P := fun a => ⟨nfP g (fun t => (a t : ℕ)), nfP_mem g _⟩
  have hYinj : Function.Injective Y := by
    intro a₁ a₂ h
    have h1 : nfP g (fun t => (a₁ t : ℕ)) = nfP g (fun t => (a₂ t : ℕ)) := congrArg Subtype.val h
    have h2 := congrArg (fun x => psi (w0 ᵥ* ρ x)) h1
    simp only [hvec] at h2
    have h3 := hW.inj _ _ (fun t => (a₁ t).isLt) (fun t => (a₂ t).isLt) h2
    funext t
    exact Fin.ext (congrFun h3 t)
  have hcardA : Nat.card (Fin 6 → Fin 5) = 5 ^ 6 := by simp
  have hYbij : Function.Bijective Y :=
    hYinj.bijective_of_nat_card_le (by rw [hcardA]; exact hcard_le)
  have hcardP : Nat.card P = 5 ^ 6 := by
    rw [← Nat.card_eq_of_bijective Y hYbij, hcardA]
  have hsurj : ∀ x ∈ P, ∃ e : Fin 6 → ℕ, (∀ t, e t < 5) ∧ x = nfP g e := by
    intro x hx
    obtain ⟨a', ha'⟩ := hYbij.2 ⟨x, hx⟩
    exact ⟨fun t => (a' t : ℕ), fun t => (a' t).isLt, (congrArg Subtype.val ha').symm⟩
  have hpg : IsPGroup 5 P := IsPGroup.of_card hcardP
  have hg5 : ∀ j : Fin 6, j.val < 2 → g j ^ 5 = 1 := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by
      rcases j with ⟨_ | _ | _, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    apply hρ
    rw [map_pow, map_one, hg]
    rcases hj' with rfl | rfl
    · exact hJ.pow0
    · exact hJ.pow1
  let Good : G → Prop := fun x => x = 1 ∨ ∃ c ∈ fus ++ oth, IsConj (nfP g (ex c)) x
  have tree : ∀ n, ∀ e : Fin 6 → ℕ, (∀ t, e t < 5) → D (v0 ᵥ* nfP HM e) = n → Good (nfP g e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro e he hn
      obtain ⟨h0, hpos⟩ := hW.tree e he
      by_cases hz : D (v0 ᵥ* nfP HM e) = 0
      · rcases h0 hz with rfl | ⟨c, hc, rfl⟩
        · exact Or.inl (nfP_zero g)
        · exact Or.inr ⟨c, hc, IsConj.refl _⟩
      · obtain ⟨j, hj, hd⟩ := hpos hz
        set x := nfP g e
        have hx' : g j ^ 4 * x * g j ∈ P :=
          P.mul_mem (P.mul_mem (P.pow_mem (gen_mem g j) 4) (nfP_mem g e)) (gen_mem g j)
        obtain ⟨e', he', hxe⟩ := hsurj _ hx'
        have hv : v0 ᵥ* nfP HM e' = v0 ᵥ* (HM j ^ 4 * nfP HM e * HM j) := by
          rw [← hvec e', ← hxe, map_mul, map_mul, map_pow, hg, nfρ]
          exact psi_inter hJ.ident (inter_mul (inter_mul (inter_pow (hJ.inter j) 4)
            (inter_nfP hJ.inter e)) (hJ.inter j)) v0
        have hlt : D (v0 ᵥ* (HM j ^ 4 * nfP HM e * HM j)) < n := by omega
        have hgood := ih _ hlt e' he' (by rw [hv])
        have hconj' : g j ^ 4 * x * g j = (g j)⁻¹ * x * g j := by
          have e5 : g j ^ 4 = (g j)⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← pow_succ, hg5 j hj]
          rw [e5]
        have hxc : IsConj x (nfP g e') := by
          rw [← hxe, hconj', isConj_iff]
          exact ⟨(g j)⁻¹, by group⟩
        rcases hgood with h1 | ⟨c, hc, hcc⟩
        · left
          rw [h1] at hxc
          exact isConj_one_left.mp hxc
        · exact Or.inr ⟨c, hc, hcc.trans hxc.symm⟩
  let X : ℕ → G := fun k => rr (wr.getD k 0)
  refine ⟨P, X, hpg, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, hc⟩ := exists_conj_into_range Nat.prime_five P.subtype P.subtype_injective hcardP hG
      hm hs
    rw [Subgroup.range_subtype] at hc
    obtain ⟨e, he, hxe⟩ := hsurj _ hc
    have hxs : IsConj (nfP g e) s := by
      rw [← hxe, isConj_iff]
      exact ⟨c, by group⟩
    rcases tree _ e he rfl with h1 | ⟨f, hf, hfc⟩
    · exfalso
      rw [h1] at hxs
      have := isConj_one_right.mp hxs
      rw [this, orderOf_one] at hs
      omega
    · have hfs := hfc.trans hxs
      rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨ht, hfe⟩ := hJ.fus f hf
        refine ⟨f.getD 7 0, ht, IsConj.trans ?_ hfs⟩
        rw [isConj_iff]
        refine ⟨rr (f.getD 6 0), ?_⟩
        have hgm : nfP g (ex f) * rr (f.getD 6 0) = rr (f.getD 6 0) * X (f.getD 7 0) :=
          hρ (by rw [map_mul, map_mul, nfρ, hrr, hrr, hfe])
        rw [← hgm, mul_inv_cancel_right]
      · exfalso
        obtain ⟨d, hd⟩ := isConj_iff.mp hfs
        have h5 : nfP g (ex f) ^ 5 = 1 := by
          have hs5 : s ^ 5 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
          rw [← hd, conj_pow] at hs5
          have := congrArg (fun u => d⁻¹ * u * d) hs5
          simpa [mul_assoc] using this
        apply hW.othK f hf
        rw [← psi_inter hJ.ident (inter_pow (inter_nfP hJ.inter (ex f)) 5) v0, ← nfρ, ← map_pow,
          h5, map_one, Matrix.vecMul_one, psi_vecMul hJ.ident]
  · intro k hk
    let Zs : List ℕ := (ce.getD k []).flatMap (·.drop 7)
    refine ⟨{u | ∃ z ∈ Zs, u = rr z}, ?_, ?_⟩
    · rintro u ⟨z, hz, rfl⟩
      obtain ⟨e, he, hze⟩ := List.mem_flatMap.mp hz
      obtain ⟨h1, h2⟩ := hJ.ent k hk e he
      refine ⟨rr (e.getD 6 0), nfP g (ex e), nfP_mem g _, ?_, ?_⟩
      · have hgm : X k * rr (e.getD 6 0) = rr (e.getD 6 0) * nfP g (ex e) :=
          hρ (by rw [map_mul, map_mul, nfρ, hrr, hrr, h1])
        rw [mul_assoc, hgm, ← mul_assoc, inv_mul_cancel, one_mul]
      · exact hρ (by rw [map_mul, map_mul, nfρ, hrr, h2 z hze])
    · have hS : ∀ Y ∈ Set.range hs ∪ {X | ∃ z ∈ Zs, X = R z},
          ∃ t ∈ Subgroup.closure ((P : Set G) ∪ {u | ∃ z ∈ Zs, u = rr z}), ρ t = Y := by
        rintro Y (⟨i, rfl⟩ | ⟨z, hz, rfl⟩)
        · exact ⟨g i, Subgroup.subset_closure (Or.inl (gen_mem g i)), hg i⟩
        · exact ⟨rr z, Subgroup.subset_closure (Or.inr ⟨z, hz, rfl⟩), hrr z⟩
      exact ⟨mem_of_mclosure ρ hρ _ hS (hJ.seeds k hk).1,
        mem_of_mclosure ρ hρ _ hS (hJ.seeds k hk).2⟩

end Classes

end CFSG.KS.SlpPc

end
