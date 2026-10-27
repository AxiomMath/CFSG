module

public import CFSG.LargeExtraspecial.S63CD4Kit
public import CFSG.LargeExtraspecial.S63CD4Inputs
public import CFSG.Quasithin.Recognition.CertTriality
public import CFSG.Quasithin.Recognition.CertTrialityFaithful

public section

namespace CFSG.LargeExtraspecial.S63

open CFSG.Quasithin CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open CFSG.Monster.B.Co2 (allLt_spec)

theorem foldl_xor_lt (Y : Array ℕ) (v : ℕ) (hY : ∀ j < 24, Y[j]?.getD 0 < 2 ^ 24) :
    ∀ (l : List ℕ) (init : ℕ), init < 2 ^ 24 → (∀ j ∈ l, j < 24) →
      l.foldl (fun acc j => if v.testBit j then acc ^^^ (Y[j]?.getD 0) else acc) init < 2 ^ 24 := by
  intro l
  induction l with
  | nil => intro init h _; exact h
  | cons j l ih =>
    intro init h hl
    rw [List.foldl_cons]
    refine ih _ ?_ fun k hk => hl k (List.mem_cons_of_mem j hk)
    split_ifs
    · exact Nat.xor_lt_two_pow h (hY j (hl j List.mem_cons_self))
    · exact h

theorem vecMulN_lt' {Y : Array ℕ} (hY : ∀ j < 24, Y[j]?.getD 0 < 2 ^ 24) (v : ℕ) :
    vecMulN 24 Y v < 2 ^ 24 :=
  foldl_xor_lt Y v hY _ 0 (by norm_num) fun j hj => List.mem_range.1 hj

theorem validR_iff {R : Array ℕ} : validR R = true ↔ R.size = 24 ∧ ∀ i < 24, R[i]! < 2 ^ 24 := by
  simp [validR]

theorem validR_mulR {X Y : Array ℕ} (hX : X.size = 24) (hY : validR Y = true) :
    validR (mulR X Y) = true := by
  rw [validR_iff] at hY ⊢
  have hY' : ∀ j < 24, Y[j]?.getD 0 < 2 ^ 24 := by
    intro j hj
    rw [getElem?_getD_of_lt (by omega)]
    exact hY.2 j hj
  refine ⟨by simp [mulR, mulRows, hX], fun i hi => ?_⟩
  rw [getElem!_pos _ i (by simp [mulR, mulRows, hX]; omega)]
  simp only [mulR, mulRows, Array.getElem_map]
  exact vecMulN_lt' hY' _

theorem size_of_validR {R : Array ℕ} (h : validR R = true) : R.size = 24 :=
  (validR_iff.1 h).1

theorem validR_oneR : validR oneR = true := by decide

theorem validR_encRows (M : Matrix (Fin 8) (Fin 8) GF8) : validR (encRows M) = true := by
  rw [validR_iff]
  refine ⟨by simp [encRows], fun i hi => ?_⟩
  rw [getElem!_pos _ i (by simp [encRows]; omega)]
  simp only [encRows, Array.getElem_ofFn]
  exact ofBits_lt 24 _

theorem validR_conjI {g g' x : Array ℕ} (hg : g.size = 24) (hg' : validR g' = true) :
    validR (conjI g g' x) = true :=
  validR_mulR (by simp [mulR, mulRows, hg]) hg'

theorem validR_sq12R {x : Array ℕ} (hx : validR x = true) : validR (sq12R x) = true := by
  have key : ∀ (k : ℕ) (y : Array ℕ), validR y = true →
      validR ((List.range k).foldl (fun acc _ => mulR acc acc) y) = true := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have := ih y hy
      exact validR_mulR (size_of_validR this) this
  exact key 12 x hx

theorem validR_powRows {m : Array ℕ} (hm : validR m = true) (e : ℕ) :
    validR (powRows 24 m e) = true := by
  induction e with
  | zero => exact validR_oneR
  | succ e ih => exact validR_mulR (size_of_validR ih) hm

theorem validR_commI {x x' c c' : Array ℕ} (hx' : x'.size = 24) (hx : x.size = 24)
    (hc : validR c = true) : validR (commI x x' c c') = true :=
  validR_mulR (by simp [mulR, mulRows, hx']) (validR_mulR hx hc)

theorem validR_wordR {gs : Array (Array ℕ)} {w : List ℕ} (hw : ∀ k ∈ w, validR gs[k]! = true) :
    validR (wordR gs w) = true := by
  induction w with
  | nil => exact validR_oneR
  | cons k w ih =>
    rw [wordR, List.foldr_cons]
    exact validR_mulR (size_of_validR (hw k List.mem_cons_self))
      (ih fun k' hk' => hw k' (List.mem_cons_of_mem k hk'))

@[expose] noncomputable def d4E : trialityGroup8 →* Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  epsHom.comp ((Units.coeHom (Matrix (Fin 8) (Fin 8) GF8)).comp trialityGroup8.subtype)

theorem d4E_apply (g : trialityGroup8) :
    d4E g = epsM ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) := rfl

theorem d4E_injective : Function.Injective d4E := fun _ _ h =>
  Subtype.ext (Units.ext (epsM_injective h))

theorem eq_iff_of_repE {R S : Array ℕ} {g h : trialityGroup8} (hR : validR R = true)
    (hS : validR S = true) (hRg : RepE d4E R g) (hSh : RepE d4E S h) : R = S ↔ g = h := by
  constructor
  · rintro rfl
    exact eq_of_repE d4E_injective hRg hSh
  · rintro rfl
    exact arr_eq_of_repE hR hS hRg hSh

@[expose] noncomputable def d4Elt (a : GF8) (s : Bool) : trialityGroup8 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (trialityElt a s)
      (by rw [det_trialityElt]; exact one_ne_zero),
    Subgroup.subset_closure (Or.inl ⟨a, s, rfl⟩)⟩

@[expose] noncomputable def d4Mid (s : Bool) : trialityGroup8 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (trialityMid s)
      (by rw [det_trialityMid]; exact one_ne_zero),
    Subgroup.subset_closure (Or.inr ⟨s, rfl⟩)⟩

@[expose] noncomputable def d4GenG : ℕ → trialityGroup8
  | 0 => d4Elt (GF8.ofNat' 1) true
  | 1 => d4Elt (GF8.ofNat' 2) true
  | 2 => d4Elt (GF8.ofNat' 4) true
  | 3 => d4Elt (GF8.ofNat' 1) false
  | 4 => d4Elt (GF8.ofNat' 2) false
  | 5 => d4Elt (GF8.ofNat' 4) false
  | 6 => d4Mid true
  | _ => d4Mid false

theorem repE_d4Gens {k : ℕ} (hk : k < 8) : RepE d4E d4Gens[k]! (d4GenG k) := by
  unfold RepE
  rw [d4E_apply, ← rowsMatrix_encRows]
  interval_cases k <;> rfl

theorem validR_d4Gens {k : ℕ} (hk : k < 8) : validR d4Gens[k]! = true := by
  interval_cases k <;> exact validR_encRows _

@[expose] noncomputable def d4Word (w : List ℕ) : trialityGroup8 := (w.map d4GenG).prod

theorem repE_d4Word {w : List ℕ} (hw : ∀ k ∈ w, k < 8) : RepE d4E (wordR d4Gens w) (d4Word w) :=
  repE_wordR fun k hk => repE_d4Gens (hw k hk)

theorem validR_d4Word {w : List ℕ} (hw : ∀ k ∈ w, k < 8) : validR (wordR d4Gens w) = true :=
  validR_wordR fun k hk => validR_d4Gens (hw k hk)

@[expose] noncomputable def d4z : trialityGroup8 := d4Word wordZ

@[expose] noncomputable def d4t : trialityGroup8 := d4Word wordT

theorem repE_z0R : RepE d4E z0R d4z := repE_d4Word (by decide)

theorem repE_t0R : RepE d4E t0R d4t := repE_d4Word (by decide)

theorem validR_z0R : validR z0R = true := validR_d4Word (by decide)

theorem validR_t0R : validR t0R = true := validR_d4Word (by decide)

@[expose] noncomputable def uGH (i : ℕ) : trialityGroup8 := d4GenG (uIdx.getD i 0)

@[expose] noncomputable def lGH (i : ℕ) : trialityGroup8 := d4GenG (lIdx.getD i 0)

@[expose] noncomputable def qGH (i : ℕ) : trialityGroup8 := d4Word (qWords.getD i [])

@[expose] noncomputable def cGH (i : ℕ) : trialityGroup8 := d4Word (cWords.getD i [])

@[expose] noncomputable def d4U : Subgroup trialityGroup8 :=
  Subgroup.closure (genSet uGH uGens.size)

theorem uGens_size : uGens.size = 4 := rfl

theorem lGens_size : lGens.size = 6 := rfl

theorem qGens_size : qGens.size = 8 := rfl

theorem cGens_size : cGens.size = 4 := rfl

theorem uGens_getElem {i : ℕ} (hi : i < 4) : uGens[i]! = d4Gens[uIdx.getD i 0]! := by
  interval_cases i <;> simp [uGens, uIdx]

theorem lGens_getElem {i : ℕ} (hi : i < 6) : lGens[i]! = d4Gens[lIdx.getD i 0]! := by
  interval_cases i <;> simp [lGens, lIdx]

theorem qGens_getElem {i : ℕ} (hi : i < 8) : qGens[i]! = wordR d4Gens (qWords.getD i []) := by
  interval_cases i <;> simp [qGens, qWords]

theorem cGens_getElem {i : ℕ} (hi : i < 4) : cGens[i]! = wordR d4Gens (cWords.getD i []) := by
  interval_cases i <;> simp [cGens, cWords]

theorem uIdx_lt {i : ℕ} (hi : i < 4) : uIdx.getD i 0 < 8 := by
  interval_cases i <;> decide

theorem lIdx_lt {i : ℕ} (hi : i < 6) : lIdx.getD i 0 < 8 := by
  interval_cases i <;> decide

theorem qWords_lt {i : ℕ} (hi : i < 8) : ∀ k ∈ qWords.getD i [], k < 8 := by
  interval_cases i <;> decide

theorem cWords_lt {i : ℕ} (hi : i < 4) : ∀ k ∈ cWords.getD i [], k < 8 := by
  interval_cases i <;> decide

theorem repE_uGens {i : ℕ} (hi : i < uGens.size) : RepE d4E uGens[i]! (uGH i) := by
  rw [uGens_size] at hi
  rw [uGens_getElem hi]
  exact repE_d4Gens (uIdx_lt hi)

theorem repE_lGens {i : ℕ} (hi : i < lGens.size) : RepE d4E lGens[i]! (lGH i) := by
  rw [lGens_size] at hi
  rw [lGens_getElem hi]
  exact repE_d4Gens (lIdx_lt hi)

theorem repE_qGens {i : ℕ} (hi : i < qGens.size) : RepE d4E qGens[i]! (qGH i) := by
  rw [qGens_size] at hi
  rw [qGens_getElem hi]
  exact repE_d4Word (qWords_lt hi)

theorem repE_cGens {i : ℕ} (hi : i < cGens.size) : RepE d4E cGens[i]! (cGH i) := by
  rw [cGens_size] at hi
  rw [cGens_getElem hi]
  exact repE_d4Word (cWords_lt hi)

theorem validR_qGens {i : ℕ} (hi : i < qGens.size) : validR qGens[i]! = true := by
  rw [qGens_size] at hi
  rw [qGens_getElem hi]
  exact validR_d4Word (qWords_lt hi)

theorem validR_lGens {i : ℕ} (hi : i < lGens.size) : validR lGens[i]! = true := by
  rw [lGens_size] at hi
  rw [lGens_getElem hi]
  exact validR_d4Gens (lIdx_lt hi)

theorem mul_self_of_gensOK {gs : Array (Array ℕ)} {gH : ℕ → trialityGroup8}
    (hrep : ∀ k < gs.size, RepE d4E gs[k]! (gH k)) (h : gensOK gs = true) :
    ∀ k < gs.size, RepE d4E gs[k]! (gH k) ∧ gH k * gH k = 1 := by
  intro k hk
  refine ⟨hrep k hk, ?_⟩
  have h1 := allLt_spec h hk
  simp only [beq_iff_eq] at h1
  have h2 := repE_mul (hrep k hk) (hrep k hk)
  rw [h1] at h2
  exact eq_of_repE d4E_injective h2 repE_one

theorem invOK_spec {D : EnumData} {n : ℕ} (h : D.invOK n = true) {i : ℕ} (hi : i < n) :
    D.inv[i]! < n ∧ mulR D.El[i]! D.El[D.inv[i]!]! = oneR := by
  have := allLt_spec h hi
  simpa using this

theorem repE_inv_of_invOK {D : EnumData} {n : ℕ} {S : Subgroup trialityGroup8}
    (hEl : ∀ i < n, ∃ a ∈ S, RepE d4E D.El[i]! a) (hinv : D.invOK n = true) {i : ℕ}
    (hi : i < n) {a : trialityGroup8} (ha : RepE d4E D.El[i]! a) :
    D.inv[i]! < n ∧ RepE d4E D.El[D.inv[i]!]! a⁻¹ := by
  obtain ⟨hlt, heq⟩ := invOK_spec hinv hi
  obtain ⟨b, -, hb⟩ := hEl _ hlt
  have hab := repE_mul ha hb
  rw [heq] at hab
  have h1 : a * b = 1 := eq_of_repE d4E_injective hab repE_one
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact ⟨hlt, hb⟩

theorem pow_4096_eq_one {x : trialityGroup8} {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ^ 4096 = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have h2 : orderOf x ∣ 211341312 := card_trialityGroup8 ▸ _root_.orderOf_dvd_natCard x
  rw [hj] at h2
  have hj12 : j ≤ 12 := by
    by_contra hc
    have h13 : 2 ^ 13 ∣ 211341312 := (Nat.pow_dvd_pow 2 (by omega)).trans h2
    norm_num at h13
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact (Nat.pow_dvd_pow 2 hj12).trans (by norm_num)

end CFSG.LargeExtraspecial.S63
