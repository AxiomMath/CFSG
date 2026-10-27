module

public import CFSG.Certificates.Kernel.J4.M12Sound
public import CFSG.Certificates.Kernel.J4.ChainSound
public import CFSG.Certificates.Kernel.J4.KShapeSound
public import CFSG.Certificates.Kernel.DceTwCore
public import Certificates.Data.Kernel.J4Run
import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KJ4.Models

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat
open CFSG.Certificates.DceWord (lvE wv)
open CFSG.Certificates.J4Words (jv invJ jv_inv)
open CFSG.Certificates.J4KShape (rv)
open scoped Matrix Pointwise

set_option exponentiation.threshold 1100

abbrev Mat12 := Matrix (Fin 12) (Fin 12) (ZMod 2)

abbrev GLm := Mat12ˣ

@[expose] noncomputable def lu (A B : ℕ) : GLm :=
  if h : chkInv A B = true then ⟨toMat A, toMat B, chkInv_sound h, chkInv_sound' h⟩ else 1

theorem val_lu {A B : ℕ} (h : chkInv A B = true) : ((lu A B : GLm) : Mat12) = toMat A := by
  simp only [lu, h, ↓reduceDIte]

theorem val_inv_lu {A B : ℕ} (h : chkInv A B = true) : (((lu A B)⁻¹ : GLm) : Mat12) = toMat B := by
  simp only [lu, h, ↓reduceDIte]
  rfl

@[expose] noncomputable def xh (LET : ℕ) : GLm := lu (letMat LET 0) (letMat LET 1)
@[expose] noncomputable def yh (LET : ℕ) : GLm := lu (letMat LET 2) (letMat LET 3)
@[expose] noncomputable def zh (LET : ℕ) : GLm := lu (letMat LET 5) (letMat LET 6)

abbrev Khat (LET : ℕ) : Subgroup GLm := Subgroup.closure {xh LET, yh LET, zh LET}

abbrev Nhat (LET : ℕ) : Subgroup GLm := Subgroup.closure {xh LET, yh LET}

theorem nhat_le_khat (LET : ℕ) : Nhat LET ≤ Khat LET :=
  Subgroup.closure_mono (Set.insert_subset_insert (Set.singleton_subset_iff.2 (by simp)))

@[expose] def tfree (w n : ℕ) : Prop := ∀ i < n, wLet w i < 4

@[expose] def relN (RT : ℕ → ℕ) {H : Type*} [Group H] (a b : H) : Prop :=
  ∀ r < 12, tfree (wW (RT r)) (wN (RT r)) → rv (jv a b 1 1) (RT r) = 1

@[expose] def relZ (RZT : ℕ → ℕ) {H : Type*} [Group H] (a b t c : H) : Prop :=
  ∀ r < 88, rv (jv a b t c) (RZT r) = 1

theorem rv_eq_wordVal {H : Type*} [Group H] (f : ℕ → H) (A : ℕ) :
    rv f A = wordVal (lvE f) (wW A) (wN A) := by
  rw [wordVal_eq_prod]
  rfl

theorem rv_eq_prod {H : Type*} [Group H] (f : ℕ → H) (A : ℕ) :
    rv f A = ((List.range (wN A)).map fun i => if wLet (wW A) i = 255 then 1 else f (wLet (wW A) i)).prod :=
  rfl

theorem wordVal_congr {M : Type*} [Monoid M] {e e' : ℕ → M} {w : ℕ} :
    ∀ {n : ℕ}, (∀ i < n, e (wLet w i) = e' (wLet w i)) → wordVal e w n = wordVal e' w n
  | 0, _ => rfl
  | n + 1, h => by
    rw [wordVal_succ, wordVal_succ, wordVal_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem rv_congr {H : Type*} [Group H] {f f' : ℕ → H} {A : ℕ}
    (h : ∀ i < wN A, wLet (wW A) i < 4 → f (wLet (wW A) i) = f' (wLet (wW A) i))
    (ht : tfree (wW A) (wN A)) : rv f A = rv f' A := by
  rw [rv_eq_wordVal, rv_eq_wordVal]
  refine wordVal_congr fun i hi => ?_
  have h4 := ht i hi
  have hne : wLet (wW A) i ≠ 255 := by omega
  simp only [lvE, hne, ↓reduceIte]
  exact h i hi h4

theorem wordVal_eq_zero {M : Type*} [MonoidWithZero M] {e : ℕ → M} {w : ℕ} :
    ∀ {n i : ℕ}, i < n → e (wLet w i) = 0 → wordVal e w n = 0
  | 0, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, hi, h0 => by
    rw [wordVal_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [wordVal_eq_zero hi h0, zero_mul]
    · rw [h0, mul_zero]

theorem map_jv {H H' : Type*} [Group H] [Group H'] (φ : H →* H') (a b t c : H) :
    (fun l => φ (jv a b t c l)) = jv (φ a) (φ b) (φ t) (φ c) := by
  funext l
  unfold jv
  split_ifs <;> simp

theorem map_rv {H H' : Type*} [Group H] [Group H'] (φ : H →* H') (f : ℕ → H) (A : ℕ) :
    φ (rv f A) = rv (fun l => φ (f l)) A := by
  rw [rv_eq_wordVal, rv_eq_wordVal, map_wordVal]
  congr 1
  funext l
  unfold lvE
  split_ifs <;> simp

section letters

variable {H : Type*} [Group H] (a b t c : H)

theorem ev0 : lvE (jv a b t c) 0 = a := by simp [lvE, jv]
theorem ev1 : lvE (jv a b t c) 1 = a⁻¹ := by simp [lvE, jv]
theorem ev2 : lvE (jv a b t c) 2 = b := by simp [lvE, jv]
theorem ev3 : lvE (jv a b t c) 3 = b⁻¹ := by simp [lvE, jv]
theorem ev5 : lvE (jv a b t c) 5 = c := by simp [lvE, jv]
theorem ev6 : lvE (jv a b t c) 6 = c⁻¹ := by simp [lvE, jv]

end letters

theorem recAnd_of (g : ℕ → Bool) : ∀ m, (∀ l < m, g l = true) →
    Nat.rec (motive := fun _ => Bool) true (fun l ih => andB (g l) ih) m = true
  | 0, _ => rfl
  | m + 1, h => andB_eq_true.2 ⟨h m (by omega), recAnd_of g m fun l hl => h l (by omega)⟩

theorem rngAll_one_of {a b : ℕ} {f : ℕ → Bool} (h : ∀ i, a ≤ i → i < b → f i = true) :
    rngAll a b 1 f = true := by
  change andB (Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB ((fun i =>
    Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i b))
      (Nat.add a (Nat.add (Nat.shiftLeft 0 6) l))) ih2) 64) true = true
  refine andB_eq_true.2 ⟨recAnd_of (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
    (Nat.blt i b)) (Nat.add a (Nat.add (Nat.shiftLeft 0 6) l))) 64 fun l _ => ?_, rfl⟩
  have e : Nat.add a (Nat.add (Nat.shiftLeft 0 6) l) = a + l := by
    change a + (0 <<< 6 + l) = a + l
    simp
  change Bool.rec (motive := fun _ => Bool) true (f (Nat.add a (Nat.add (Nat.shiftLeft 0 6) l)))
    (Nat.blt (Nat.add a (Nat.add (Nat.shiftLeft 0 6) l)) b) = true
  rw [e]
  cases hc : Nat.blt (a + l) b
  · rfl
  · exact h _ (by omega) (blt_eq_true.1 hc)

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem kSetup_parts {k : KD} (h : kSetup k = true) :
    letMat k.LET 4 = 0 ∧ chkInv (letMat k.LET 0) (letMat k.LET 1) = true ∧
    chkInv (letMat k.LET 2) (letMat k.LET 3) = true ∧ chkInv (letMat k.LET 5) (letMat k.LET 6) = true ∧
    k.LET < 2 ^ 1008 ∧ (∀ r < 12, relAt k.RT k.LET r = true) ∧
    (∀ i < 88, rzAt k.RZT k.LET i = true) := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨h4, h⟩ := andB_eq_true.1 h
  obtain ⟨h01, h⟩ := andB_eq_true.1 h
  obtain ⟨h23, h⟩ := andB_eq_true.1 h
  obtain ⟨h56, h⟩ := andB_eq_true.1 h
  obtain ⟨hL, h⟩ := andB_eq_true.1 h
  obtain ⟨hR, h⟩ := andB_eq_true.1 h
  obtain ⟨hZ, -⟩ := andB_eq_true.1 h
  refine ⟨beq_eq_true.1 h4, h01, h23, h56, ?_,
    fun r hr => CFSG.Certificates.J4KShape.rngAll_spec _ hR r (Nat.zero_le _) hr
      (lt_of_lt_of_le hr (by decide)),
    fun i hi => CFSG.Certificates.J4KShape.rngAll_spec _ hZ i (Nat.zero_le _) hi
      (lt_of_lt_of_le hi (by decide))⟩
  have h' : k.LET < 1 <<< 1008 := blt_eq_true.1 hL
  rw [Nat.one_shiftLeft] at h'
  exact h'

theorem kChains_parts {k : KD} (h : kChains k = true) :
    chainRun k.FT k.EK k.LET k.W0 k.TR1 65535 37 k.neK k.LVK = k.BK ∧
    chainRun k.FT k.EN k.LET k.W0 k.TR1 65535 5 k.neN k.LVN = k.BN ∧ k.BK = 2048 * k.BN := by
  obtain ⟨hK, h⟩ := andB_eq_true.1 h
  obtain ⟨hN, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hB, -⟩ := andB_eq_true.1 h
  exact ⟨beq_eq_true.1 hK, beq_eq_true.1 hN, beq_eq_true.1 hB⟩

theorem kRange_parts {k : KD} (h : kRange k = true) :
    k.INV = invJ ∧ KShape.wordsOK k.WREC = true ∧ KShape.sqOK k.RZT k.INV k.WREC = true ∧
    KShape.commOK k.RZT k.INV k.WREC 0 3 = true ∧ KShape.commOK k.RZT k.INV k.WREC 3 11 = true ∧
    KShape.conjOK k.RZT k.INV k.WREC k.CM = true := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hI, h⟩ := andB_eq_true.1 h
  obtain ⟨hw, h⟩ := andB_eq_true.1 h
  obtain ⟨hs, h⟩ := andB_eq_true.1 h
  obtain ⟨hc, hj⟩ := andB_eq_true.1 h
  exact ⟨beq_eq_true.1 hI, hw, hs,
    rngAll_one_of fun i h1 h2 => CFSG.Certificates.J4KShape.rngAll_spec 1 hc i h1
      (lt_of_lt_of_le h2 (by decide)) (lt_of_lt_of_le h2 (by decide)),
    rngAll_one_of fun i _ h2 => CFSG.Certificates.J4KShape.rngAll_spec 1 hc i (Nat.zero_le _) h2
      (lt_of_lt_of_le h2 (by decide)), hj⟩

theorem letMat_eq_zero {LET c : ℕ} (hL : LET < 2 ^ 1008) (hc : 7 ≤ c) : letMat LET c = 0 := by
  change (LET >>> (144 * c)) &&& _ = 0
  rw [Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt (lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) (by omega))), Nat.zero_and]

theorem letter_cases {LET c : ℕ} (hL : LET < 2 ^ 1008) (h4 : letMat LET 4 = 0)
    (hc : toMat (letMat LET c) ≠ 0) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 5 ∨ c = 6 := by
  have hc7 : c < 7 := by
    by_contra h
    exact hc (by rw [letMat_eq_zero hL (by omega), toMat_zero])
  interval_cases c
  all_goals first | decide | exact absurd (by rw [h4, toMat_zero]) hc

theorem model_letter {LET c : ℕ} (h01 : chkInv (letMat LET 0) (letMat LET 1) = true)
    (h23 : chkInv (letMat LET 2) (letMat LET 3) = true)
    (h56 : chkInv (letMat LET 5) (letMat LET 6) = true)
    (hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 5 ∨ c = 6) :
    toMat (letMat LET c) = ((lvE (jv (xh LET) (yh LET) 1 (zh LET)) c : GLm) : Mat12) := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ev0, xh, val_lu h01]
  · rw [ev1, xh, val_inv_lu h01]
  · rw [ev2, yh, val_lu h23]
  · rw [ev3, yh, val_inv_lu h23]
  · rw [ev5, zh, val_lu h56]
  · rw [ev6, zh, val_inv_lu h56]

theorem model_word_of {LET w n : ℕ} (h01 : chkInv (letMat LET 0) (letMat LET 1) = true)
    (h23 : chkInv (letMat LET 2) (letMat LET 3) = true)
    (h56 : chkInv (letMat LET 5) (letMat LET 6) = true)
    (hg : ∀ i < n, wLet w i = 0 ∨ wLet w i = 1 ∨ wLet w i = 2 ∨ wLet w i = 3 ∨ wLet w i = 5 ∨
      wLet w i = 6) :
    wordVal (fun c => toMat (letMat LET c)) w n =
      ((wordVal (lvE (jv (xh LET) (yh LET) 1 (zh LET))) w n : GLm) : Mat12) := by
  rw [wordVal_congr (e' := fun c => ((lvE (jv (xh LET) (yh LET) 1 (zh LET)) c : GLm) : Mat12))
    (fun i hi => model_letter h01 h23 h56 (hg i hi))]
  exact (map_wordVal (Units.coeHom Mat12) _ w n).symm

theorem model_relN {k : KD} (hS : kSetup k = true) : relN k.RT (xh k.LET) (yh k.LET) := by
  obtain ⟨-, h01, h23, h56, -, hR, -⟩ := kSetup_parts hS
  intro r hr ht
  rw [rv_congr (f' := jv (xh k.LET) (yh k.LET) 1 (zh k.LET)) (fun i _ h4 => by
    unfold jv
    generalize wLet (wW (k.RT r)) i = l at h4 ⊢
    interval_cases l <;> simp) ht, rv_eq_wordVal]
  have hU := model_word_of (LET := k.LET) h01 h23 h56 (w := wW (k.RT r)) (n := wN (k.RT r))
    (fun i hi => by have := ht i hi; omega)
  obtain ⟨-, hM⟩ := andB_eq_true.1 (hR r hr)
  rcases orB_eq_true.1 hM with hM | hM
  · apply Units.ext
    rw [← hU, ← toMat_evalW, beq_eq_true.1 hM, toMat_ident12, Units.val_one]
  · exfalso
    apply (wordVal (lvE (jv (xh k.LET) (yh k.LET) 1 (zh k.LET))) (wW (k.RT r)) (wN (k.RT r))).ne_zero
    rw [← hU, ← toMat_evalW, beq_eq_true.1 hM, toMat_zero]

theorem model_relZ {k : KD} (hS : kSetup k = true) :
    relZ k.RZT (xh k.LET) (yh k.LET) 1 (zh k.LET) := by
  obtain ⟨h4, h01, h23, h56, hL, -, hZ⟩ := kSetup_parts hS
  intro i hi
  obtain ⟨-, hE⟩ := andB_eq_true.1 (hZ i hi)
  have h1 := chkEval_sound hE
  rw [toMat_ident12] at h1
  have hg : ∀ j < wN (k.RZT i), wLet (wW (k.RZT i)) j = 0 ∨ wLet (wW (k.RZT i)) j = 1 ∨
      wLet (wW (k.RZT i)) j = 2 ∨ wLet (wW (k.RZT i)) j = 3 ∨ wLet (wW (k.RZT i)) j = 5 ∨
      wLet (wW (k.RZT i)) j = 6 := fun j hj => letter_cases hL h4 fun h0 =>
    one_ne_zero (h1.trans (wordVal_eq_zero (e := fun c => toMat (letMat k.LET c)) hj h0))
  have hU := model_word_of h01 h23 h56 hg
  rw [rv_eq_wordVal]
  apply Units.ext
  rw [Units.val_one, ← hU, ← h1]

@[expose] noncomputable def pm : CFSG.Certificates.J4Chain.PackedModel Mat12 (Fin 12 → ZMod 2) where
  ev := toMat
  vv := toVec
  A := { act := fun v M => v ᵥ* M, act_one := fun v => Matrix.vecMul_one v,
         act_mul := fun v X Y => (Matrix.vecMul_vecMul v X Y).symm }
  ev_mul a b _ _ := toMat_mul12 a b
  ev_one := toMat_ident12
  vv_vecmul v X _ _ := toVec_vecmul v X
  vv_inj v w hv hw h := eq_of_toVec_eq (lt_of_lt_of_eq hv (by norm_num))
    (lt_of_lt_of_eq hw (by norm_num)) h

instance : Finite GLm := Finite.of_injective _ Units.val_injective

theorem gm_false {GM l : ℕ} (h : gmHas GM l = false) (h' : gmHas GM l = true) : False := by
  rw [h] at h'
  cases h'

theorem bk_le_card_khat {k : KD} (hS : kSetup k = true) (hC : kChains k = true) :
    k.BK ≤ Nat.card (Khat k.LET) := by
  obtain ⟨-, h01, h23, h56, -, -, -⟩ := kSetup_parts hS
  rw [← (kChains_parts hC).1]
  refine CFSG.Certificates.J4Chain.chainRun_le pm _ ⟨fun l hl hg => ?_, fun _ _ _ hg => ?_, fun hg => ?_, fun hg => ?_⟩
  · interval_cases l
    · exact ⟨xh k.LET, by simp, val_lu h01⟩
    · exact (gm_false (by decide +kernel) hg).elim
    · exact ⟨yh k.LET, by simp, val_lu h23⟩
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact ⟨zh k.LET, by simp, val_lu h56⟩
    · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim

theorem bn_le_card_nhat {k : KD} (hS : kSetup k = true) (hC : kChains k = true) :
    k.BN ≤ Nat.card (Nhat k.LET) := by
  obtain ⟨-, h01, h23, -, -, -, -⟩ := kSetup_parts hS
  rw [← (kChains_parts hC).2.1]
  refine CFSG.Certificates.J4Chain.chainRun_le pm _ ⟨fun l hl hg => ?_, fun _ _ _ hg => ?_, fun hg => ?_, fun hg => ?_⟩
  · interval_cases l
    · exact ⟨xh k.LET, by simp, val_lu h01⟩
    · exact (gm_false (by decide +kernel) hg).elim
    · exact ⟨yh k.LET, by simp, val_lu h23⟩
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim

theorem finite_closure3 {H : Type*} [Group H] {a b c : H} {V : Subgroup H} [Finite V]
    [Finite (Subgroup.closure ({a, b} : Set H))] (hc : c ∈ V)
    (hKN : Subgroup.closure ({a, b, c} : Set H) ≤ Subgroup.normalizer V) :
    Finite (Subgroup.closure ({a, b, c} : Set H)) := by
  set N := Subgroup.closure ({a, b} : Set H)
  have hNK : N ≤ Subgroup.closure ({a, b, c} : Set H) :=
    Subgroup.closure_mono (Set.insert_subset_insert (Set.singleton_subset_iff.2 (by simp)))
  have hKVN : Subgroup.closure ({a, b, c} : Set H) ≤ V ⊔ N := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact le_sup_right (a := V) (Subgroup.subset_closure (by simp))
    · exact le_sup_right (a := V) (Subgroup.subset_closure (by simp))
    · exact le_sup_left (b := N) hc
  have hset : ((V ⊔ N : Subgroup H) : Set H) = (V : Set H) * (N : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left V N (hNK.trans hKN)
  have hfin : ((V ⊔ N : Subgroup H) : Set H).Finite := by
    rw [hset]
    exact Set.Finite.mul (Set.toFinite _) (Set.toFinite _)
  exact (hfin.subset hKVN).to_subtype

theorem ktilde_bound {k : KD} (hR : kRange k = true) (hC : kChains k = true)
    (hL : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN)
    {H : Type} [Group H] (a b t c : H) (ht : t * t = 1) (hab : relN k.RT a b)
    (hz : relZ k.RZT a b t c) :
    Finite (Subgroup.closure ({a, b, c} : Set H)) ∧
      Nat.card (Subgroup.closure ({a, b, c} : Set H)) ≤ k.BK := by
  obtain ⟨hI, hw, hs, hc0, hc1, hj⟩ := kRange_parts hR
  obtain ⟨hNf, hNc⟩ := hN H a b hab
  have hI' : ∀ c' < 255, lInv k.INV c' < 255 ∧ jv a b t c (lInv k.INV c') = (jv a b t c c')⁻¹ :=
    fun c' _ => by
      rw [hI]
      exact jv_inv a b t c ht c'
  have := CFSG.Certificates.J4KShape.kshape_sound (jv a b t c) hI' (by simp [jv]) (by simp [jv]) (by simp [jv]) hL hz
    hw hs hc0 hc1 hj
  have e0 : jv a b t c 0 = a := by simp [jv]
  have e2 : jv a b t c 2 = b := by simp [jv]
  have e5 : jv a b t c 5 = c := by simp [jv]
  rw [e0, e2, e5] at this
  obtain ⟨-, -, hVf, -, hcV, -, hKN, hKc⟩ := this
  refine ⟨finite_closure3 hcV hKN, hKc.trans ?_⟩
  rw [(kChains_parts hC).2.2]
  exact Nat.mul_le_mul_left _ hNc

theorem card_nhat {k : KD} (hS : kSetup k = true) (hC : kChains k = true)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN) :
    Nat.card (Nhat k.LET) = k.BN :=
  le_antisymm (hN _ _ _ (model_relN hS)).2 (bn_le_card_nhat hS hC)

theorem card_khat {k : KD} (hS : kSetup k = true) (hR : kRange k = true) (hC : kChains k = true)
    (hL : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN) :
    Nat.card (Khat k.LET) = k.BK :=
  le_antisymm (ktilde_bound hR hC hL hN _ _ 1 _ (one_mul 1) (model_relN hS) (model_relZ hS)).2
    (bk_le_card_khat hS hC)

@[expose] def gen4 {H : Type*} (a b c t : H) (n : ℕ) : H :=
  if n = 0 then a else if n = 1 then b else if n = 2 then c else t

@[expose] def RK (RT RZT : ℕ → ℕ) : Set (FreeGroup ℕ) :=
  {g | g = FreeGroup.of 3 * FreeGroup.of 3} ∪
  ({g | ∃ r < 12, tfree (wW (RT r)) (wN (RT r)) ∧
      g = rv (jv (FreeGroup.of 0) (FreeGroup.of 1) 1 1) (RT r)} ∪
    {g | ∃ r < 88, g = rv (jv (FreeGroup.of 0) (FreeGroup.of 1) (FreeGroup.of 3) (FreeGroup.of 2)) (RZT r)})

theorem lift_rv {H : Type*} [Group H] (g : ℕ → H) (a b t c : FreeGroup ℕ) (A : ℕ) :
    FreeGroup.lift g (rv (jv a b t c) A) =
      rv (jv (FreeGroup.lift g a) (FreeGroup.lift g b) (FreeGroup.lift g t) (FreeGroup.lift g c)) A := by
  rw [map_rv, map_jv]

theorem lift_RK {RT RZT : ℕ → ℕ} {H : Type*} [Group H] (g : ℕ → H) :
    (∀ r ∈ RK RT RZT, FreeGroup.lift g r = 1) ↔
      g 3 * g 3 = 1 ∧ relN RT (g 0) (g 1) ∧ relZ RZT (g 0) (g 1) (g 3) (g 2) := by
  constructor
  · intro h
    refine ⟨?_, fun r hr ht => ?_, fun r hr => ?_⟩
    · have := h (FreeGroup.of 3 * FreeGroup.of 3) (Or.inl rfl)
      rwa [map_mul, FreeGroup.lift_apply_of] at this
    · have := h _ (Or.inr (Or.inl ⟨r, hr, ht, rfl⟩))
      rwa [lift_rv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, map_one] at this
    · have := h _ (Or.inr (Or.inr ⟨r, hr, rfl⟩))
      rwa [lift_rv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of] at this
  · rintro ⟨h0, h1, h2⟩ r (rfl | ⟨r', hr, ht, rfl⟩ | ⟨r', hr, rfl⟩)
    · rw [map_mul, FreeGroup.lift_apply_of]
      exact h0
    · rw [lift_rv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, map_one]
      exact h1 r' hr ht
    · rw [lift_rv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      exact h2 r' hr

theorem image_012 {H : Type*} (g : ℕ → H) : g '' {0, 1, 2} = {g 0, g 1, g 2} := by
  simp only [Set.image_insert_eq, Set.image_singleton]

theorem range_of_gen {K H : Type*} [Group K] [Group H] {s : Set K} (f : Subgroup.closure s →* H)
    {u : Set H} (hu : f '' (((↑) : Subgroup.closure s → K) ⁻¹' s) = u) :
    f.range = Subgroup.closure u := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := s),
    MonoidHom.map_closure, hu]

theorem exists_phiK {k : KD} (hS : kSetup k = true) (hR : kRange k = true) (hC : kChains k = true)
    (hL : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN)
    {G : Type} [Group G] (x y t z : G) (ht : t * t = 1) (hxy : relN k.RT x y)
    (hz : relZ k.RZT x y t z) :
    ∃ φ : Khat k.LET →* G, (∀ g : Khat k.LET, (g : GLm) = xh k.LET → φ g = x) ∧
      (∀ g : Khat k.LET, (g : GLm) = yh k.LET → φ g = y) ∧
      (∀ g : Khat k.LET, (g : GLm) = zh k.LET → φ g = z) ∧
      φ.range = Subgroup.closure {x, y, z} ∧
      (φ.comp (Subgroup.inclusion (nhat_le_khat k.LET))).range = Subgroup.closure {x, y} := by
  classical
  have hLS : gen4 (xh k.LET) (yh k.LET) (zh k.LET) 1 '' {0, 1, 2} = {xh k.LET, yh k.LET, zh k.LET} := by
    rw [image_012]
    simp [gen4]
  obtain ⟨φ, hφ, -, -⟩ := CFSG.Certificates.DceTw.lift_hom (RK k.RT k.RZT) {0, 1, 2} k.BK
    (fun H _ g hg => by
      obtain ⟨h0, h1, h2⟩ := (lift_RK g).1 hg
      rw [image_012]
      exact ktilde_bound hR hC hL hN _ _ _ _ h0 h1 h2)
    (gen4 (xh k.LET) (yh k.LET) (zh k.LET) 1)
    ((lift_RK _).2 ⟨by simp [gen4], by simpa [gen4] using model_relN hS,
      by simpa [gen4] using model_relZ hS⟩)
    (by rw [hLS]; exact bk_le_card_khat hS hC)
    (gen4 x y z t) ((lift_RK _).2 ⟨by simpa [gen4] using ht, by simpa [gen4] using hxy,
      by simpa [gen4] using hz⟩)
  have e : Khat k.LET = Subgroup.closure (gen4 (xh k.LET) (yh k.LET) (zh k.LET) 1 '' {0, 1, 2}) := by
    rw [hLS]
  set φK : Khat k.LET →* G := φ.comp (MulEquiv.subgroupCongr e).toMonoidHom with hφK
  have key : ∀ c ∈ ({0, 1, 2} : Set ℕ), ∀ g : Khat k.LET,
      (g : GLm) = gen4 (xh k.LET) (yh k.LET) (zh k.LET) 1 c → φK g = gen4 x y z t c := by
    intro c hc g hg
    rw [← hφ c hc, hφK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    exact Subtype.ext hg
  have kx : ∀ g : Khat k.LET, (g : GLm) = xh k.LET → φK g = x := fun g hg =>
    key 0 (by simp) g (by simpa [gen4] using hg)
  have ky : ∀ g : Khat k.LET, (g : GLm) = yh k.LET → φK g = y := fun g hg =>
    key 1 (by simp) g (by simpa [gen4] using hg)
  have kz : ∀ g : Khat k.LET, (g : GLm) = zh k.LET → φK g = z := fun g hg =>
    key 2 (by simp) g (by simpa [gen4] using hg)
  refine ⟨φK, kx, ky, kz, range_of_gen φK ?_, range_of_gen _ ?_⟩
  · ext u
    constructor
    · rintro ⟨g, hg, rfl⟩
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg | hg
      · rw [kx g hg]; simp
      · rw [ky g hg]; simp
      · rw [kz g hg]; simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨xh k.LET, Subgroup.subset_closure (by simp)⟩, by simp, kx _ rfl⟩
      · exact ⟨⟨yh k.LET, Subgroup.subset_closure (by simp)⟩, by simp, ky _ rfl⟩
      · exact ⟨⟨zh k.LET, Subgroup.subset_closure (by simp)⟩, by simp, kz _ rfl⟩
  · ext u
    constructor
    · rintro ⟨g, hg, rfl⟩
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · rw [MonoidHom.comp_apply, kx _ hg]; simp
      · rw [MonoidHom.comp_apply, ky _ hg]; simp
    · rintro (rfl | rfl)
      · exact ⟨⟨xh k.LET, Subgroup.subset_closure (by simp)⟩, by simp, kx _ rfl⟩
      · exact ⟨⟨yh k.LET, Subgroup.subset_closure (by simp)⟩, by simp, ky _ rfl⟩

end CFSG.KJ4.Models

end
