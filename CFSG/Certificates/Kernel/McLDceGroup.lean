module

public import CFSG.Certificates.Kernel.McLMat25Sound
public import CFSG.Certificates.Kernel.McL.Dce
public import CFSG.Certificates.Kernel.LceSTabSound
public import Mathlib.GroupTheory.FreeGroup.Basic
import CFSG.Certificates.Kernel.DceTwCore

public section

namespace CFSG.Certificates.McLD

open CFSG.KC CFSG.KC.McL.Mat CFSG.Certificates.LCE

set_option exponentiation.threshold 700

abbrev Mat25 : Type := Matrix (Fin 25) (Fin 25) (ZMod 2)

theorem andB_iff (a b : Bool) : Th.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem brec_true {α : Sort*} (a b : α) : Bool.rec (motive := fun _ => α) a b true = b := rfl

theorem brec_false {α : Sort*} (a b : α) : Bool.rec (motive := fun _ => α) a b false = a := rfl

theorem notB_iff (b : Bool) : McL.Dce.notB b = true ↔ b = false := by
  cases b <;> decide

theorem strictN_eq (v : ℕ) (k : ℕ → ℕ) : Loop.strictN v k = k v := by
  cases v <;> rfl

theorem allRec_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun q acc => Th.andB acc (f q)) n = true ↔
      ∀ q < n, f q = true
  | 0 => ⟨fun _ q hq => absurd hq (Nat.not_lt_zero q), fun _ => rfl⟩
  | n + 1 => by
    change Th.andB (Nat.rec (motive := fun _ => Bool) true (fun q acc => Th.andB acc (f q)) n)
      (f n) = true ↔ _
    rw [andB_iff, allRec_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
      · exact h1 q h
      · exact h2
    · intro h
      exact ⟨fun q hq => h q (by omega), h n (by omega)⟩

theorem isN_iff {TL NL c : ℕ} : McL.Dce.isN TL NL c = true ↔ c < NL ∧ c ≠ TL := by
  unfold McL.Dce.isN
  rw [andB_iff, notB_iff, Nat.blt_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => by simp [h] at h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases h : c.beq TL
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) h2

theorem land255_lt (x : ℕ) : Nat.land x 255 < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

theorem sD_mkSt {D : ℕ} (hD : D < 256) (p : ℕ) : McL.Dce.sD (McL.Dce.mkSt D p) = D := by
  change (D ||| p <<< 8) &&& 255 = D
  apply Nat.eq_of_testBit_eq
  intro i
  have h255 : (255 : ℕ) = 2 ^ 8 - 1 := rfl
  rw [h255, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 8
  · simp [hi]
  · have hD' : D < 2 ^ 8 := hD
    have : D.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hD' (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]

theorem sPi_mkSt {D : ℕ} (hD : D < 256) (p : ℕ) : McL.Dce.sPi (McL.Dce.mkSt D p) = p := by
  change (D ||| p <<< 8) >>> 8 = p
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hD' : D < 2 ^ 8 := hD
  have : D.testBit (8 + i) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hD' (Nat.pow_le_pow_right (by omega) (by omega)))
  simp [this]

theorem sD_bad : McL.Dce.sD McL.Dce.bad = 255 := rfl

theorem sPi_bad : McL.Dce.sPi McL.Dce.bad = 0 := rfl

theorem sD_lt (S : ℕ) : McL.Dce.sD S < 256 := land255_lt S

theorem let25_lt (LT c : ℕ) : McL.Dce.let25 LT c < 2 ^ 625 := land_m625_lt _

theorem mat_lt (HB : ℕ → ℕ) (h : ℕ) : McL.Dce.mat HB h < 2 ^ 625 := land_m625_lt _

theorem toMat_zero : toMat 0 = 0 := by
  ext i j
  simp [toMat]

theorem mul25_zero_left (B : ℕ) : mul25 0 B = 0 :=
  eq_of_toMat_eq (mul25_lt _ _) (Nat.two_pow_pos _) (by rw [toMat_mul25, toMat_zero, zero_mul])

theorem ident_ne_zero : ident ≠ 0 := by
  intro h
  have e := ident_testBit 0 (by omega) 0 (by omega)
  rw [h, Nat.zero_testBit] at e
  exact absurd e (by decide)

@[expose] noncomputable def wc (LT : ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc c => mul25 acc (McL.Dce.let25 LT c)) ident

theorem foldl_spec (LT : ℕ) : ∀ (w : List ℕ) (acc : ℕ), acc < 2 ^ 625 →
    w.foldl (fun acc c => mul25 acc (McL.Dce.let25 LT c)) acc < 2 ^ 625 ∧
      toMat (w.foldl (fun acc c => mul25 acc (McL.Dce.let25 LT c)) acc) =
        toMat acc * (w.map fun c => toMat (McL.Dce.let25 LT c)).prod
  | [], acc, h => ⟨h, by simp⟩
  | c :: w, acc, _ => by
    obtain ⟨h1, h2⟩ := foldl_spec LT w (mul25 acc (McL.Dce.let25 LT c)) (mul25_lt _ _)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, toMat_mul25, List.map_cons, List.prod_cons, mul_assoc]

theorem wc_lt (LT : ℕ) (w : List ℕ) : wc LT w < 2 ^ 625 := (foldl_spec LT w ident ident_lt).1

theorem toMat_wc (LT : ℕ) (w : List ℕ) :
    toMat (wc LT w) = (w.map fun c => toMat (McL.Dce.let25 LT c)).prod := by
  rw [wc, (foldl_spec LT w ident ident_lt).2, toMat_ident, one_mul]

theorem wc_append (LT : ℕ) (w w' : List ℕ) : wc LT (w ++ w') = mul25 (wc LT w) (wc LT w') :=
  eq_of_toMat_eq (wc_lt _ _) (mul25_lt _ _)
    (by rw [toMat_mul25, toMat_wc, toMat_wc, toMat_wc, List.map_append, List.prod_append])

theorem lettersOK_spec {LT LI TL NL : ℕ} (h : McL.Dce.lettersOK LT LI TL NL = true) :
    NL < 255 ∧ TL < NL ∧ ∀ c < NL, McL.Dce.byte LI c = c ∧
      (c ≠ TL → mul25 (McL.Dce.let25 LT c) (McL.Dce.let25 LT c) = ident) := by
  unfold McL.Dce.lettersOK at h
  rw [andB_iff, andB_iff, Nat.blt_eq, Nat.blt_eq, allRec_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun c hc => ?_⟩
  have e := h3 c hc
  rw [andB_iff, Nat.beq_eq] at e
  refine ⟨e.1, fun hcT => ?_⟩
  have hN : McL.Dce.isN TL NL c = true := isN_iff.2 ⟨hc, hcT⟩
  rw [hN] at e
  exact Nat.eq_of_beq_eq_true e.2

@[expose] noncomputable def nrP (LT TL NL Wd k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) ident
    (fun i acc => (fun g => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (mul25 acc (McL.Dce.let25 LT g)) (McL.Dce.isN TL NL g))
      (Nat.shiftRight (McL.Dce.byte Wd i) (nat_lit 1))) k

theorem nrP_zero (LT TL NL Wd : ℕ) : nrP LT TL NL Wd 0 = ident := rfl

theorem nrP_succ (LT TL NL Wd k : ℕ) : nrP LT TL NL Wd (k + 1) =
    Bool.rec (motive := fun _ => Nat) 0
      (mul25 (nrP LT TL NL Wd k) (McL.Dce.let25 LT (Nat.shiftRight (McL.Dce.byte Wd k) 1)))
      (McL.Dce.isN TL NL (Nat.shiftRight (McL.Dce.byte Wd k) 1)) := rfl

theorem nrP_spec (LT TL NL Wd : ℕ) : ∀ k, nrP LT TL NL Wd k = 0 ∨
    ((∀ i < k, McL.Dce.isN TL NL (Nat.shiftRight (McL.Dce.byte Wd i) 1) = true) ∧
      nrP LT TL NL Wd k < 2 ^ 625 ∧
      toMat (nrP LT TL NL Wd k) = ((List.range k).map fun i =>
        toMat (McL.Dce.let25 LT (Nat.shiftRight (McL.Dce.byte Wd i) 1))).prod)
  | 0 => by
    rw [nrP_zero]
    exact Or.inr ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ident_lt, by
      rw [toMat_ident, List.range_zero, List.map_nil, List.prod_nil]⟩
  | k + 1 => by
    rw [nrP_succ]
    rcases nrP_spec LT TL NL Wd k with h | ⟨h1, _, h3⟩
    · left
      rw [h, mul25_zero_left]
      cases McL.Dce.isN TL NL (Nat.shiftRight (McL.Dce.byte Wd k) 1) <;> rfl
    · cases hk : McL.Dce.isN TL NL (Nat.shiftRight (McL.Dce.byte Wd k) 1)
      · exact Or.inl rfl
      · refine Or.inr ⟨fun i hi => ?_, mul25_lt (nrP LT TL NL Wd k)
          (McL.Dce.let25 LT (Nat.shiftRight (McL.Dce.byte Wd k) 1)), ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
          · exact h1 i h
          · exact hk
        · rw [toMat_mul25, h3, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
            List.prod_singleton]

theorem nRels_prod {LT TL NL nRN : ℕ} {NRN : ℕ → ℕ}
    (h : McL.Dce.nRelsHold LT NRN TL NL nRN = true) : ∀ r < nRN,
    (∀ i < LceS.wLen (NRN r),
      McL.Dce.isN TL NL (Nat.shiftRight (McL.Dce.byte (LceS.wWord (NRN r)) i) 1) = true) ∧
      ((List.range (LceS.wLen (NRN r))).map fun i =>
        toMat (McL.Dce.let25 LT (Nat.shiftRight (McL.Dce.byte (LceS.wWord (NRN r)) i) 1))).prod
        = 1 := by
  intro r hr
  unfold McL.Dce.nRelsHold at h
  rw [allRec_iff] at h
  have e := h r hr
  change Nat.beq (nrP LT TL NL (LceS.wWord (NRN r)) (LceS.wLen (NRN r))) ident = true at e
  rw [Nat.beq_eq] at e
  rcases nrP_spec LT TL NL (LceS.wWord (NRN r)) (LceS.wLen (NRN r)) with h0 | ⟨h1, _, h3⟩
  · exact absurd (e.symm.trans h0) ident_ne_zero
  · exact ⟨h1, by rw [← h3, e, toMat_ident]⟩

@[expose] noncomputable def Lf (LT TL NL c : ℕ) : Mat25ˣ :=
  @dite _ (McL.Dce.isN TL NL c = true ∧
      mul25 (McL.Dce.let25 LT c) (McL.Dce.let25 LT c) = ident) (Classical.propDecidable _)
    (fun h => ⟨toMat (McL.Dce.let25 LT c), toMat (McL.Dce.let25 LT c),
      by rw [← toMat_mul25, h.2, toMat_ident], by rw [← toMat_mul25, h.2, toMat_ident]⟩)
    (fun _ => 1)

@[expose] noncomputable def Mg (LT TL NL : ℕ) : Subgroup Mat25ˣ :=
  Subgroup.closure (Lf LT TL NL '' {i | i < 3})

variable {LT LI TL NL : ℕ}

theorem Lf_sq (c : ℕ) : Lf LT TL NL c * Lf LT TL NL c = 1 := by
  unfold Lf
  split_ifs with h
  · ext1
    change toMat _ * toMat _ = 1
    rw [← toMat_mul25, h.2, toMat_ident]
  · exact one_mul 1

theorem Lf_inv (c : ℕ) : (Lf LT TL NL c)⁻¹ = Lf LT TL NL c :=
  inv_eq_of_mul_eq_one_right (Lf_sq c)

theorem Lf_of_not {c : ℕ} (hc : ¬(c < NL ∧ c ≠ TL)) : Lf LT TL NL c = 1 := by
  unfold Lf
  rw [dite_eq_right]
  exact fun h => hc (isN_iff.1 h.1)

theorem Lf_val (hlet : McL.Dce.lettersOK LT LI TL NL = true) {c : ℕ} (hc : c < NL ∧ c ≠ TL) :
    ((Lf LT TL NL c : Mat25ˣ) : Mat25) = toMat (McL.Dce.let25 LT c) := by
  unfold Lf
  rw [dite_eq_left ⟨isN_iff.2 hc, ((lettersOK_spec hlet).2.2 c hc.1).2 hc.2⟩]

theorem val_prod_Lf (hlet : McL.Dce.lettersOK LT LI TL NL = true) {w : List ℕ}
    (hw : ∀ c ∈ w, c < NL ∧ c ≠ TL) :
    (((w.map (Lf LT TL NL)).prod : Mat25ˣ) : Mat25) = toMat (wc LT w) := by
  rw [toMat_wc, ← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact Lf_val hlet (hw c hc)

theorem Lf_mem {c : ℕ} (hc : c < 3) : Lf LT TL NL c ∈ Mg LT TL NL :=
  Subgroup.subset_closure ⟨c, hc, rfl⟩

theorem prod_Lf_mem {w : List ℕ} (hw : ∀ c ∈ w, c < 3) : (w.map (Lf LT TL NL)).prod ∈ Mg LT TL NL := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg
  exact Lf_mem (hw c hc)

theorem Mg_word {y : Mat25ˣ} (hy : y ∈ Mg LT TL NL) :
    ∃ w : List ℕ, (∀ c ∈ w, c < 3) ∧ (w.map (Lf LT TL NL)).prod = y := by
  have gen1 : ∀ c, c < 3 → ∃ w : List ℕ, (∀ c ∈ w, c < 3) ∧
      (w.map (Lf LT TL NL)).prod = Lf LT TL NL c := fun c hc => by
    refine ⟨[c], by simpa using hc, ?_⟩
    rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [Mg] at hy
  induction hy using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨c, hc, rfl⟩ := hg
    exact gen1 c hc
  | inv_mem g hg =>
    obtain ⟨c, hc, rfl⟩ := hg
    rw [Lf_inv]
    exact gen1 c hc
  | one => exact ⟨[], by simp, rfl⟩
  | mul g g' _ _ ih ih' =>
    obtain ⟨w, hw, e⟩ := ih
    obtain ⟨w', hw', e'⟩ := ih'
    refine ⟨w ++ w', fun c hc => ?_, by rw [List.map_append, List.prod_append, e, e']⟩
    rcases List.mem_append.1 hc with h | h
    · exact hw c h
    · exact hw' c h

theorem bval_map {H K : Type*} [Group H] [Group K] (f : H →* K) (z : ℕ → H) (W n : ℕ) :
    f (bval z W n) = bval (fun i => f (z i)) W n := by
  unfold bval
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, letV]
  split_ifs <;> simp

theorem nRels_model {nRN : ℕ} {NRN : ℕ → ℕ} (hNL : NL < 128)
    (hlet : McL.Dce.lettersOK LT LI TL NL = true) (hnrel : McL.Dce.nRelsHold LT NRN TL NL nRN = true) :
    ∀ r < nRN, bval (Lf LT TL NL) (LceS.wWord (NRN r)) (LceS.wLen (NRN r)) = 1 := by
  intro r hr
  obtain ⟨h1, h2⟩ := nRels_prod hnrel r hr
  ext1
  rw [Units.val_one, ← h2, bval, ← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hN := isN_iff.1 (h1 i (List.mem_range.1 hi))
  change ((letV (Lf LT TL NL) (McL.Dce.byte (LceS.wWord (NRN r)) i) : Mat25ˣ) : Mat25) =
    toMat (McL.Dce.let25 LT (Nat.shiftRight (McL.Dce.byte (LceS.wWord (NRN r)) i) 1))
  generalize McL.Dce.byte (LceS.wWord (NRN r)) i = b at hN ⊢
  have hb : Nat.shiftRight b 1 = b / 2 := by
    change b >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  rw [hb] at hN ⊢
  rw [← Lf_val hlet hN]
  have h255 : b ≠ 255 := by
    rintro rfl
    omega
  unfold letV
  rw [ite_eq_right h255]
  split_ifs
  · rfl
  · rw [Lf_inv]

theorem card_Mg {nRN NORD : ℕ} {NRN : ℕ → ℕ} (hNL : NL = 4)
    (hlet : McL.Dce.lettersOK LT LI TL NL = true) (hnrel : McL.Dce.nRelsHold LT NRN TL NL nRN = true)
    (hN : ∀ (H : Type) [Group H] (z : ℕ → H),
      (∀ r < nRN, bval z (LceS.wWord (NRN r)) (LceS.wLen (NRN r)) = 1) →
        Nat.card (Subgroup.closure (z '' {i | i < 3})) ≠ 0 ∧
          Nat.card (Subgroup.closure (z '' {i | i < 3})) ≤ NORD) :
    Nat.card (Mg LT TL NL) ≠ 0 ∧ Nat.card (Mg LT TL NL) ≤ NORD :=
  hN Mat25ˣ (Lf LT TL NL) (nRels_model (by omega) hlet hnrel)

@[expose] noncomputable def Nsub {G : Type*} [Group G] (gen : ℕ → G) : Subgroup G :=
  Subgroup.closure (gen '' {i | i < 3})

theorem lift_bval {K : Type*} [Group K] (z : ℕ → K) (W n : ℕ) :
    FreeGroup.lift z (bval FreeGroup.of W n) = bval z W n := by
  rw [bval_map]
  simp only [FreeGroup.lift_apply_of]

@[expose] noncomputable def nRelSet (NRN : ℕ → ℕ) (nRN : ℕ) : Set (FreeGroup ℕ) :=
  {r | ∃ k < nRN, r = bval FreeGroup.of (LceS.wWord (NRN k)) (LceS.wLen (NRN k))}

theorem nRelSet_iff {NRN : ℕ → ℕ} {nRN : ℕ} {K : Type*} [Group K] (z : ℕ → K) :
    (∀ r ∈ nRelSet NRN nRN, FreeGroup.lift z r = 1) ↔
      ∀ k < nRN, bval z (LceS.wWord (NRN k)) (LceS.wLen (NRN k)) = 1 := by
  constructor
  · intro h k hk
    rw [← lift_bval]
    exact h _ ⟨k, hk, rfl⟩
  · rintro h _ ⟨k, hk, rfl⟩
    rw [lift_bval]
    exact h k hk

theorem model_hom {G : Type*} [Group G] (gen : ℕ → G) {nRN NORD : ℕ} {NRN : ℕ → ℕ}
    (hNL : NL = 4)
    (hlet : McL.Dce.lettersOK LT LI TL NL = true) (hnrel : McL.Dce.nRelsHold LT NRN TL NL nRN = true)
    (hNRN : ∀ r < nRN, bval gen (LceS.wWord (NRN r)) (LceS.wLen (NRN r)) = 1)
    (hN : ∀ (H : Type) [Group H] (z : ℕ → H),
      (∀ r < nRN, bval z (LceS.wWord (NRN r)) (LceS.wLen (NRN r)) = 1) →
        Nat.card (Subgroup.closure (z '' {i | i < 3})) ≠ 0 ∧
          Nat.card (Subgroup.closure (z '' {i | i < 3})) ≤ NORD)
    (hM : NORD ≤ Nat.card (Mg LT TL NL)) :
    ∃ φ : Mg LT TL NL →* G, (∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c) ∧
      (∀ m, φ m ∈ Nsub gen) ∧ ∀ n ∈ Nsub gen, ∃ m, φ m = n :=
  DceTw.lift_hom (nRelSet NRN nRN) {i | i < 3} NORD
    (fun H _i y hy => by
      obtain ⟨h1, h2⟩ := hN H y ((nRelSet_iff y).1 hy)
      exact ⟨Nat.finite_of_card_ne_zero h1, h2⟩)
    (Lf LT TL NL) ((nRelSet_iff _).2 (nRels_model (by omega) hlet hnrel)) hM gen
    ((nRelSet_iff gen).2 hNRN)

@[expose] def InM (LT TL NL A : ℕ) : Prop := ∃ y ∈ Mg LT TL NL, ((y : Mat25ˣ) : Mat25) = toMat A

theorem InM_congr {A B : ℕ} (h : toMat A = toMat B) : InM LT TL NL A ↔ InM LT TL NL B :=
  ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e.trans h⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e.trans h.symm⟩⟩

theorem InM_ident : InM LT TL NL ident :=
  ⟨1, Subgroup.one_mem _, by rw [toMat_ident, Units.val_one]⟩

theorem InM_mul {A B : ℕ} (hA : InM LT TL NL A) (hB : InM LT TL NL B) :
    InM LT TL NL (mul25 A B) := by
  obtain ⟨u, hu, eu⟩ := hA
  obtain ⟨v, hv, ev⟩ := hB
  exact ⟨u * v, (Mg LT TL NL).mul_mem hu hv, by rw [Units.val_mul, eu, ev, toMat_mul25]⟩

theorem val_inv_of {u : Mat25ˣ} {B : ℕ} (h : (u : Mat25) * toMat B = 1) :
    ((u⁻¹ : Mat25ˣ) : Mat25) = toMat B := by
  rw [← mul_one ((u⁻¹ : Mat25ˣ) : Mat25), ← h, ← mul_assoc, Units.inv_mul, one_mul]

theorem val_inv_of' {v : Mat25ˣ} {A : ℕ} (h : toMat A * (v : Mat25) = 1) :
    ((v⁻¹ : Mat25ˣ) : Mat25) = toMat A := by
  rw [← one_mul ((v⁻¹ : Mat25ˣ) : Mat25), ← h, mul_assoc, Units.mul_inv, mul_one]

theorem InM_inv {A B : ℕ} (hA : InM LT TL NL A) (hAB : mul25 A B = ident) : InM LT TL NL B := by
  obtain ⟨u, hu, eu⟩ := hA
  exact ⟨u⁻¹, (Mg LT TL NL).inv_mem hu,
    val_inv_of (by rw [eu, ← toMat_mul25, hAB, toMat_ident])⟩

theorem InM_invL {A B : ℕ} (hB : InM LT TL NL B) (hAB : mul25 A B = ident) : InM LT TL NL A := by
  obtain ⟨v, hv, ev⟩ := hB
  exact ⟨v⁻¹, (Mg LT TL NL).inv_mem hv,
    val_inv_of' (by rw [ev, ← toMat_mul25, hAB, toMat_ident])⟩

theorem lt3 (hTL : TL = 3) (hNL : NL = 4) {c : ℕ} (hc : c < 3) : c < NL ∧ c ≠ TL := by
  omega

theorem InM_letter (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {c : ℕ} (hc : c < 3) : InM LT TL NL (McL.Dce.let25 LT c) :=
  ⟨_, Lf_mem hc, Lf_val hlet (lt3 hTL hNL hc)⟩

theorem InM_wc (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {w : List ℕ} (hw : ∀ c ∈ w, c < 3) : InM LT TL NL (wc LT w) :=
  ⟨_, prod_Lf_mem hw, val_prod_Lf hlet fun c hc => lt3 hTL hNL (hw c hc)⟩

theorem hdrOK_spec {HB : ℕ → ℕ} {h d : ℕ} (hh : McL.Dce.hdrOK HB LT TL NL h d = true) :
    McL.Dce.mat HB h = ident ∨
      (∃ a, McL.Dce.isN TL NL a = true ∧ McL.Dce.mat HB h = McL.Dce.let25 LT a) ∨
      (∃ a b, a < h ∧ b < h ∧ McL.Dce.mat HB h = mul25 (McL.Dce.mat HB a) (McL.Dce.mat HB b)) ∨
      (∃ a, a < h ∧ mul25 (McL.Dce.mat HB h) (McL.Dce.mat HB a) = ident) := by
  unfold McL.Dce.hdrOK at hh
  beta_reduce at hh
  generalize McL.Dce.mat HB h = H at hh ⊢
  generalize Nat.land d 7 = k at hh
  generalize McL.Dce.bits d 3 20 = a at hh
  generalize McL.Dce.bits d 23 20 = b at hh
  revert hh
  cases Nat.beq k 0
  · cases Nat.beq k 1
    · cases Nat.beq k 2
      · cases Nat.beq k 3
        · intro hh
          exact absurd hh Bool.false_ne_true
        · intro hh
          change Th.andB (Nat.blt a h) (Nat.beq (mul25 H (McL.Dce.mat HB a)) ident) = true at hh
          rw [andB_iff, Nat.blt_eq, Nat.beq_eq] at hh
          exact Or.inr (Or.inr (Or.inr ⟨a, hh.1, hh.2⟩))
      · intro hh
        change Th.andB (Nat.blt a h) (Th.andB (Nat.blt b h)
          (Nat.beq H (mul25 (McL.Dce.mat HB a) (McL.Dce.mat HB b)))) = true at hh
        rw [andB_iff, andB_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq] at hh
        exact Or.inr (Or.inr (Or.inl ⟨a, b, hh.1, hh.2.1, hh.2.2⟩))
    · intro hh
      change Th.andB (McL.Dce.isN TL NL a) (Nat.beq H (McL.Dce.let25 LT a)) = true at hh
      rw [andB_iff, Nat.beq_eq] at hh
      exact Or.inr (Or.inl ⟨a, hh.1, hh.2⟩)
  · intro hh
    change Nat.beq H ident = true at hh
    exact Or.inl (Nat.eq_of_beq_eq_true hh)

@[expose] def CntInv (ok : ℕ → ℕ → Bool) (S : ℕ) : Prop := ∀ h, h + 1 < S → ∃ d, ok h d = true

@[expose] noncomputable def cntInner (ok : ℕ → ℕ → Bool) (wd n J S : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih2 J S => Loop.strictN (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.succ S)
        (Th.andB (Nat.blt (nat_lit 0) S) (ok (Nat.sub S (nat_lit 1)) (McL.Dce.bits J (nat_lit 0) wd))))
      (ih2 (Nat.shiftRight J wd))) n J S

@[expose] noncomputable def cntRun (ok : ℕ → ℕ → Bool) (wd : ℕ) (cnt str : ℕ → ℕ) (Cs : List ℕ) :
    ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => Loop.strictN (cntInner ok wd (cnt C) (str C) S) ih) Cs

theorem cntInner_inv (ok : ℕ → ℕ → Bool) (wd : ℕ) : ∀ n J S, CntInv ok S →
    CntInv ok (cntInner ok wd n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change CntInv ok (Loop.strictN (Bool.rec (motive := fun _ => ℕ) 0 (Nat.succ S)
        (Th.andB (Nat.blt 0 S) (ok (Nat.sub S 1) (McL.Dce.bits J 0 wd))))
      (cntInner ok wd n (Nat.shiftRight J wd)))
    rw [strictN_eq]
    apply cntInner_inv ok wd n
    cases hc : Th.andB (Nat.blt 0 S) (ok (Nat.sub S 1) (McL.Dce.bits J 0 wd))
    · intro k hk
      exact absurd hk (Nat.not_lt_zero _)
    · rw [andB_iff, Nat.blt_eq] at hc
      intro k hk
      change k + 1 < S + 1 at hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact h k hk
      · refine ⟨McL.Dce.bits J 0 wd, ?_⟩
        have e : k = Nat.sub S 1 := by
          change k = S - 1
          omega
        rw [e]
        exact hc.2

theorem cntRun_inv (ok : ℕ → ℕ → Bool) (wd : ℕ) (cnt str : ℕ → ℕ) : ∀ (Cs : List ℕ) (S : ℕ),
    CntInv ok S → CntInv ok (cntRun ok wd cnt str Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change CntInv ok (Loop.strictN (cntInner ok wd (cnt C) (str C) S) (cntRun ok wd cnt str Cs))
    rw [strictN_eq]
    exact cntRun_inv ok wd cnt str Cs _ (cntInner_inv ok wd _ _ _ h)

theorem runHdr_eq (HB : ℕ → ℕ) (Cs : List ℕ) (S : ℕ) :
    McL.Dce.runHdr HB LT TL NL Cs S = cntRun (McL.Dce.hdrOK HB LT TL NL) 43
      (fun C => Nat.land C 255) (fun C => Nat.shiftRight C 8) Cs S := rfl

theorem runT_eq (HB TB OB RR : ℕ → ℕ) (NR nH nT I0 : ℕ) (Cs : List ℕ) (S : ℕ) :
    McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Cs S =
      cntRun (McL.Dce.tOK HB TB OB RR LT TL NL NR nH nT I0) 59
        (fun C => Nat.land C 65535) (fun C => Nat.shiftRight C 16) Cs S := rfl

theorem runT_ok {HB TB OB RR : ℕ → ℕ} {NR nH nT I0 : ℕ} {Ct : List ℕ}
    (h : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true) :
    ∀ e < nT, ∃ d, McL.Dce.tOK HB TB OB RR LT TL NL NR nH nT I0 e d = true := by
  have hi := cntRun_inv (McL.Dce.tOK HB TB OB RR LT TL NL NR nH nT I0) 59
    (fun C => Nat.land C 65535) (fun C => Nat.shiftRight C 16) Ct 1
    (fun k hk => absurd hk (by omega))
  rw [← runT_eq, Nat.eq_of_beq_eq_true h] at hi
  exact fun e he => hi e (by omega)

theorem hdr_mem (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {HB : ℕ → ℕ} {Ch : List ℕ} {nH : ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true) :
    ∀ h < nH, InM LT TL NL (McL.Dce.mat HB h) := by
  have hi := cntRun_inv (McL.Dce.hdrOK HB LT TL NL) 43
    (fun C => Nat.land C 255) (fun C => Nat.shiftRight C 8) Ch 1 (fun k hk => absurd hk (by omega))
  rw [← runHdr_eq, Nat.eq_of_beq_eq_true hhdr] at hi
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh
    obtain ⟨d, hd⟩ := hi h (by omega)
    rcases hdrOK_spec hd with e | ⟨a, ha, e⟩ | ⟨a, b, ha, hb, e⟩ | ⟨a, ha, e⟩
    · rw [e]
      exact InM_ident
    · rw [e]
      have ha' := isN_iff.1 ha
      exact InM_letter hTL hNL hlet (by omega)
    · rw [e]
      exact InM_mul (ih a ha (by omega)) (ih b hb (by omega))
    · exact InM_invL (ih a ha (by omega)) e

section Rc

variable {G : Type*} [Group G] (φ : Mg LT TL NL →* G)

noncomputable def rc (A : ℕ) : G :=
  @dite _ (InM LT TL NL A) (Classical.propDecidable _)
    (fun h => φ ⟨Classical.choose h, (Classical.choose_spec h).1⟩) (fun _ => 1)

theorem rc_eq {A : ℕ} (y : Mg LT TL NL) (hy : ((y : Mat25ˣ) : Mat25) = toMat A) :
    rc φ A = φ y := by
  have h : InM LT TL NL A := ⟨y, y.2, hy⟩
  unfold rc
  rw [dite_eq_left h]
  congr 1
  apply Subtype.ext
  apply Units.ext
  exact (Classical.choose_spec h).2.trans hy.symm

theorem rc_congr {A B : ℕ} (h : toMat A = toMat B) : rc φ A = rc φ B := by
  by_cases hA : InM LT TL NL A
  · obtain ⟨y, hy, e⟩ := hA
    rw [rc_eq φ ⟨y, hy⟩ e, rc_eq φ ⟨y, hy⟩ (e.trans h)]
  · have hB : ¬InM LT TL NL B := fun hB => hA ((InM_congr h).2 hB)
    unfold rc
    rw [dite_eq_right hA, dite_eq_right hB]

theorem rc_ident : rc φ ident = 1 := by
  rw [rc_eq φ 1 (by rw [toMat_ident]; rfl), map_one]

theorem rc_mul {A B : ℕ} (hA : InM LT TL NL A) (hB : InM LT TL NL B) :
    rc φ (mul25 A B) = rc φ A * rc φ B := by
  obtain ⟨u, hu, eu⟩ := hA
  obtain ⟨v, hv, ev⟩ := hB
  rw [rc_eq φ (⟨u, hu⟩ * ⟨v, hv⟩) (by rw [toMat_mul25, ← eu, ← ev]; rfl), map_mul,
    rc_eq φ ⟨u, hu⟩ eu, rc_eq φ ⟨v, hv⟩ ev]

theorem rc_inv {A B : ℕ} (hA : InM LT TL NL A) (hAB : mul25 A B = ident) :
    rc φ B = (rc φ A)⁻¹ := by
  obtain ⟨u, hu, eu⟩ := hA
  rw [rc_eq φ (⟨u, hu⟩⁻¹) (val_inv_of (by rw [eu, ← toMat_mul25, hAB, toMat_ident])), map_inv,
    rc_eq φ ⟨u, hu⟩ eu]

theorem rc_invL {A B : ℕ} (hB : InM LT TL NL B) (hAB : mul25 A B = ident) :
    rc φ A = (rc φ B)⁻¹ := by
  obtain ⟨v, hv, ev⟩ := hB
  rw [rc_eq φ (⟨v, hv⟩⁻¹) (val_inv_of' (by rw [ev, ← toMat_mul25, hAB, toMat_ident])), map_inv,
    rc_eq φ ⟨v, hv⟩ ev]

theorem rc_mem {gen : ℕ → G} (hφN : ∀ m, φ m ∈ Nsub gen) (A : ℕ) : rc φ A ∈ Nsub gen := by
  unfold rc
  split_ifs
  · exact hφN _
  · exact (Nsub gen).one_mem

section Letters

variable {gen : ℕ → G} (hφ : ∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c)
  (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
include hφ hTL hNL hlet

theorem rc_letter {c : ℕ} (hc : c < 3) : rc φ (McL.Dce.let25 LT c) = gen c := by
  rw [rc_eq φ ⟨_, Lf_mem hc⟩ (Lf_val hlet (lt3 hTL hNL hc))]
  exact hφ c hc

theorem rc_wc : ∀ {w : List ℕ}, (∀ c ∈ w, c < 3) → rc φ (wc LT w) = (w.map gen).prod
  | [], _ => rc_ident φ
  | c :: w, hw => by
    have hc : c < 3 := hw c List.mem_cons_self
    have hw' : ∀ d ∈ w, d < 3 := fun d hd => hw d (List.mem_cons_of_mem c hd)
    have e : toMat (wc LT (c :: w)) = toMat (mul25 (McL.Dce.let25 LT c) (wc LT w)) := by
      rw [toMat_mul25, toMat_wc, toMat_wc, List.map_cons, List.prod_cons]
    rw [rc_congr φ e, rc_mul φ (InM_letter hTL hNL hlet hc) (InM_wc hTL hNL hlet hw'),
      rc_letter φ hφ hTL hNL hlet hc, rc_wc hw', List.map_cons, List.prod_cons]

theorem gen_sq {c : ℕ} (hc : c < 3) : gen c * gen c = 1 := by
  rw [← rc_letter φ hφ hTL hNL hlet hc, ← rc_mul φ (InM_letter hTL hNL hlet hc)
    (InM_letter hTL hNL hlet hc), ((lettersOK_spec hlet).2.2 c (by omega)).2 (by omega), rc_ident]

theorem faithful {w : List ℕ} (hw : ∀ c ∈ w, c < 3) (h : wc LT w = ident) :
    (w.map gen).prod = 1 := by
  rw [← rc_wc φ hφ hTL hNL hlet hw, h, rc_ident]

omit hφ in
theorem rc_surj (hNφ : ∀ n ∈ Nsub gen, ∃ m, φ m = n) {g : G} (hg : g ∈ Nsub gen) :
    ∃ w : List ℕ, (∀ c ∈ w, c < 3) ∧ InM LT TL NL (wc LT w) ∧ rc φ (wc LT w) = g := by
  obtain ⟨m, rfl⟩ := hNφ g hg
  obtain ⟨w, hw, e⟩ := Mg_word m.2
  refine ⟨w, hw, InM_wc hTL hNL hlet hw, ?_⟩
  rw [rc_eq φ m (by rw [← e]; exact val_prod_Lf hlet fun c hc => lt3 hTL hNL (hw c hc))]

end Letters

end Rc

@[expose] noncomputable def actV (p : Fin 25 → ZMod 2) (a : Mat25ˣ) : Fin 25 → ZMod 2 :=
  Matrix.vecMul p (a : Mat25)

theorem actV_one (p : Fin 25 → ZMod 2) : actV p 1 = p := by
  rw [actV, Units.val_one, Matrix.vecMul_one]

theorem actV_mul (p : Fin 25 → ZMod 2) (a b : Mat25ˣ) : actV (actV p a) b = actV p (a * b) := by
  rw [actV, actV, actV, Units.val_mul, Matrix.vecMul_vecMul]

theorem toVec_vecmul_actV {x A : ℕ} {y : Mat25ˣ} (hy : (y : Mat25) = toMat A) :
    toVec (vecmul x A) = actV (toVec x) y := by
  rw [toVec_vecmul, actV, hy]

end CFSG.Certificates.McLD

end
