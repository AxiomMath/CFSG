module

public import CFSG.Certificates.Kernel.J4.ModelsSound
public import Certificates.Data.Kernel.J4Fix
import Mathlib.Tactic.IntervalCases
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.KJ4.TStruct

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models CFSG.KC.Loop
open CFSG.Certificates.DceWord (lvE wv)
open CFSG.Certificates.J4Words (jv invJ jv_inv)
open CFSG.Certificates.J4KShape (rv)
open CFSG.Certificates.J4Chain (RightAct card_mul_le_of_orbit)
open scoped Matrix

set_option exponentiation.threshold 4096

abbrev Vec := Fin 12 → ZMod 2

@[expose] noncomputable def e11 : Vec := Pi.single 11 1

theorem e11_apply (i : Fin 12) : e11 i = if i = 11 then 1 else 0 := by
  simp [e11, Pi.single_apply]

theorem mulVec_e11 (M : Mat12) (i : Fin 12) : (M *ᵥ e11) i = M i 11 := by
  simp [e11, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem e11_vecMul (M : Mat12) (j : Fin 12) : (e11 ᵥ* M) j = M 11 j := by
  simp [e11, Matrix.vecMul, dotProduct, Pi.single_apply]

@[expose] noncomputable def Lsub : Subgroup GLm where
  carrier := {g | (g : Mat12) *ᵥ e11 = e11}
  one_mem' := by
    change ((1 : GLm) : Mat12) *ᵥ e11 = e11
    rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb
    have ha' : (a : Mat12) *ᵥ e11 = e11 := ha
    have hb' : (b : Mat12) *ᵥ e11 = e11 := hb
    change ((a * b : GLm) : Mat12) *ᵥ e11 = e11
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : (a : Mat12) *ᵥ e11 = e11 := ha
    change ((a⁻¹ : GLm) : Mat12) *ᵥ e11 = e11
    calc ((a⁻¹ : GLm) : Mat12) *ᵥ e11 = ((a⁻¹ : GLm) : Mat12) *ᵥ ((a : Mat12) *ᵥ e11) := by rw [ha']
      _ = e11 := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

@[expose] noncomputable def Rsub : Subgroup GLm where
  carrier := {g | e11 ᵥ* (g : Mat12) = e11}
  one_mem' := by
    change e11 ᵥ* ((1 : GLm) : Mat12) = e11
    rw [Units.val_one, Matrix.vecMul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : e11 ᵥ* (a : Mat12) = e11 := ha
    have hb' : e11 ᵥ* (b : Mat12) = e11 := hb
    change e11 ᵥ* ((a * b : GLm) : Mat12) = e11
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : e11 ᵥ* (a : Mat12) = e11 := ha
    change e11 ᵥ* ((a⁻¹ : GLm) : Mat12) = e11
    calc e11 ᵥ* ((a⁻¹ : GLm) : Mat12) = (e11 ᵥ* (a : Mat12)) ᵥ* ((a⁻¹ : GLm) : Mat12) := by rw [ha']
      _ = e11 := by
        rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem zmod2_eq_one {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h
  decide

theorem mem_Lsub_of {g : GLm} (h : ∀ i : Fin 12, i ≠ 11 → (g : Mat12) i 11 = 0) : g ∈ Lsub := by
  have h1 : ((g⁻¹ : GLm) : Mat12) * (g : Mat12) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 := congrFun (congrFun h1 11) 11
  rw [Matrix.mul_apply, Finset.sum_eq_single (11 : Fin 12) (fun m _ hm => by rw [h m hm, mul_zero])
    (by simp), Matrix.one_apply_eq] at h2
  have h3 : (g : Mat12) 11 11 = 1 := zmod2_eq_one fun h0 => by
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  change (g : Mat12) *ᵥ e11 = e11
  funext i
  rw [mulVec_e11, e11_apply]
  split_ifs with hi
  · rw [hi]
    exact h3
  · exact h i hi

theorem mem_Lsub_iff {g : GLm} : g ∈ Lsub ↔ ∀ i : Fin 12, (g : Mat12) i 11 = if i = 11 then 1 else 0 := by
  constructor
  · intro h i
    have h' : (g : Mat12) *ᵥ e11 = e11 := h
    rw [← mulVec_e11 (g : Mat12) i, h', e11_apply]
  · intro h
    change (g : Mat12) *ᵥ e11 = e11
    funext i
    rw [mulVec_e11, e11_apply, h]

theorem mem_Rsub_iff {g : GLm} : g ∈ Rsub ↔ ∀ j : Fin 12, (g : Mat12) 11 j = if j = 11 then 1 else 0 := by
  constructor
  · intro h j
    have h' : e11 ᵥ* (g : Mat12) = e11 := h
    rw [← e11_vecMul (g : Mat12) j, h', e11_apply]
  · intro h
    change e11 ᵥ* (g : Mat12) = e11
    funext j
    rw [e11_vecMul, e11_apply, h]

theorem col_mul_L (A : Mat12) {l : GLm} (hl : l ∈ Lsub) : (A * (l : Mat12)) *ᵥ e11 = A *ᵥ e11 := by
  have hl' : (l : Mat12) *ᵥ e11 = e11 := hl
  rw [← Matrix.mulVec_mulVec, hl']

theorem mul_tr_apply {A l : Mat12} (hA : ∀ i j : Fin 12, ¬ (j = 11 ∧ i ≠ 11) → A i j = (1 : Mat12) i j)
    (hl : ∀ j : Fin 12, l 11 j = if j = 11 then 1 else 0) {i j : Fin 12} (hij : ¬ (j = 11 ∧ i ≠ 11)) :
    (A * l) i j = l i j := by
  have e : (A * l) i j = ((1 : Mat12) * l) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m = 11 ∧ i ≠ 11
    · obtain ⟨rfl, hi⟩ := hm
      have hj : j ≠ 11 := fun hj => hij ⟨hj, hi⟩
      rw [hl, ite_eq_right hj, mul_zero, mul_zero]
    · rw [hA i m hm]
  rw [e, one_mul]

theorem tr_mul_self {A : Mat12} (hA : ∀ i j : Fin 12, ¬ (j = 11 ∧ i ≠ 11) → A i j = (1 : Mat12) i j) :
    A * A = 1 := by
  have hl : ∀ j : Fin 12, A 11 j = if j = 11 then 1 else 0 := fun j => by
    rw [hA 11 j (fun h => h.2 rfl), Matrix.one_apply]
    by_cases hj : j = 11
    · simp [hj]
    · simp [hj, Ne.symm hj]
  ext i j
  by_cases hij : j = 11 ∧ i ≠ 11
  · obtain ⟨rfl, hi⟩ := hij
    rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem i 11 (Finset.mem_univ _) (Finset.mem_univ _) hi
      (fun m _ hm => by rw [hA i m (fun h => hm.2 h.1), Matrix.one_apply_ne (Ne.symm hm.1), zero_mul]),
      hA i i (fun h => hi h.1), Matrix.one_apply_eq, one_mul, hl, ite_eq_left rfl, mul_one,
      Matrix.one_apply_ne hi]
    generalize A i 11 = a
    revert a
    decide
  · rw [mul_tr_apply hA hl hij, hA i j hij]

theorem inv_val {u : GLm} {X : Mat12} (h : (u : Mat12) * X = 1) : ((u⁻¹ : GLm) : Mat12) = X := by
  calc ((u⁻¹ : GLm) : Mat12) = ((u⁻¹ : GLm) : Mat12) * ((u : Mat12) * X) := by rw [h, mul_one]
    _ = X := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

@[expose] noncomputable def actS : RightAct GLm (Set Vec) where
  act P g := (fun v => v ᵥ* (g : Mat12)) '' P
  act_one P := by simp
  act_mul P g h := by
    rw [Units.val_mul]
    exact image_vecMul_mul _ _ _

@[expose] noncomputable def Stab (P : Set Vec) : Subgroup GLm := actS.fixSub {P}

theorem mem_Stab {P : Set Vec} {g : GLm} : g ∈ Stab P ↔ (fun v => v ᵥ* (g : Mat12)) '' P = P := by
  simp only [Stab, RightAct.mem_fixSub, Set.mem_singleton_iff, forall_eq]
  rfl

theorem act_eq (P : Set Vec) (g : GLm) : actS.act P g = (fun v => v ᵥ* (g : Mat12)) '' P := rfl

theorem stab_of_chkPt {P g h : ℕ} {u : GLm} (hP : ptOK P = true) (hu : (u : Mat12) = toMat g)
    (hc : chkPt P g P h = true) : u ∈ Stab (ptVecs P) :=
  mem_Stab.2 (by rw [hu]; exact chkPt_image hP hP hc)

@[expose] noncomputable def thV (k : KD) : Set Vec := ptVecs k.TH

@[expose] noncomputable def xK (LET : ℕ) : Khat LET := ⟨xh LET, Subgroup.subset_closure (by simp)⟩
@[expose] noncomputable def yK (LET : ℕ) : Khat LET := ⟨yh LET, Subgroup.subset_closure (by simp)⟩
@[expose] noncomputable def zK (LET : ℕ) : Khat LET := ⟨zh LET, Subgroup.subset_closure (by simp)⟩

@[expose] noncomputable def kv (LET : ℕ) : ℕ → Khat LET := lvE (jv (xK LET) (yK LET) 1 (zK LET))

@[expose] def good (c : ℕ) : Prop := c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 5 ∨ c = 6

theorem coe_kv (LET c : ℕ) : ((kv LET c : Khat LET) : GLm) = lvE (jv (xh LET) (yh LET) 1 (zh LET)) c := by
  unfold kv lvE jv
  split_ifs <;> rfl

theorem coe_wordVal_kv (LET w n : ℕ) :
    ((wordVal (kv LET) w n : Khat LET) : GLm) = wordVal (lvE (jv (xh LET) (yh LET) 1 (zh LET))) w n := by
  have h := map_wordVal (Khat LET).subtype (kv LET) w n
  rw [Subgroup.coe_subtype] at h
  rw [h]
  exact wordVal_congr fun i _ => coe_kv LET _

theorem wv_eq_wordVal {G : Type*} [Group G] (f : ℕ → G) (w n : ℕ) : wv f w n = wordVal f w n := by
  rw [wordVal_eq_prod]
  rfl

theorem word_unit {k : KD} (hS : kSetup k = true) {w n M : ℕ} (hE : chkEval k.LET w n M = true)
    {X : Mat12} (hX : toMat M * X = 1) :
    (∀ i < n, good (wLet w i)) ∧ toMat M = (((wordVal (kv k.LET) w n : Khat k.LET) : GLm) : Mat12) := by
  obtain ⟨h4, h01, h23, h56, hL, -, -⟩ := kSetup_parts hS
  have hM := chkEval_sound hE
  have hg : ∀ i < n, good (wLet w i) := fun i hi => letter_cases hL h4 fun h0 => by
    have h0' := wordVal_eq_zero (e := fun c => toMat (letMat k.LET c)) hi h0
    rw [← hM] at h0'
    rw [h0', zero_mul] at hX
    exact zero_ne_one hX
  refine ⟨hg, ?_⟩
  rw [hM, model_word_of h01 h23 h56 (fun i hi => hg i hi), coe_wordVal_kv]

theorem unit_mem {k : KD} (hS : kSetup k = true) {w n M : ℕ} (hE : chkEval k.LET w n M = true)
    {u : GLm} (hu : (u : Mat12) = toMat M) : u ∈ Khat k.LET := by
  have hX : toMat M * ((u⁻¹ : GLm) : Mat12) = 1 := by
    rw [← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨-, hM⟩ := word_unit hS hE hX
  have e : u = ((wordVal (kv k.LET) w n : Khat k.LET) : GLm) := Units.ext (hu.trans hM)
  rw [e]
  exact SetLike.coe_mem _

section phi

variable {LET : ℕ} {G : Type*} [Group G] {φ : Khat LET →* G} {x y t z : G}

theorem phi_kv (hx : ∀ g : Khat LET, (g : GLm) = xh LET → φ g = x)
    (hy : ∀ g : Khat LET, (g : GLm) = yh LET → φ g = y)
    (hz : ∀ g : Khat LET, (g : GLm) = zh LET → φ g = z) {c : ℕ} (hc : good c) :
    φ (kv LET c) = lvE (jv x y t z) c := by
  have ex : φ (xK LET) = x := hx _ rfl
  have ey : φ (yK LET) = y := hy _ rfl
  have ez : φ (zK LET) = z := hz _ rfl
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [kv, lvE, jv, ex, ey, ez]

theorem phi_word (hx : ∀ g : Khat LET, (g : GLm) = xh LET → φ g = x)
    (hy : ∀ g : Khat LET, (g : GLm) = yh LET → φ g = y)
    (hz : ∀ g : Khat LET, (g : GLm) = zh LET → φ g = z) {w n : ℕ} (hg : ∀ i < n, good (wLet w i)) :
    φ (wordVal (kv LET) w n) = wordVal (lvE (jv x y t z)) w n := by
  rw [map_wordVal]
  exact wordVal_congr fun i hi => phi_kv hx hy hz (hg i hi)

end phi

theorem allIn_spec {b : ℕ} {f : ℕ → Bool} (h : allIn 0 b f = true) {i : ℕ} (hi : i < b) : f i = true := by
  refine CFSG.Certificates.J4KShape.rngAll_spec _ h i (Nat.zero_le _) hi ?_
  change i < 0 + 64 * ((b - 0) >>> 6 + 1)
  rw [Nat.shiftRight_eq_div_pow]
  have h64 : (2 : ℕ) ^ 6 = 64 := rfl
  rw [h64]
  omega

structure Ok (k : KD) : Prop where
  hS : kSetup k = true
  hH : kHdr k = true
  hP : kPts k = true
  hL : kLam k = true
  hC : kChains k = true
  hR : kRange k = true
  x11 : row11 (letMat k.LET 0) = true
  w11 : row11 k.W0 = true
  ylin : chkLin (letMat k.LET 2) = true
  hW : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000
  hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
    Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN
  hHT : ∀ h, k.nH ≤ h → h < 2 ^ 16 → k.HT h = 0
  hsw : k.sw < 256 ^ k.sn

theorem Ok.of {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)}
    (h : j4Ok k d KW MW MT FLs = true) (hf : j4Fix k FLs = true)
    (hW : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN)
    (hHT : ∀ h, k.nH ≤ h → h < 2 ^ 16 → k.HT h = 0) (hsw : k.sw < 256 ^ k.sn) : Ok k := by
  obtain ⟨hS, h⟩ := andB_eq_true.1 h
  obtain ⟨hH, h⟩ := andB_eq_true.1 h
  obtain ⟨hP, h⟩ := andB_eq_true.1 h
  obtain ⟨hL, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hC, h⟩ := andB_eq_true.1 h
  obtain ⟨hR, -⟩ := andB_eq_true.1 h
  obtain ⟨-, hf⟩ := andB_eq_true.1 hf
  obtain ⟨x11, hf⟩ := andB_eq_true.1 hf
  obtain ⟨w11, hf⟩ := andB_eq_true.1 hf
  obtain ⟨ylin, -⟩ := andB_eq_true.1 hf
  exact ⟨hS, hH, hP, hL, hC, hR, x11, w11, ylin, hW, hN, hHT, hsw⟩

theorem kSetup_more {k : KD} (h : kSetup k = true) :
    ptOK k.TH = true ∧ (∀ r < 12, relAt k.RT k.LET r = true) ∧
    chkEval k.LET (wW k.PAW) (wN k.PAW) k.TR1 = true ∧ chkEval k.LET (wW k.PBW) (wN k.PBW) k.PS1 = true ∧
    chkTrans k.TR1 = true := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hT, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hR, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hA, h⟩ := andB_eq_true.1 h
  obtain ⟨hB, h⟩ := andB_eq_true.1 h
  obtain ⟨hTr, -⟩ := andB_eq_true.1 h
  exact ⟨hT, fun r hr => CFSG.Certificates.J4KShape.rngAll_spec _ hR r (Nat.zero_le _) hr
    (lt_of_lt_of_le hr (by decide)), hA, hB, hTr⟩

theorem kChains_T0 {k : KD} (h : kChains k = true) :
    chainRun k.FT k.ET0 k.LET k.W0 k.TR1 65535 513 k.neT0 k.LVT0 = k.BT0 ∧
    k.BK = k.NOM * 512 * k.BT0 := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨h0, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, hB⟩ := andB_eq_true.1 h
  exact ⟨beq_eq_true.1 h0, beq_eq_true.1 hB⟩

theorem kRange_nom {k : KD} (h : kRange k = true) : 0 < k.NOM := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨h0, -⟩ := andB_eq_true.1 h
  exact blt_eq_true.1 h0

theorem kPts_parts {k : KD} (h : kPts k = true) :
    (∀ i < k.NOM, ptAt k.PT i = true) ∧ (∀ j < k.NOM, omAt k.HT k.PT k.OT k.TH j = true) := by
  obtain ⟨h1, h2⟩ := andB_eq_true.1 h
  exact ⟨fun i hi => allIn_spec h1 hi, fun j hj => allIn_spec h2 hj⟩

theorem kLam_parts {k : KD} (h : kLam k = true) :
    (∀ i < 9, conjOK k.CT k.LET k.TH k.TR1 k.PS1 i = true) ∧
    (∀ e < 512, lamOK k.LT k.CT k.TH e = true) ∧ lamCols k.LT 512 < 2 ^ 2048 ∧
    psiGenOK k.RT k.HT k.LET k.INV k.TH 8 1 1 1 1 k.hx 2 = true ∧ hMat (k.HT k.hx) = letMat k.LET 0 ∧
    psiGenOK k.RT k.HT k.LET k.INV k.TH 9 k.sw k.sn k.sw k.sn k.hw 1 = true ∧
    chkInv (hMat (k.HT k.hw)) k.W0 = true := by
  obtain ⟨hc, h⟩ := andB_eq_true.1 h
  obtain ⟨hl, h⟩ := andB_eq_true.1 h
  obtain ⟨hcol, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨h8, h9⟩ := andB_eq_true.1 h
  obtain ⟨p8, e8⟩ := andB_eq_true.1 h8
  obtain ⟨p9, e9⟩ := andB_eq_true.1 h9
  have hcol' : lamCols k.LT 512 < 1 <<< 2048 := blt_eq_true.1 hcol
  rw [Nat.one_shiftLeft] at hcol'
  exact ⟨fun i hi => allIn_spec hc hi, fun e he => allIn_spec hl he, hcol', p8, beq_eq_true.1 e8, p9, e9⟩

theorem psiGen_spec {RT HT : ℕ → ℕ} {LET INV TH r sw sn pw pn sH h : ℕ}
    (hc : psiGenOK RT HT LET INV TH r sw sn pw pn sH h = true) :
    chkPsiRel INV 4 sw sn pw pn (wW (RT r)) (wN (RT r)) = true ∧ chkEval LET sw sn (hMat (HT sH)) = true ∧
    chkLin (hMat (HT sH)) = true ∧ chkPt TH (hMat (HT sH)) TH h = true ∧
    chkEval LET pw pn (hMat (HT sH)) = true := by
  simp only [psiGenOK, CFSG.Certificates.J4Chain.letB_eq, chkPtF_eq] at hc
  obtain ⟨a, hc⟩ := andB_eq_true.1 hc
  obtain ⟨b, hc⟩ := andB_eq_true.1 hc
  obtain ⟨c, hc⟩ := andB_eq_true.1 hc
  obtain ⟨d, e⟩ := andB_eq_true.1 hc
  exact ⟨a, b, c, d, e⟩

theorem conj_spec {CT : ℕ → ℕ} {LET TH TR PS i : ℕ} (hc : conjOK CT LET TH TR PS i = true) :
    chkEval LET (cW (CT i)) (cN (CT i)) (cC (CT i)) = true ∧ chkLin (cC (CT i)) = true ∧
    chkPt TH (cC (CT i)) TH (cS (CT i)) = true ∧ mul12 (cC (CT i)) (cCI (CT i)) = ident12 ∧
    cBT (CT i) = mul12 (mul12 (cCI (CT i)) TR) (cC (CT i)) ∧
    cBP (CT i) = mul12 (mul12 (cCI (CT i)) PS) (cC (CT i)) := by
  simp only [conjOK, CFSG.Certificates.J4Chain.letB_eq, chkPtF_eq, mulF_eq] at hc
  obtain ⟨-, hc⟩ := andB_eq_true.1 hc
  obtain ⟨-, hc⟩ := andB_eq_true.1 hc
  obtain ⟨a, hc⟩ := andB_eq_true.1 hc
  obtain ⟨b, hc⟩ := andB_eq_true.1 hc
  obtain ⟨c, hc⟩ := andB_eq_true.1 hc
  obtain ⟨d, hc⟩ := andB_eq_true.1 hc
  obtain ⟨e, f⟩ := andB_eq_true.1 hc
  exact ⟨a, b, c, beq_eq_true.1 d, beq_eq_true.1 e, beq_eq_true.1 f⟩

theorem lam_spec {LT CT : ℕ → ℕ} {TH e : ℕ} (hc : lamOK LT CT TH e = true) :
    (e = 0 ∧ lamT (LT e) = ident12 ∧ lP' (LT e) = ident12) ∨
    (e ≠ 0 ∧ lPar (LT e) < e ∧ lK (LT e) < 9 ∧
      lamT (LT e) = mul12 (lamT (LT (lPar (LT e)))) (cBT (CT (lK (LT e)))) ∧
      lP' (LT e) = mul12 (lP' (LT (lPar (LT e)))) (cBP (CT (lK (LT e)))) ∧
      chkTrans (lamT (LT e)) = true ∧ chkPt TH (lamT (LT e)) TH (lS (LT e)) = true) := by
  simp only [lamOK, CFSG.Certificates.J4Chain.letB_eq, chkPtF_eq, mulF_eq] at hc
  revert hc
  cases hb : Nat.beq e (nat_lit 0)
  · intro hc
    obtain ⟨a, hc⟩ := andB_eq_true.1 hc
    obtain ⟨b, hc⟩ := andB_eq_true.1 hc
    obtain ⟨c, hc⟩ := andB_eq_true.1 hc
    obtain ⟨d, hc⟩ := andB_eq_true.1 hc
    obtain ⟨f, g⟩ := andB_eq_true.1 hc
    exact Or.inr ⟨Nat.ne_of_beq_eq_false hb, blt_eq_true.1 a, blt_eq_true.1 b, beq_eq_true.1 c,
      beq_eq_true.1 d, f, g⟩
  · intro hc
    obtain ⟨a, b⟩ := andB_eq_true.1 hc
    exact Or.inl ⟨Nat.eq_of_beq_eq_true hb, beq_eq_true.1 a, beq_eq_true.1 b⟩

theorem hOK_spec {HT : ℕ → ℕ} {LET nl R1 R2 h : ℕ} (hc : hOK HT LET nl R1 R2 h = true) :
    mul12 (hMat (HT h)) (hInv (HT h)) = ident12 ∧
    (hMat (HT h) = ident12 ∨ (hA (HT h) < nl ∧ hMat (HT h) = letMat LET (hA (HT h))) ∨
      (hA (HT h) < h ∧ hB (HT h) < h ∧
        hMat (HT h) = mul12 (hMat (HT (hA (HT h)))) (hMat (HT (hB (HT h))))) ∨
      (hA (HT h) < h ∧ mul12 (hMat (HT h)) (hMat (HT (hA (HT h)))) = ident12) ∨
      hMat (HT h) = R1 ∨ hMat (HT h) = R2) := by
  simp only [hOK, CFSG.Certificates.J4Chain.letB_eq, mulF_eq] at hc
  obtain ⟨h1, h2⟩ := andB_eq_true.1 hc
  refine ⟨beq_eq_true.1 h1, ?_⟩
  revert h2
  cases Nat.beq (hKind (HT h)) (nat_lit 0)
  · cases Nat.beq (hKind (HT h)) (nat_lit 1)
    · cases Nat.beq (hKind (HT h)) (nat_lit 2)
      · cases Nat.beq (hKind (HT h)) (nat_lit 3)
        · intro h2
          obtain ⟨-, h2⟩ := andB_eq_true.1 h2
          obtain ⟨-, h2⟩ := andB_eq_true.1 h2
          rcases orB_eq_true.1 h2 with e | e
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (beq_eq_true.1 e)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (beq_eq_true.1 e)))))
        · intro h2
          obtain ⟨a, b⟩ := andB_eq_true.1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨blt_eq_true.1 a, beq_eq_true.1 b⟩)))
      · intro h2
        obtain ⟨a, h2⟩ := andB_eq_true.1 h2
        obtain ⟨b, c⟩ := andB_eq_true.1 h2
        exact Or.inr (Or.inr (Or.inl ⟨blt_eq_true.1 a, blt_eq_true.1 b, beq_eq_true.1 c⟩))
    · intro h2
      obtain ⟨a, b⟩ := andB_eq_true.1 h2
      exact Or.inr (Or.inl ⟨blt_eq_true.1 a, beq_eq_true.1 b⟩)
  · intro h2
    exact Or.inl (beq_eq_true.1 h2)

theorem tr_unit {A : ℕ} (hA : chkTrans A = true) : chkInv A A = true := by
  have h := tr_mul_self (chkTrans_iff.1 hA)
  change Nat.beq (mul12 A A) ident12 = true
  rw [beq_eq_true]
  refine eq_of_toMat_eq (mul12_lt _ _) ident12_lt ?_
  rw [toMat_mul12, h, toMat_ident12]

@[expose] noncomputable def tr1u (k : KD) : GLm := lu k.TR1 k.TR1

theorem tr1_facts {k : KD} (hS : kSetup k = true) :
    ((tr1u k : GLm) : Mat12) = toMat k.TR1 ∧ tr1u k ∈ Khat k.LET := by
  obtain ⟨-, -, hA, -, hT⟩ := kSetup_more hS
  have hv : ((tr1u k : GLm) : Mat12) = toMat k.TR1 := val_lu (tr_unit hT)
  exact ⟨hv, unit_mem hS hA hv⟩

theorem hdr_mem {k : KD} (hS : kSetup k = true) (hH : kHdr k = true) :
    ∀ h < k.nH, ∃ u : Khat k.LET, ((u : GLm) : Mat12) = toMat (hMat (k.HT h)) := by
  obtain ⟨h4, h01, h23, h56, hL, -, -⟩ := kSetup_parts hS
  obtain ⟨-, -, hPA, hPB, -⟩ := kSetup_more hS
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
  intro hh
  obtain ⟨hinv, hc⟩ := hOK_spec (allIn_spec hH hh)
  have hX : toMat (hMat (k.HT h)) * toMat (hInv (k.HT h)) = 1 := by
    rw [← toMat_mul12, hinv, toMat_ident12]
  rcases hc with e | ⟨-, e⟩ | ⟨ha, hb, e⟩ | ⟨ha, e⟩ | e | e
  · exact ⟨1, by rw [e, toMat_ident12]; rfl⟩
  · have hg : good (hA (k.HT h)) := letter_cases hL h4 fun h0 => by
      rw [e, h0, zero_mul] at hX
      exact zero_ne_one hX
    exact ⟨kv k.LET _, by rw [e, model_letter h01 h23 h56 hg, coe_kv]⟩
  · obtain ⟨ua, hua⟩ := ih _ ha (by omega)
    obtain ⟨ub, hub⟩ := ih _ hb (by omega)
    refine ⟨ua * ub, ?_⟩
    rw [e, toMat_mul12, ← hua, ← hub]
    rfl
  · obtain ⟨ua, hua⟩ := ih _ ha (by omega)
    refine ⟨ua⁻¹, ?_⟩
    have h1 : toMat (hMat (k.HT h)) * ((ua : GLm) : Mat12) = 1 := by
      rw [hua, ← toMat_mul12, e, toMat_ident12]
    have h2 : toMat (hMat (k.HT h)) = (((ua : GLm)⁻¹ : GLm) : Mat12) := by
      calc toMat (hMat (k.HT h)) = toMat (hMat (k.HT h)) * (((ua : GLm) : Mat12) * (((ua : GLm)⁻¹ : GLm) : Mat12)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
        _ = (((ua : GLm)⁻¹ : GLm) : Mat12) := by rw [← mul_assoc, h1, one_mul]
    rw [h2]
    rfl
  · rw [e] at hX ⊢
    obtain ⟨-, hM⟩ := word_unit hS hPA hX
    exact ⟨_, hM.symm⟩
  · rw [e] at hX ⊢
    obtain ⟨-, hM⟩ := word_unit hS hPB hX
    exact ⟨_, hM.symm⟩

theorem chkOmF_eq (TH O H h : ℕ) : chkOmF TH O H h = chkOm TH O H h := by
  cases O <;> cases H <;> rfl

theorem oBase_eq (O : ℕ) : oBase O = O &&& (2 ^ 340 - 1) := by
  rw [← Nat.one_shiftLeft]
  rfl

theorem testBit_oBase (O i : ℕ) : (oBase O).testBit i = (O.testBit i && decide (i < 340)) := by
  rw [oBase_eq, Nat.testBit_and, Nat.testBit_two_pow_sub_one]

theorem mask144_eq : mask144 = 2 ^ 144 - 1 := by decide +kernel

theorem oJ_oBase (O : ℕ) : oJ (oBase O) = oJ O := by
  change oBase O &&& (2 ^ 16 - 1) = O &&& (2 ^ 16 - 1)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, testBit_oBase, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 16
  · have : i < 340 := by omega
    simp [hi, this]
  · simp [hi]

theorem oP_oBase (O : ℕ) : oP (oBase O) = oP O := by
  change (oBase O >>> 16) &&& (2 ^ 36 - 1) = (O >>> 16) &&& (2 ^ 36 - 1)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_oBase, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 36
  · have : 16 + i < 340 := by omega
    simp [hi, this]
  · simp [hi]

theorem oG_oBase (O : ℕ) : oG (oBase O) = oG O := by
  change (oBase O >>> 52) &&& mask144 = (O >>> 52) &&& mask144
  rw [mask144_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_oBase, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 144
  · have : 52 + i < 340 := by omega
    simp [hi, this]
  · simp [hi]

theorem oGi_oBase (O : ℕ) : oGi (oBase O) = oGi' O := by
  change oBase O >>> 196 = (O >>> 196) &&& mask144
  rw [mask144_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_oBase, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 144
  · have : 196 + i < 340 := by omega
    simp [hi, this]
  · have : ¬ 196 + i < 340 := by omega
    simp [hi, this]

theorem om_spec {k : KD} (o : Ok k) {j : ℕ} (hj : j < k.NOM) (hO : k.OT j ≠ 0) :
    oJ (k.OT j) = j + 1 ∧ oP (k.OT j) = k.PT j ∧
    ∃ g : Khat k.LET, ((g : GLm) : Mat12) = toMat (oG (k.OT j)) ∧
      (((g⁻¹ : Khat k.LET) : GLm) : Mat12) = toMat (oGi' (k.OT j)) ∧
      actS.act (thV k) g = ptVecs (k.PT j) := by
  have hc : omOK k.HT k.PT k.TH j (k.OT j) = true := (kPts_parts o.hP).2 j hj
  simp only [omOK, chkOmF_eq] at hc
  rcases orB_eq_true.1 hc with h0 | hc
  · exact absurd (beq_eq_true.1 h0) hO
  obtain ⟨hJ, hc⟩ := andB_eq_true.1 hc
  obtain ⟨hP, hc⟩ := andB_eq_true.1 hc
  obtain ⟨-, hc⟩ := andB_eq_true.1 hc
  obtain ⟨hpt, hc⟩ := andB_eq_true.1 hc
  obtain ⟨hpt2, hc⟩ := andB_eq_true.1 hc
  obtain ⟨hgi, hgH⟩ := andB_eq_true.1 hc
  rw [oP_oBase] at hpt hpt2
  rw [oG_oBase] at hpt2 hgi hgH
  rw [oGi_oBase] at hgi
  have hgi' := beq_eq_true.1 hgi
  have hgH' := beq_eq_true.1 hgH
  have hP' := beq_eq_true.1 hP
  refine ⟨beq_eq_true.1 hJ, hP', ?_⟩
  have hX : toMat (oG (k.OT j)) * toMat (oGi' (k.OT j)) = 1 := by
    rw [← toMat_mul12, hgi', toMat_ident12]
  have hne : k.HT (oH (k.OT j)) ≠ 0 := by
    intro h0
    rw [h0] at hgH'
    have h0' : oG (k.OT j) = 0 := hgH'
    rw [h0', toMat_zero, zero_mul] at hX
    exact zero_ne_one hX
  have hlt : oH (k.OT j) < k.nH := by
    by_contra hn
    exact hne (o.hHT _ (not_lt.1 hn) (Nat.and_lt_two_pow _ (by decide)))
  obtain ⟨u, hu⟩ := hdr_mem o.hS o.hH _ hlt
  rw [← hgH'] at hu
  refine ⟨u, hu, ?_, ?_⟩
  · rw [Subgroup.coe_inv]
    exact inv_val (by rw [hu]; exact hX)
  · rw [act_eq, hu, ← hP']
    exact chkPt_image (kSetup_more o.hS).1 hpt hpt2

@[expose] noncomputable def w0u (k : KD) : GLm := (lu (hMat (k.HT k.hw)) k.W0)⁻¹

@[expose] noncomputable def Tg (k : KD) : Subgroup GLm := Stab (thV k) ⊓ Khat k.LET

@[expose] noncomputable def T0 (k : KD) : Subgroup GLm := Subgroup.closure {xh k.LET, w0u k}

theorem mem_Rsub_of_row11 {g : GLm} {M : ℕ} (hg : (g : Mat12) = toMat M)
    (h : Nat.beq (Nat.land (Nat.shiftRight M 132) 4095) 2048 = true) : g ∈ Rsub :=
  mem_Rsub_iff.2 fun j => by rw [hg]; exact row11_iff.1 h j

theorem xh_facts {k : KD} (o : Ok k) : xh k.LET ∈ Tg k ∧ xh k.LET ∈ Lsub ∧ xh k.LET ∈ Rsub := by
  obtain ⟨-, h01, -, -, -, -, -⟩ := kSetup_parts o.hS
  obtain ⟨-, -, -, p8, e8, -, -⟩ := kLam_parts o.hL
  obtain ⟨-, -, hlin, hpt, -⟩ := psiGen_spec p8
  rw [e8] at hlin hpt
  have hv : ((xh k.LET : GLm) : Mat12) = toMat (letMat k.LET 0) := val_lu h01
  refine ⟨⟨stab_of_chkPt (kSetup_more o.hS).1 hv hpt, Subgroup.subset_closure (by simp)⟩,
    mem_Lsub_of fun i hi => by rw [hv]; exact chkLin_iff.1 hlin i hi, mem_Rsub_of_row11 hv o.x11⟩

theorem w0_facts {k : KD} (o : Ok k) :
    w0u k ∈ Tg k ∧ w0u k ∈ Lsub ∧ w0u k ∈ Rsub ∧ ((w0u k : GLm) : Mat12) = toMat k.W0 := by
  obtain ⟨-, -, -, -, -, p9, hinv⟩ := kLam_parts o.hL
  obtain ⟨-, hev, hlin, hpt, -⟩ := psiGen_spec p9
  have hU : ((lu (hMat (k.HT k.hw)) k.W0 : GLm) : Mat12) = toMat (hMat (k.HT k.hw)) := val_lu hinv
  have hv : ((w0u k : GLm) : Mat12) = toMat k.W0 := val_inv_lu hinv
  have hK : lu (hMat (k.HT k.hw)) k.W0 ∈ Khat k.LET := unit_mem o.hS hev hU
  have hSt := stab_of_chkPt (kSetup_more o.hS).1 hU hpt
  have hLs : lu (hMat (k.HT k.hw)) k.W0 ∈ Lsub :=
    mem_Lsub_of fun i hi => by rw [hU]; exact chkLin_iff.1 hlin i hi
  exact ⟨⟨(Stab _).inv_mem hSt, (Khat k.LET).inv_mem hK⟩, Lsub.inv_mem hLs,
    mem_Rsub_of_row11 hv o.w11, hv⟩

theorem T0_le {k : KD} (o : Ok k) : T0 k ≤ Tg k ⊓ (Lsub ⊓ Rsub) := by
  obtain ⟨a1, a2, a3⟩ := xh_facts o
  obtain ⟨b1, b2, b3, -⟩ := w0_facts o
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact ⟨a1, a2, a3⟩
  · exact ⟨b1, b2, b3⟩

theorem T0_le_Tg {k : KD} (o : Ok k) : T0 k ≤ Tg k := fun _ h => (T0_le o h).1

theorem T0_le_Khat {k : KD} (o : Ok k) : T0 k ≤ Khat k.LET := fun _ h => (T0_le o h).1.2

theorem bt0_le {k : KD} (o : Ok k) : k.BT0 ≤ Nat.card (T0 k) := by
  obtain ⟨-, h01, -, -, -, -, -⟩ := kSetup_parts o.hS
  rw [← (kChains_T0 o.hC).1]
  unfold T0
  refine CFSG.Certificates.J4Chain.chainRun_le pm _
    ⟨fun l hl hg => ?_, fun _ _ _ hg => ?_, fun _ => ?_, fun hg => ?_⟩
  · interval_cases l
    · exact ⟨xh k.LET, by simp, val_lu h01⟩
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim
  · exact ⟨w0u k, by simp, (w0_facts o).2.2.2⟩
  · exact (gm_false (by decide +kernel) hg).elim

@[expose] noncomputable def trG (k : KD) (e : ℕ) : GLm := lu (lamT (k.LT e)) (lamT (k.LT e))

@[expose] noncomputable def cu (k : KD) (i : ℕ) : GLm := lu (cC (k.CT i)) (cCI (k.CT i))

theorem lam_trans {k : KD} (o : Ok k) {e : ℕ} (he : e < 512) : chkTrans (lamT (k.LT e)) = true := by
  rcases lam_spec ((kLam_parts o.hL).2.1 e he) with ⟨-, h, -⟩ | ⟨-, -, -, -, -, h, -⟩
  · rw [h]
    decide +kernel
  · exact h

theorem val_trG {k : KD} (o : Ok k) {e : ℕ} (he : e < 512) :
    ((trG k e : GLm) : Mat12) = toMat (lamT (k.LT e)) :=
  val_lu (tr_unit (lam_trans o he))

theorem trG_zero {k : KD} (o : Ok k) : trG k 0 = 1 := by
  apply Units.ext
  rw [val_trG o (by norm_num)]
  rcases lam_spec ((kLam_parts o.hL).2.1 0 (by norm_num)) with ⟨-, h, -⟩ | ⟨h, -⟩
  · rw [h, toMat_ident12, Units.val_one]
  · exact absurd rfl h

theorem cu_facts {k : KD} (o : Ok k) {i : ℕ} (hi : i < 9) :
    ((cu k i : GLm) : Mat12) = toMat (cC (k.CT i)) ∧
    (((cu k i)⁻¹ : GLm) : Mat12) = toMat (cCI (k.CT i)) ∧ cu k i ∈ Tg k ∧ cu k i ∈ Lsub := by
  obtain ⟨hev, hlin, hpt, hinv, -, -⟩ := conj_spec ((kLam_parts o.hL).1 i hi)
  have hi' : chkInv (cC (k.CT i)) (cCI (k.CT i)) = true := by
    change Nat.beq _ _ = true
    rw [hinv]
    exact Nat.beq_refl _
  have hv : ((cu k i : GLm) : Mat12) = toMat (cC (k.CT i)) := val_lu hi'
  exact ⟨hv, val_inv_lu hi', ⟨stab_of_chkPt (kSetup_more o.hS).1 hv hpt, unit_mem o.hS hev hv⟩,
    mem_Lsub_of fun j hj => by rw [hv]; exact chkLin_iff.1 hlin j hj⟩

theorem cBT_val {k : KD} (o : Ok k) {i : ℕ} (hi : i < 9) :
    toMat (cBT (k.CT i)) = ((((cu k i)⁻¹ * tr1u k * cu k i : GLm)) : Mat12) := by
  obtain ⟨-, -, -, -, h, -⟩ := conj_spec ((kLam_parts o.hL).1 i hi)
  obtain ⟨c1, c2, -, -⟩ := cu_facts o hi
  rw [h, toMat_mul12, toMat_mul12, Units.val_mul, Units.val_mul, c1, c2, (tr1_facts o.hS).1]

theorem cBP_val {k : KD} (o : Ok k) {i : ℕ} (hi : i < 9) :
    toMat (cBP (k.CT i)) = (((cu k i)⁻¹ : GLm) : Mat12) * toMat k.PS1 * ((cu k i : GLm) : Mat12) := by
  obtain ⟨-, -, -, -, -, h⟩ := conj_spec ((kLam_parts o.hL).1 i hi)
  obtain ⟨c1, c2, -, -⟩ := cu_facts o hi
  rw [h, toMat_mul12, toMat_mul12, c1, c2]

theorem trG_succ {k : KD} (o : Ok k) {e : ℕ} (he : e < 512) (he0 : e ≠ 0) :
    lPar (k.LT e) < e ∧ lK (k.LT e) < 9 ∧
    trG k e = trG k (lPar (k.LT e)) * ((cu k (lK (k.LT e)))⁻¹ * tr1u k * cu k (lK (k.LT e))) ∧
    toMat (lP' (k.LT e)) = toMat (lP' (k.LT (lPar (k.LT e)))) *
      ((((cu k (lK (k.LT e)))⁻¹ : GLm) : Mat12) * toMat k.PS1 * ((cu k (lK (k.LT e)) : GLm) : Mat12)) := by
  rcases lam_spec ((kLam_parts o.hL).2.1 e he) with ⟨h0, -⟩ | ⟨-, hp, hk, hT, hP, -, -⟩
  · exact absurd h0 he0
  refine ⟨hp, hk, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, val_trG o he, val_trG o (by omega), hT, toMat_mul12, cBT_val o hk]
  · rw [hP, toMat_mul12, cBP_val o hk]

theorem lam_mem {k : KD} (o : Ok k) : ∀ e < 512, trG k e ∈ Khat k.LET := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro he
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · rw [trG_zero o]
    exact one_mem _
  obtain ⟨hp, hk, h, -⟩ := trG_succ o he (by omega)
  rw [h]
  have hc := (cu_facts o hk).2.2.1.2
  exact mul_mem (ih _ hp (by omega)) (mul_mem (mul_mem (inv_mem hc) (tr1_facts o.hS).2) hc)

theorem lam_stab {k : KD} (o : Ok k) {e : ℕ} (he : e < 512) : trG k e ∈ Tg k := by
  refine ⟨?_, lam_mem o e he⟩
  rcases lam_spec ((kLam_parts o.hL).2.1 e he) with ⟨rfl, -⟩ | ⟨-, -, -, -, -, -, hpt⟩
  · rw [trG_zero o]
    exact one_mem _
  · exact stab_of_chkPt (kSetup_more o.hS).1 (val_trG o he) hpt

theorem land_one_of_testBit {A B p : ℕ} (h : A.testBit p = B.testBit p) :
    Nat.land (Nat.shiftRight A p) 1 = Nat.land (Nat.shiftRight B p) 1 := by
  change (A >>> p) &&& 1 = (B >>> p) &&& 1
  rw [Nat.and_one_is_mod, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h
  rcases Nat.mod_two_eq_zero_or_one (A / 2 ^ p) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (B / 2 ^ p) with h2 | h2 <;>
    rw [h1, h2] at h ⊢ <;> first | rfl | exact absurd h (by decide)

@[expose] noncomputable def colN (A n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun r acc => Nat.lor acc
    (Nat.shiftLeft (Nat.land (Nat.shiftRight A (Nat.add (Nat.mul 12 r) 11)) 1) r)) n

theorem colN_succ (A n : ℕ) : colN A (n + 1) =
    Nat.lor (colN A n) (Nat.shiftLeft (Nat.land (Nat.shiftRight A (Nat.add (Nat.mul 12 n) 11)) 1) n) :=
  rfl

theorem colN_congr {A B : ℕ} : ∀ n, (∀ r < n, A.testBit (12 * r + 11) = B.testBit (12 * r + 11)) →
    colN A n = colN B n
  | 0, _ => rfl
  | n + 1, h => by
    rw [colN_succ, colN_succ, colN_congr n (fun r hr => h r (by omega)),
      land_one_of_testBit (p := Nat.add (Nat.mul 12 n) 11) (h n (by omega))]

theorem colOf_congr {A B : ℕ} (h : ∀ r < 11, A.testBit (12 * r + 11) = B.testBit (12 * r + 11)) :
    colOf A = colOf B :=
  colN_congr 11 h

theorem lamCols_succ (LT : ℕ → ℕ) (m : ℕ) : lamCols LT (m + 1) =
    Bool.rec (motive := fun _ => ℕ) (Nat.lor (lamCols LT m) (Nat.shiftLeft 1 2048))
      (Nat.lor (lamCols LT m) (Nat.shiftLeft 1 (colOf (lamT (LT m)))))
      (Nat.beq (Nat.land (lamCols LT m) (Nat.shiftLeft 1 (colOf (lamT (LT m))))) 0) := by
  change strictN (lamCols LT m) (fun B => strictN (colOf (lamT (LT m))) (fun c =>
    Bool.rec (motive := fun _ => ℕ) (Nat.lor B (Nat.shiftLeft 1 2048)) (Nat.lor B (Nat.shiftLeft 1 c))
      (Nat.beq (Nat.land B (Nat.shiftLeft 1 c)) 0))) = _
  simp only [CFSG.Certificates.J4Chain.strictN_eq]

theorem lamCols_inv (LT : ℕ → ℕ) : ∀ m, lamCols LT m < 2 ^ 2048 →
    (∀ e < m, (lamCols LT m).testBit (colOf (lamT (LT e))) = true) ∧
    ∀ e < m, ∀ e' < m, colOf (lamT (LT e)) = colOf (lamT (LT e')) → e = e'
  | 0, _ => ⟨fun e he => absurd he (Nat.not_lt_zero _), fun e he => absurd he (Nat.not_lt_zero _)⟩
  | m + 1, h => by
    rw [lamCols_succ] at h ⊢
    revert h
    cases hb : Nat.beq (Nat.land (lamCols LT m) (Nat.shiftLeft 1 (colOf (lamT (LT m))))) 0
    · intro h
      exfalso
      have h' : lamCols LT m ||| 1 <<< 2048 < 2 ^ 2048 := h
      have hbit : (lamCols LT m ||| 1 <<< 2048).testBit 2048 = true := by
        rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.or_true]
      exact absurd (Nat.ge_two_pow_of_testBit hbit) (not_le.2 h')
    · intro h
      have h' : lamCols LT m ||| 1 <<< colOf (lamT (LT m)) < 2 ^ 2048 := h
      obtain ⟨ih1, ih2⟩ := lamCols_inv LT m (lt_of_le_of_lt Nat.left_le_or h')
      have hc0 : (lamCols LT m).testBit (colOf (lamT (LT m))) = false := by
        have h0 : lamCols LT m &&& 1 <<< colOf (lamT (LT m)) = 0 := Nat.eq_of_beq_eq_true hb
        have := congrArg (fun x => Nat.testBit x (colOf (lamT (LT m)))) h0
        simpa [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_self] using this
      refine ⟨fun e he => ?_, fun e he e' he' hee => ?_⟩
      · change (lamCols LT m ||| 1 <<< colOf (lamT (LT m))).testBit _ = true
        rw [Nat.testBit_or]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ih1 e he, Bool.true_or]
        · rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.or_true]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.1 he' with he' | rfl
        · exact ih2 e he e' he' hee
        · have h1 := ih1 e he
          rw [hee, hc0] at h1
          exact absurd h1 (by decide)
        · have h1 := ih1 e' he'
          rw [← hee, hc0] at h1
          exact absurd h1 (by decide)
        · rfl

theorem lam_inj {k : KD} (o : Ok k) {e e' : ℕ} (he : e < 512) (he' : e' < 512)
    (h : ∀ i : Fin 12, i ≠ 11 → toMat (lamT (k.LT e)) i 11 = toMat (lamT (k.LT e')) i 11) : e = e' := by
  have hc : colOf (lamT (k.LT e)) = colOf (lamT (k.LT e')) := colOf_congr fun r hr => by
    have h1 := h ⟨r, by omega⟩ (fun h' => by
      have := congrArg Fin.val h'
      simp at this
      omega)
    rw [toMat_apply, toMat_apply] at h1
    exact eq_of_cast_eq h1
  exact (lamCols_inv k.LT 512 (kLam_parts o.hL).2.2.1).2 e he e' he' hc

@[expose] def Orb (k : KD) : Prop :=
  ∀ j < k.NOM, ∃ g ∈ Khat k.LET, actS.act (thV k) g = ptVecs (k.PT j)

theorem orb_of_om {k : KD} (o : Ok k) {j : ℕ} (hj : j < k.NOM) (hO : k.OT j ≠ 0) :
    ∃ g ∈ Khat k.LET, actS.act (thV k) g = ptVecs (k.PT j) := by
  obtain ⟨-, -, g, -, -, hg⟩ := om_spec o hj hO
  exact ⟨g, g.2, hg⟩

theorem pt_lt {k : KD} (o : Ok k) : ∀ j < k.NOM, ∀ i < j, k.PT i < k.PT j := by
  have hP := (kPts_parts o.hP).1
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ j ih =>
    intro hj i hi
    have h2 : Nat.blt (k.PT (j + 1 - 1)) (k.PT (j + 1)) = true := (andB_eq_true.1 (hP (j + 1) hj)).2
    rw [Nat.add_sub_cancel] at h2
    have hs : k.PT j < k.PT (j + 1) := blt_eq_true.1 h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact lt_trans (ih (by omega) i hi) hs
    · exact hs

theorem pt_inj {k : KD} (o : Ok k) {i j : ℕ} (hi : i < k.NOM) (hj : j < k.NOM)
    (h : ptVecs (k.PT i) = ptVecs (k.PT j)) : i = j := by
  have hP := (kPts_parts o.hP).1
  have e := eq_of_ptVecs_eq (andB_eq_true.1 (hP i hi)).1 (andB_eq_true.1 (hP j hj)).1 h
  rcases lt_trichotomy i j with hl | rfl | hl
  · exact absurd e (ne_of_lt (pt_lt o j hj i hl))
  · rfl
  · exact absurd e (ne_of_gt (pt_lt o i hi j hl))

theorem tstruct {k : KD} (o : Ok k) (hO : Orb k) :
    Nat.card (T0 k) = k.BT0 ∧ Nat.card (Tg k) = 512 * k.BT0 ∧ k.BK = k.NOM * Nat.card (Tg k) ∧
    ∀ g ∈ Tg k, ∃ e < 512, ∃ l ∈ T0 k, g = trG k e * l := by
  classical
  let F : Fin 512 × T0 k → Tg k := fun p =>
    ⟨trG k p.1 * p.2, (Tg k).mul_mem (lam_stab o p.1.2) (T0_le_Tg o p.2.2)⟩
  have hinj : Function.Injective F := by
    rintro ⟨a, l⟩ ⟨b, l'⟩ hab
    have hab' : trG k a * l = trG k b * l' := congrArg Subtype.val hab
    have hcol : ((trG k a : GLm) : Mat12) *ᵥ e11 = ((trG k b : GLm) : Mat12) *ᵥ e11 := by
      calc ((trG k a : GLm) : Mat12) *ᵥ e11 = ((trG k a * l : GLm) : Mat12) *ᵥ e11 := by
            rw [Units.val_mul, col_mul_L _ (T0_le o l.2).2.1]
        _ = ((trG k b * l' : GLm) : Mat12) *ᵥ e11 := by rw [hab']
        _ = ((trG k b : GLm) : Mat12) *ᵥ e11 := by rw [Units.val_mul, col_mul_L _ (T0_le o l'.2).2.1]
    have hab0 : (a : ℕ) = b := lam_inj o a.2 b.2 fun i _ => by
      have h1 := congrFun hcol i
      rwa [mulVec_e11, mulVec_e11, val_trG o a.2, val_trG o b.2] at h1
    have hab1 : a = b := Fin.ext hab0
    subst hab1
    have hl : (l : GLm) = l' := mul_left_cancel hab'
    exact Prod.ext rfl (Subtype.ext hl)
  have hcF : Nat.card (Fin 512 × T0 k) = 512 * Nat.card (T0 k) := by rw [Nat.card_prod, Nat.card_fin]
  have h1 : 512 * Nat.card (T0 k) ≤ Nat.card (Tg k) := hcF ▸ Nat.card_le_card_of_injective F hinj
  have hO' := hO
  choose g hgK hgA using hO'
  have h2 : k.NOM * Nat.card (Tg k) ≤ Nat.card (Khat k.LET) :=
    card_mul_le_of_orbit actS (Khat k.LET) (thV k) k.NOM (fun j => if h : j < k.NOM then g j h else 1)
      (fun j hj => by simp only [dite_eq_left hj]; exact hgK j hj)
      (fun i hi j hj hij => by
        simp only [dite_eq_left hi, dite_eq_left hj] at hij
        rw [hgA i hi, hgA j hj] at hij
        exact pt_inj o hi hj hij)
  have hK : Nat.card (Khat k.LET) = k.BK := card_khat o.hS o.hR o.hC o.hW o.hN
  have hBK := (kChains_T0 o.hC).2
  have hnom := kRange_nom o.hR
  have h3 := bt0_le o
  have h2' : k.NOM * Nat.card (Tg k) ≤ k.NOM * (512 * k.BT0) :=
    (h2.trans hK.le).trans (by rw [hBK, Nat.mul_assoc])
  have h4 := Nat.le_of_mul_le_mul_left h2' hnom
  have hT0 : Nat.card (T0 k) = k.BT0 := by omega
  have hTg : Nat.card (Tg k) = 512 * k.BT0 := by omega
  refine ⟨hT0, hTg, by rw [hTg, hBK, Nat.mul_assoc], fun g' hg' => ?_⟩
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcF, hT0, hTg])
  obtain ⟨⟨e, l⟩, he⟩ := hbij.2 ⟨g', hg'⟩
  exact ⟨e, e.2, l, l.2, (congrArg Subtype.val he).symm⟩

theorem T_decomp {k : KD} (o : Ok k) (hO : Orb k) {g : GLm} (hg : g ∈ Tg k) :
    ∃ e < 512, ∃ l ∈ T0 k, g = trG k e * l :=
  (tstruct o hO).2.2.2 g hg

theorem T_inf_L {k : KD} (o : Ok k) (hO : Orb k) {g : GLm} (hg : g ∈ Tg k) (hL : g ∈ Lsub) :
    g ∈ T0 k := by
  obtain ⟨e, he, l, hl, rfl⟩ := T_decomp o hO hg
  have hcol : ((trG k e : GLm) : Mat12) *ᵥ e11 = e11 := by
    have h' : ((trG k e * l : GLm) : Mat12) *ᵥ e11 = e11 := hL
    rwa [Units.val_mul, col_mul_L _ (T0_le o hl).2.1] at h'
  have he0 : e = 0 := lam_inj o he (by norm_num) fun i _ => by
    have h0 := congrFun hcol i
    rw [mulVec_e11, val_trG o he] at h0
    rw [h0, ← val_trG o (by norm_num : 0 < 512), trG_zero o, Units.val_one, e11_apply,
      Matrix.one_apply]
  subst he0
  rw [trG_zero o, one_mul]
  exact hl

theorem nhat_le_L {k : KD} (o : Ok k) : Nhat k.LET ≤ Lsub := by
  obtain ⟨-, -, h23, -, -, -, -⟩ := kSetup_parts o.hS
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact (xh_facts o).2.1
  · have hv : ((yh k.LET : GLm) : Mat12) = toMat (letMat k.LET 2) := val_lu h23
    exact mem_Lsub_of fun i hi => by rw [hv]; exact chkLin_iff.1 o.ylin i hi

theorem stabN_le {k : KD} (o : Ok k) (hO : Orb k) {g : GLm} (hg : g ∈ Nhat k.LET)
    (hs : g ∈ Stab (thV k)) : g ∈ T0 k :=
  T_inf_L o hO ⟨hs, nhat_le_khat k.LET hg⟩ (nhat_le_L o hg)

theorem orbit_pts {k : KD} (o : Ok k) (hO : Orb k) {g : GLm} (hg : g ∈ Khat k.LET) :
    ∃ j < k.NOM, actS.act (thV k) g = ptVecs (k.PT j) := by
  classical
  obtain ⟨-, -, hBK, -⟩ := tstruct o hO
  by_contra hne
  push Not at hne
  have hO' := hO
  choose g' hgK hgA using hO'
  have h := card_mul_le_of_orbit actS (Khat k.LET) (thV k) (k.NOM + 1)
    (fun j => if h : j < k.NOM then g' j h else g)
    (fun j _ => by
      by_cases h : j < k.NOM
      · simp only [dite_eq_left h]; exact hgK j h
      · simp only [dite_eq_right h]; exact hg)
    (fun i hi j hj hij => by
      by_cases h1 : i < k.NOM <;> by_cases h2 : j < k.NOM
      · simp only [dite_eq_left h1, dite_eq_left h2] at hij
        rw [hgA i h1, hgA j h2] at hij
        exact pt_inj o h1 h2 hij
      · simp only [dite_eq_left h1, dite_eq_right h2] at hij
        rw [hgA i h1] at hij
        exact absurd hij.symm (hne i h1)
      · simp only [dite_eq_right h1, dite_eq_left h2] at hij
        rw [hgA j h2] at hij
        exact absurd hij (hne j h2)
      · omega)
  have h' : (k.NOM + 1) * Nat.card (Tg k) ≤ k.NOM * Nat.card (Tg k) := by
    rw [← hBK, ← card_khat o.hS o.hR o.hC o.hW o.hN]
    exact h
  have hpos : 0 < Nat.card (Tg k) := Nat.card_pos
  nlinarith

theorem lin_step {k : KD} (o : Ok k) (hO : Orb k) {τ : GLm} (hτ : τ ∈ Tg k) {TAU e : ℕ}
    (hTAU : (τ : Mat12) = toMat TAU) (he : e < 512)
    (hcol : TAU &&& colMask = lamT (k.LT e) &&& colMask) :
    ∃ l ∈ T0 k, τ = trG k e * l ∧ (l : Mat12) = toMat (TAU &&& linMask) := by
  obtain ⟨e', he', l, hl, rfl⟩ := T_decomp o hO hτ
  have hc : ∀ i : Fin 12, i ≠ 11 → toMat TAU i 11 = toMat (lamT (k.LT e)) i 11 := fun i hi => by
    have h1 := congrFun (congrFun (congrArg toMat hcol) i) 11
    rwa [toMat_land_colMask, toMat_land_colMask, ite_eq_left ⟨rfl, hi⟩, ite_eq_left ⟨rfl, hi⟩] at h1
  have hlL := (T0_le o hl).2.1
  have hlR := (T0_le o hl).2.2
  have hee : e' = e := lam_inj o he' he fun i hi => by
    have h1 := congrFun (col_mul_L ((trG k e' : GLm) : Mat12) hlL) i
    rw [mulVec_e11, mulVec_e11, ← Units.val_mul, hTAU, val_trG o he'] at h1
    rw [← h1, hc i hi]
  subst hee
  refine ⟨l, hl, rfl, ?_⟩
  ext i j
  rw [toMat_land_linMask]
  split_ifs with hij
  · obtain ⟨rfl, hi⟩ := hij
    rw [mem_Lsub_iff.1 hlL i, ite_eq_right hi]
  · rw [← hTAU, Units.val_mul, val_trG o he', mul_tr_apply (chkTrans_iff.1 (lam_trans o he'))
      (mem_Rsub_iff.1 hlR) hij]

structure GHyp (k : KD) {G : Type*} [Group G] (φ : Khat k.LET →* G) (x y t z : G) : Prop where
  hx : ∀ g : Khat k.LET, (g : GLm) = xh k.LET → φ g = x
  hy : ∀ g : Khat k.LET, (g : GLm) = yh k.LET → φ g = y
  hz : ∀ g : Khat k.LET, (g : GLm) = zh k.LET → φ g = z
  ht : t * t = 1
  r8 : rv (jv x y t z) (k.RT 8) = 1
  r9 : rv (jv x y t z) (k.RT 9) = 1

theorem comm_of_conj {G : Type*} [Group G] {t s : G} (ht : t * t = 1) (h : t * s * t = s) :
    Commute t s := by
  change t * s = s * t
  calc t * s = t * s * (t * t) := by rw [ht, mul_one]
    _ = s * t := by rw [← mul_assoc, h]

theorem psiGen_comm {k : KD} (o : Ok k) {G : Type*} [Group G] {φ : Khat k.LET →* G} {x y t z : G}
    (gh : GHyp k φ x y t z) {r sw sn sH h : ℕ} (hr : r < 12) (hsw : sw < 256 ^ sn)
    (hc : psiGenOK k.RT k.HT k.LET k.INV k.TH r sw sn sw sn sH h = true)
    (hrel : rv (jv x y t z) (k.RT r) = 1) {X : Mat12} (hX : toMat (hMat (k.HT sH)) * X = 1) :
    ∃ s : Khat k.LET, ((s : GLm) : Mat12) = toMat (hMat (k.HT sH)) ∧ Commute t (φ s) := by
  obtain ⟨hpr, hev, -, -, -⟩ := psiGen_spec hc
  obtain ⟨hg, hM⟩ := word_unit o.hS hev hX
  refine ⟨wordVal (kv k.LET) sw sn, hM.symm, comm_of_conj gh.ht ?_⟩
  have hfit : wW (k.RT r) < 256 ^ wN (k.RT r) :=
    CFSG.Certificates.J4KShape.wFits_spec (andB_eq_true.1 ((kSetup_more o.hS).2.1 r hr)).1
  have hINV : k.INV = invJ := (kRange_parts o.hR).1
  have hp : ∀ q < sn, lvE (jv x y t z) (CFSG.KJ4.lInv k.INV (CFSG.KJ4.wLet sw q)) =
      (lvE (jv x y t z) (CFSG.KJ4.wLet sw q))⁻¹ := by
    intro q hq
    have h255 : wLet sw q ≠ 255 := by rcases hg q hq with h | h | h | h | h | h <;> omega
    rw [hINV]
    have hl255 : CFSG.KJ4.lInv invJ (wLet sw q) ≠ 255 := by
      have := CFSG.Certificates.J4Words.lInv_invJ_lt (wLet sw q)
      omega
    simp only [lvE, ite_eq_right h255, ite_eq_right hl255]
    exact (jv_inv x y t z gh.ht _).2
  have key := CFSG.Certificates.J4Words.chkPsiRel_val (lvE (jv x y t z)) hfit hrel (by norm_num) hsw
    hp hpr
  have e4 : lvE (jv x y t z) 4 = t := by simp [lvE, jv]
  rw [e4, wv_eq_wordVal, ← phi_word gh.hx gh.hy gh.hz hg] at key
  exact key

theorem T0_comm {k : KD} (o : Ok k) {G : Type*} [Group G] {φ : Khat k.LET →* G} {x y t z : G}
    (gh : GHyp k φ x y t z) : ∀ g : Khat k.LET, (g : GLm) ∈ T0 k → Commute t (φ g) := by
  obtain ⟨-, h01, -, -, -, -, -⟩ := kSetup_parts o.hS
  obtain ⟨-, -, -, p8, e8, p9, hinv⟩ := kLam_parts o.hL
  have hx8 : toMat (hMat (k.HT k.hx)) * toMat (letMat k.LET 1) = 1 := by
    rw [e8]
    exact chkInv_sound h01
  obtain ⟨s8, hs8, c8⟩ := psiGen_comm o gh (by norm_num) (by norm_num) p8 gh.r8 hx8
  obtain ⟨s9, hs9, c9⟩ := psiGen_comm o gh (by norm_num) o.hsw p9 gh.r9 (chkInv_sound hinv)
  have ex : (s8 : GLm) = xh k.LET := Units.ext (by rw [hs8, e8]; exact (val_lu h01).symm)
  have ew : ((s9⁻¹ : Khat k.LET) : GLm) = w0u k := by
    rw [Subgroup.coe_inv]
    unfold w0u
    congr 1
    exact Units.ext (by rw [hs9]; exact (val_lu hinv).symm)
  have key : ∀ a (ha : a ∈ Subgroup.closure ({xh k.LET, w0u k} : Set GLm)) (hK : a ∈ Khat k.LET),
      Commute t (φ ⟨a, hK⟩) := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      intro hK
      rcases ha with rfl | rfl
      · have e : (⟨xh k.LET, hK⟩ : Khat k.LET) = s8 := Subtype.ext ex.symm
        rw [e]
        exact c8
      · have e : (⟨w0u k, hK⟩ : Khat k.LET) = s9⁻¹ := Subtype.ext ew.symm
        rw [e, map_inv]
        exact c9.inv_right
    | one =>
      intro hK
      have e : (⟨1, hK⟩ : Khat k.LET) = 1 := rfl
      rw [e, map_one]
      exact Commute.one_right t
    | mul a b ha hb iha ihb =>
      intro hK
      have e : (⟨a * b, hK⟩ : Khat k.LET) = ⟨a, T0_le_Khat o ha⟩ * ⟨b, T0_le_Khat o hb⟩ := rfl
      rw [e, map_mul]
      exact (iha _).mul_right (ihb _)
    | inv a ha iha =>
      intro hK
      have e : (⟨a⁻¹, hK⟩ : Khat k.LET) = (⟨a, T0_le_Khat o ha⟩ : Khat k.LET)⁻¹ := rfl
      rw [e, map_inv]
      exact (iha _).inv_right
  intro g hg
  exact key g hg g.2

theorem stabN_comm {k : KD} (o : Ok k) (hO : Orb k) {G : Type*} [Group G] {φ : Khat k.LET →* G}
    {x y t z : G} (gh : GHyp k φ x y t z) {g : Khat k.LET} (hgN : (g : GLm) ∈ Nhat k.LET)
    (hs : (g : GLm) ∈ Stab (thV k)) : Commute t (φ g) :=
  T0_comm o gh g (stabN_le o hO hgN hs)

theorem conj_t {G : Type*} [Group G] {t a c d : G} (ht : t * t = 1) (hc : Commute t c) :
    t * (a * (c⁻¹ * d * c)) * t = (t * a * t) * (c⁻¹ * (t * d * t) * c) := by
  have tt : ∀ X : G, t * (t * X) = X := fun X => by rw [← mul_assoc, ht, one_mul]
  have e : c⁻¹ * (t * d * t) * c = t * (c⁻¹ * d * c) * t := by
    have e1 : c⁻¹ * (t * d * t) * c = (c⁻¹ * t) * d * (t * c) := by simp only [mul_assoc]
    rw [e1, ← hc.inv_right.eq, hc.eq]
    simp only [mul_assoc]
  rw [e]
  simp only [mul_assoc, tt]

theorem lam_psi {k : KD} (o : Ok k) (hO : Orb k) {G : Type*} [Group G] {φ : Khat k.LET →* G}
    {x y t z : G} (gh : GHyp k φ x y t z) {ps : Khat k.LET} (hps : ((ps : GLm) : Mat12) = toMat k.PS1)
    (hψ : ∀ g : Khat k.LET, ((g : GLm) : Mat12) = toMat k.TR1 → t * φ g * t = φ ps) :
    ∀ e < 512, ∃ v : Khat k.LET, ((v : GLm) : Mat12) = toMat (lP' (k.LT e)) ∧
      ∀ u : Khat k.LET, (u : GLm) = trG k e → t * φ u * t = φ v := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro he
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · rcases lam_spec ((kLam_parts o.hL).2.1 0 (by norm_num)) with ⟨-, -, h⟩ | ⟨h, -⟩
    · refine ⟨1, by rw [h, toMat_ident12]; rfl, fun u hu => ?_⟩
      have e1 : u = 1 := Subtype.ext (by rw [hu, trG_zero o]; rfl)
      rw [e1, map_one, mul_one, gh.ht]
    · exact absurd rfl h
  obtain ⟨hp, hk, hT, hP⟩ := trG_succ o he (by omega)
  obtain ⟨vp, hvp, hvp'⟩ := ih _ hp (by omega)
  obtain ⟨-, -, c3, c4⟩ := cu_facts o hk
  obtain ⟨c, hcc⟩ : ∃ c : Khat k.LET, (c : GLm) = cu k (lK (k.LT e)) := ⟨⟨_, c3.2⟩, rfl⟩
  obtain ⟨tr, htr⟩ : ∃ tr : Khat k.LET, (tr : GLm) = tr1u k := ⟨⟨_, (tr1_facts o.hS).2⟩, rfl⟩
  obtain ⟨up, hup⟩ : ∃ up : Khat k.LET, (up : GLm) = trG k (lPar (k.LT e)) :=
    ⟨⟨_, lam_mem o _ (by omega)⟩, rfl⟩
  have hc : Commute t (φ c) := T0_comm o gh c (by rw [hcc]; exact T_inf_L o hO c3 c4)
  have htr' : ((tr : GLm) : Mat12) = toMat k.TR1 := by rw [htr]; exact (tr1_facts o.hS).1
  refine ⟨vp * (c⁻¹ * ps * c), ?_, fun u hu => ?_⟩
  · rw [hP, ← hvp, ← hps, ← hcc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  · have hu' : u = up * (c⁻¹ * tr * c) := Subtype.ext (by
      rw [hu, hT, ← hup, ← htr, ← hcc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv])
    rw [hu']
    simp only [map_mul, map_inv]
    rw [conj_t gh.ht hc, hvp' up hup, hψ tr htr']

theorem t_step {k : KD} (o : Ok k) (hO : Orb k) {G : Type*} [Group G] {φ : Khat k.LET →* G}
    {x y t z : G} (gh : GHyp k φ x y t z) {ps : Khat k.LET} (hps : ((ps : GLm) : Mat12) = toMat k.PS1)
    (hψ : ∀ g : Khat k.LET, ((g : GLm) : Mat12) = toMat k.TR1 → t * φ g * t = φ ps)
    {τ : Khat k.LET} {TAU e h : ℕ} (hτ : ((τ : GLm) : Mat12) = toMat TAU) (he : e < 512)
    (hin : inT k.TH (lamT (k.LT e)) h TAU = true) :
    ∃ l v : Khat k.LET, ((l : GLm) : Mat12) = toMat (TAU &&& linMask) ∧
      ((v : GLm) : Mat12) = toMat (lP' (k.LT e)) ∧ (l : GLm) ∈ T0 k ∧ t * φ τ * t = φ v * φ l := by
  obtain ⟨hpt, hcol⟩ := andB_eq_true.1 hin
  have hcol' : TAU &&& colMask = lamT (k.LT e) &&& colMask := beq_eq_true.1 hcol
  have hτT : (τ : GLm) ∈ Tg k := ⟨stab_of_chkPt (kSetup_more o.hS).1 hτ hpt, τ.2⟩
  obtain ⟨l, hl, hτl, hlv⟩ := lin_step o hO hτT hτ he hcol'
  obtain ⟨v, hv, hv'⟩ := lam_psi o hO gh hps hψ e he
  refine ⟨⟨l, T0_le_Khat o hl⟩, v, hlv, hv, hl, ?_⟩
  have e1 : τ = ⟨trG k e, lam_mem o e he⟩ * ⟨l, T0_le_Khat o hl⟩ := Subtype.ext hτl
  have hc := T0_comm o gh ⟨l, T0_le_Khat o hl⟩ hl
  rw [e1, map_mul, ← hv' ⟨trG k e, lam_mem o e he⟩ rfl]
  simp only [mul_assoc]
  rw [hc.eq]

end CFSG.KJ4.TStruct

end
