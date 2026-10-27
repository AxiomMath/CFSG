module

public import Certificates.Data.Kernel.HeisN
public import CFSG.LieType.SeitzGeneration.HeisSmallModel

public section

namespace CFSG.KC.HeisN

open CFSG.LieType.SeitzGeneration.HeisSmall

structure FK.Sound (K : FK) {F : Type} [Field F] (d : ℕ → F) : Prop where
  one_lt : 1 < K.p
  add_lt : ∀ a b, K.add a b < K.p
  neg_lt : ∀ a, K.neg a < K.p
  add : ∀ a b, d (K.add a b) = d a + d b
  mul : ∀ a b, d (K.mul a b) = d a * d b
  neg : ∀ a, d (K.neg a) = -d a
  zero : d 0 = 0
  one : d 1 = 1
  inj : ∀ a b, a < K.p → b < K.p → d a = d b → a = b
  surj : ∀ x, ∃ a < K.p, d a = x

namespace FK

variable {K : FK} {F : Type} [Field F] [NoCubeRoot F] {d : ℕ → F}

@[expose] def dec (K : FK) (d : ℕ → F) (x : ℕ) : QExt F := ⟨d (x % K.p), d (x / K.p)⟩

@[expose] def toL (K : FK) (d : ℕ → F) (A : M3 ℕ) : M3 (QExt F) :=
  ⟨dec K d A.a00, dec K d A.a01, dec K d A.a02, dec K d A.a10, dec K d A.a11, dec K d A.a12,
    dec K d A.a20, dec K d A.a21, dec K d A.a22⟩

section
variable (hK : K.Sound d)
include hK

theorem p_pos : 0 < K.p := by have := hK.one_lt; omega

theorem pack_mod {r : ℕ} (i : ℕ) (hr : r < K.p) : (r + K.p * i) % K.p = r := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem pack_div {r : ℕ} (i : ℕ) (hr : r < K.p) : (r + K.p * i) / K.p = i := by
  rw [Nat.add_mul_div_left _ _ (p_pos hK), Nat.div_eq_of_lt hr, Nat.zero_add]

theorem dec_pack {r : ℕ} (i : ℕ) (hr : r < K.p) : dec K d (r + K.p * i) = ⟨d r, d i⟩ := by
  rw [dec, pack_mod hK i hr, pack_div hK i hr]

theorem pack_lt {r i : ℕ} (hr : r < K.p) (hi : i < K.p) : r + K.p * i < K.p * K.p := by
  have : K.p * i + K.p ≤ K.p * K.p := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hi
  omega

theorem dec_zero : dec K d 0 = 0 := by
  rw [dec, Nat.zero_mod, Nat.zero_div, hK.zero]
  rfl

theorem dec_one : dec K d 1 = 1 := by
  rw [dec, Nat.mod_eq_of_lt hK.one_lt, Nat.div_eq_of_lt hK.one_lt, hK.zero, hK.one]
  rfl

theorem dec_eAdd (x y : ℕ) : dec K d (K.eAdd x y) = dec K d x + dec K d y := by
  rw [eAdd, dec_pack hK _ (hK.add_lt _ _)]
  ext <;> simp [hK.add, dec]

theorem dec_eNeg (x : ℕ) : dec K d (K.eNeg x) = -dec K d x := by
  rw [eNeg, dec_pack hK _ (hK.neg_lt _)]
  ext <;> simp [hK.neg, dec]

theorem dec_eSub (x y : ℕ) : dec K d (K.eSub x y) = dec K d x - dec K d y := by
  rw [eSub, dec_eAdd hK, dec_eNeg hK, sub_eq_add_neg]

theorem dec_eMul (x y : ℕ) : dec K d (K.eMul x y) = dec K d x * dec K d y := by
  simp only [eMul]
  rw [dec_pack hK _ (hK.add_lt _ _)]
  ext <;> simp [hK.add, hK.mul, hK.neg, dec, sub_eq_add_neg]

theorem dec_ePow (x : ℕ) (n : ℕ) : dec K d (K.ePow x n) = dec K d x ^ n := by
  induction n with
  | zero => rw [ePow, pow_zero, dec_one hK]
  | succ n ih => rw [ePow, dec_eMul hK, ih, pow_succ]

theorem eAdd_lt (x y : ℕ) : K.eAdd x y < K.p * K.p := pack_lt hK (hK.add_lt _ _) (hK.add_lt _ _)

theorem dec_inj {x y : ℕ} (hx : x < K.p * K.p) (hy : y < K.p * K.p)
    (h : dec K d x = dec K d y) : x = y := by
  have hp := p_pos hK
  have h1 := hK.inj _ _ (Nat.mod_lt x hp) (Nat.mod_lt y hp) (congrArg QExt.re h)
  have h2 := hK.inj _ _ (Nat.div_lt_of_lt_mul hx) (Nat.div_lt_of_lt_mul hy) (congrArg QExt.im h)
  rw [← Nat.mod_add_div x K.p, ← Nat.mod_add_div y K.p, h1, h2]

theorem dec_surj (z : QExt F) : ∃ x < K.p * K.p, dec K d x = z := by
  obtain ⟨r, hr, hdr⟩ := hK.surj z.re
  obtain ⟨i, hi, hdi⟩ := hK.surj z.im
  exact ⟨r + K.p * i, pack_lt hK hr hi, by rw [dec_pack hK i hr, hdr, hdi]⟩

theorem toL_mOne : toL K d mOne = 1 := by
  simp only [toL, mOne, dec_zero hK, dec_one hK]
  rfl

theorem toL_mMul (A B : M3 ℕ) : toL K d (K.mMul A B) = toL K d A * toL K d B := by
  rw [M3.mul_def]
  simp only [toL, mMul, dec_eAdd hK, dec_eMul hK]

theorem toL_mSmul (c : ℕ) (A : M3 ℕ) : toL K d (K.mSmul c A) = M3.smul (dec K d c) (toL K d A) := by
  simp only [toL, mSmul, M3.smul, dec_eMul hK]

theorem toL_mDet (A : M3 ℕ) : dec K d (K.mDet A) = (toL K d A).det := by
  simp only [mDet, M3.det, toL, dec_eAdd hK, dec_eSub hK, dec_eMul hK]

theorem toL_mPowTr (q : ℕ) (A : M3 ℕ) :
    toL K d (K.mPowTr q A) = ((toL K d A).map (· ^ q)).transpose := by
  simp only [toL, mPowTr, M3.map, M3.transpose, dec_ePow hK]

end

theorem mEq_sound {A B : M3 ℕ} (h : mEq A B = true) : A = B := by
  simp only [mEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact M3.ext h0 h1 h2 h3 h4 h5 h6 h7 h8

section
variable (hK : K.Sound d)
include hK

theorem linesN_toL (w : ℕ) : (K.linesN w).map (toL K d) = lineList (dec K d w) := by
  have hd : toL K d ⟨1, 0, 0, 0, w, 0, 0, 0, K.ePow w 2⟩ = dM3 (dec K d w) := by
    simp only [toL, dM3, dec_zero hK, dec_one hK, dec_ePow hK]
  have hs : toL K d ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩ = (sM3 : M3 (QExt F)) := by
    simp only [toL, sM3, dec_zero hK, dec_one hK]
  simp only [linesN, List.map_cons, List.map_nil, lineList, toL_mMul hK, hd, hs]

theorem genOkN_sound (q w : ℕ) (G : M3 ℕ) (h : K.genOkN q w G = true) :
    GenOk q (dec K d w) (toL K d G) := by
  simp only [genOkN, Bool.and_eq_true, Nat.beq_eq, List.any_eq_true] at h
  obtain ⟨⟨hdet, hu⟩, M, hM, hc⟩ := h
  refine ⟨?_, ?_, toL K d M, ?_, dec K d (K.cGuess (K.mMul G M) (K.mMul M G)), ?_⟩
  · rw [← toL_mDet hK, hdet, dec_one hK]
  · rw [← toL_mPowTr hK, ← toL_mMul hK, mEq_sound hu, toL_mOne hK]
  · rw [← linesN_toL hK]
    exact List.mem_map_of_mem hM
  · have e := congrArg (toL K d) (mEq_sound hc)
    rw [toL_mMul hK, toL_mSmul hK, toL_mMul hK] at e
    exact e

end

theorem getD_map {α β : Type} (f : α → β) (l : List α) (i : ℕ) (x : α) :
    (l.map f).getD i (f x) = f (l.getD i x) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

section
variable (hK : K.Sound d)
include hK

theorem evalN_toL (letters : List (M3 ℕ)) (w : List ℕ) :
    evalW (letters.map (toL K d)) w = toL K d (K.evalN letters w) := by
  induction w with
  | nil => rw [evalW, evalN, toL_mOne hK]
  | cons i w ih => rw [evalW, evalN, ih, toL_mMul hK, ← toL_mOne hK, getD_map]

theorem evalsN_toL (Ls : List (M3 ℕ)) (ws : List (List ℕ)) :
    ws.map (evalW (Ls.map (toL K d))) = (ws.map (K.evalN Ls)).map (toL K d) := by
  rw [List.map_map]
  exact List.map_congr_left fun w _ => evalN_toL hK Ls w

theorem mem_of_testBit (q : ℕ) (vals : List (M3 ℕ)) (k : ℕ) (h : (K.bitsN q vals).testBit k) :
    ∃ V ∈ vals, K.keyN q V = some k := by
  induction vals with
  | nil => simp [bitsN] at h
  | cons V vs ih =>
    simp only [bitsN] at h
    split at h
    · rename_i k' hk'
      rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft] at h
      rcases h with h | h
      · obtain ⟨W, hW, hk⟩ := ih h
        exact ⟨W, List.mem_cons_of_mem _ hW, hk⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero] at h
        refine ⟨V, List.mem_cons_self, ?_⟩
        rw [hk']
        congr 1
        omega
    · obtain ⟨W, hW, hk⟩ := ih h
      exact ⟨W, List.mem_cons_of_mem _ hW, hk⟩

theorem toL_of_keyN (q : ℕ) {V : M3 ℕ} {a b : ℕ} (ha : a < K.p * K.p) (hb : b < K.p * K.p)
    (h : K.keyN q V = some (a + K.p * K.p * b)) :
    toL K d V = blockM3 q (dec K d a) (dec K d b) := by
  unfold keyN at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
    have hk := Option.some.inj h
    have hp : 0 < K.p * K.p := by omega
    have e1 : V.a00 = a := by
      have := congrArg (· % (K.p * K.p)) hk
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt ha] at this
      exact this
    have e2 : V.a01 = b := by
      have := congrArg (· / (K.p * K.p)) hk
      simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h0, Nat.div_eq_of_lt ha] at this
      omega
    simp only [toL, blockM3, h2, h3, h4, h5, h6, h7, h8, dec_eNeg hK, dec_ePow hK, dec_zero hK,
      dec_one hK, e1, e2]
  · exact absurd h (by simp)

theorem coverN_sound (q : ℕ) (vals : List (M3 ℕ)) (h : K.coverN q vals = true) :
    CoverOk q (vals.map (toL K d)) := by
  intro a b hab
  obtain ⟨x, hx, rfl⟩ := dec_surj hK a
  obtain ⟨y, hy, rfl⟩ := dec_surj hK b
  simp only [coverN, List.all_eq_true, List.mem_map, List.mem_range] at h
  have h1 := h (x, K.eMul x (K.ePow x q)) ⟨x, hx, rfl⟩ (y, K.eMul y (K.ePow y q)) ⟨y, hy, rfl⟩
  have h1p : 1 < K.p * K.p := by
    have h1 := hK.one_lt
    have h2 : K.p ≤ K.p * K.p := Nat.le_mul_self _
    omega
  have hn : K.eAdd (K.eMul x (K.ePow x q)) (K.eMul y (K.ePow y q)) = 1 := by
    refine dec_inj hK (eAdd_lt hK _ _) h1p ?_
    rw [dec_eAdd hK, dec_eMul hK, dec_eMul hK, dec_ePow hK, dec_ePow hK, dec_one hK, hab]
  dsimp only at h1
  rw [hn] at h1
  rw [show Nat.beq 1 1 = true from rfl, Bool.not_true, Bool.false_or] at h1
  obtain ⟨V, hV, hk⟩ := mem_of_testBit hK q vals _ h1
  rw [← toL_of_keyN hK q hx hy hk]
  exact List.mem_map_of_mem hV

theorem heisN_sound (q w : ℕ) (raw ws₁ ws₂ : List (List ℕ)) [DecidableEq F] [Fintype F]
    (h : K.heisN q w raw ws₁ ws₂ = true) :
    heisCheck q (dec K d w) ((raw.map matN).map (toL K d)) ws₁ ws₂ = true := by
  simp only [heisN, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hg, hc⟩ := h
  unfold heisCheck coverBool
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun G' hG' => ?_, ?_⟩
  · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hG'
    exact decide_eq_true (genOkN_sound hK q w G (hg G hG))
  · refine decide_eq_true ?_
    rw [evalsN_toL hK, evalsN_toL hK]
    exact coverN_sound hK q _ hc

end

end FK

theorem fkP_sound (p : ℕ) [Fact p.Prime] : (fkP p).Sound (fun n : ℕ => (n : ZMod p)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨(Fact.out : p.Prime).one_lt, fun a b => Nat.mod_lt _ hp, fun a => Nat.mod_lt _ hp,
    ?_, ?_, ?_, Nat.cast_zero, Nat.cast_one, ?_, ?_⟩
  · intro a b
    simp [fkP]
  · intro a b
    simp [fkP]
  · intro a
    simp only [fkP, ZMod.natCast_mod]
    rw [Nat.cast_sub (Nat.mod_lt a hp).le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
  · intro a b ha hb h
    change a < p at ha
    change b < p at hb
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro x
    exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩

end CFSG.KC.HeisN
