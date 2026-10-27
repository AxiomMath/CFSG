module

public import Certificates.Data.Kernel.J4TreeColPair
public import CFSG.Certificates.Kernel.J4Q.Rep
public import CFSG.Sporadic.J4.QT2LocGenLem
import all CFSG.Certificates.Kernel.J4Q.Rep

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

section RankPf

open CFSG.KS.PackFld

private noncomputable def rv (g : Nat → Nat) (i : Nat) : Fin 112 → ZMod 2 :=
  fun j => if (g i).testBit j.val then 1 else 0

private noncomputable def rkS (g : Nat → Nat) (t : Nat) : Nat :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (rv g '' {i | i < t}))

private theorem img_succ (g : Nat → Nat) (t : Nat) :
    rv g '' {i | i < t + 1} = insert (rv g t) (rv g '' {i | i < t}) := by
  have e : {i | i < t + 1} = insert t {i | i < t} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    omega
  rw [e, Set.image_insert_eq]

private theorem rkS_congr {g g' : Nat → Nat} {t : Nat} (h : ∀ i < t, rv g i = rv g' i) :
    rkS g t = rkS g' t := by
  unfold rkS
  rw [Set.image_congr (s := {i | i < t}) fun i hi => h i hi]

private theorem finrank_insert_pivot {S : Set (Fin 112 → ZMod 2)} {w : Fin 112 → ZMod 2}
    (pp : Fin 112) (hw : w pp = 1) (hS : ∀ u ∈ S, u pp = 0) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (insert w S)) =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) S) + 1 := by
  have hle : Submodule.span (ZMod 2) S ≤ LinearMap.ker (LinearMap.proj (R := ZMod 2)
      (φ := fun _ : Fin 112 => ZMod 2) pp) := by
    rw [Submodule.span_le]
    intro u hu
    simp [hS u hu]
  have hw0 : w ≠ 0 := fun h => by
    rw [h] at hw
    simp at hw
  have hdis : Submodule.span (ZMod 2) {w} ⊓ Submodule.span (ZMod 2) S = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
    have h1 := hle hx2
    simp [LinearMap.mem_ker, hw] at h1
    simp [h1]
  rw [Submodule.span_insert]
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 2) {w})
    (Submodule.span (ZMod 2) S)
  rw [hdis, finrank_bot, add_zero, finrank_span_singleton hw0] at h2
  omega

private theorem lowBit_spec {v : Nat} (hv : v ≠ 0) :
    ∃ p, lowBitJ v = 2 ^ p ∧ v.testBit p = true ∧ ∀ j < p, v.testBit j = false := by
  classical
  have hex := Nat.exists_testBit_of_ne_zero hv
  let p := Nat.find hex
  have hp : v.testBit p = true := Nat.find_spec hex
  have hlow : ∀ j < p, v.testBit j = false := fun j hj => by
    have := Nat.find_min hex hj
    simpa using this
  refine ⟨p, ?_, hp, hlow⟩
  have hmod : v % 2 ^ (p + 1) = 2 ^ p := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases hj : j < p
    · rw [hlow j hj]
      simp
      omega
    · by_cases hj' : j = p
      · subst hj'
        simp [hp]
      · have : ¬ j < p + 1 := by omega
        simp [this]
        omega
  have hdv : v = 2 ^ (p + 1) * (v / 2 ^ (p + 1)) + 2 ^ p := by
    have := Nat.div_add_mod v (2 ^ (p + 1))
    omega
  have hp1 : (2 : Nat) ^ p < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpos : 0 < (2 : Nat) ^ p := Nat.two_pow_pos p
  obtain ⟨q, hq⟩ : ∃ q, v = 2 ^ (p + 1) * q + 2 ^ p := ⟨_, hdv⟩
  have hdv1 : v - 1 = 2 ^ (p + 1) * q + (2 ^ p - 1) := by omega
  apply Nat.eq_of_testBit_eq
  intro j
  unfold lowBitJ
  change (v &&& (v ^^^ (v - 1))).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_xor, hdv1, hq]
  rw [Nat.testBit_two_pow_mul_add _ hp1, Nat.testBit_two_pow_mul_add _ (by omega : 2 ^ p - 1 < 2 ^ (p + 1)), Nat.testBit_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hj : j < p + 1
  · simp only [hj, ↓reduceIte, Nat.testBit_two_pow]
    by_cases hjp : j = p
    · subst hjp
      simp
    · have : p ≠ j := fun e => hjp e.symm
      simp [this]
  · simp only [hj, ↓reduceIte]
    have : p ≠ j := by omega
    simp [this]

private theorem fld_zero_eq {X : Nat} {g : Nat → Nat} (hX : Fld 128 X g)
    (hg : ∀ i, g i < 2 ^ 112) (h0 : X = 0) (i : Nat) : g i = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 128
  · rw [← hX i k hk, h0]
    simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg i)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp

private theorem gRank_fold {G : Mats} (hc : G.c = rep 1 128 112) (hrm : G.rm = 2 ^ 112 - 1) :
    ∀ t ≤ 112, ∀ (X : Nat) (g : Nat → Nat) (rk : Nat), Fld 128 X g → (∀ i, g i < 2 ^ 112) →
      (∀ i, t ≤ i → g i = 0) →
      Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ rk => rk)
        (fun t ih X rk =>
          Bool.rec (motive := fun _ => Nat)
            (strictN (rowJ G.rm X t) fun v =>
              strictN (Nat.mod X (Nat.shiftLeft (nat_lit 1) (Nat.mul t (nat_lit 128)))) fun L =>
                Bool.rec (motive := fun _ => Nat)
                  (strictN (Nat.xor L (Nat.land
                      (Nat.mul (Nat.land (Nat.div L (lowBitJ v)) G.c) G.rm) (Nat.mul v G.c)))
                    fun L' => ih L' (Nat.succ rk))
                  (ih L rk) (Nat.beq v 0))
            rk (Nat.beq X 0)) t X rk = rk + rkS g t := by
  intro t
  induction t with
  | zero =>
    intro _ X g rk _ _ _
    have e : rv g '' {i | i < 0} = ∅ := by
      ext x
      simp
    change rk = rk + rkS g 0
    unfold rkS
    rw [e, Submodule.span_empty, finrank_bot]
    rfl
  | succ t ih =>
    intro ht X g rk hX hg hz
    simp only [Nat.rec_add_one]
    by_cases hX0 : X = 0
    · have hb : Nat.beq X 0 = true := by rw [hX0]; rfl
      rw [hb]
      change rk = rk + rkS g (t + 1)
      have hz' : ∀ i, rv g i = 0 := fun i => by
        funext j
        simp [rv, fld_zero_eq hX hg hX0 i]
      have e : rv g '' {i | i < t + 1} ⊆ {0} := by
        rintro _ ⟨i, _, rfl⟩
        exact hz' i
      unfold rkS
      rw [Submodule.span_eq_bot.2 (fun x hx => e hx), finrank_bot]
      rfl
    have hb : Nat.beq X 0 = false := by
      cases h : Nat.beq X 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hX0
    rw [hb]
    dsimp only
    rw [CFSG.KC.J4Q.strictN_eq, CFSG.KC.J4Q.strictN_eq]
    have hv : rowJ G.rm X t = g t := by
      rw [hrm]
      apply Nat.eq_of_testBit_eq
      intro j
      change ((X >>> (t * 128)) &&& (2 ^ 112 - 1)).testBit j = _
      rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
      by_cases hj : j < 112
      · rw [show t * 128 + j = 128 * t + j by ring, hX t j (by omega)]
        simp [hj]
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg t)
          (Nat.pow_le_pow_right (by omega) (by omega)))]
        simp [hj]
    set gL : Nat → Nat := fun i => if i < t then g i else 0 with hgL
    have hL : Fld 128 (Nat.mod X (Nat.shiftLeft 1 (Nat.mul t 128))) gL := by
      intro i k hk
      change (X % (1 <<< (t * 128))).testBit (128 * i + k) = _
      rw [Nat.one_shiftLeft, Nat.testBit_mod_two_pow, hX i k hk, hgL]
      by_cases hi : i < t
      · have : 128 * i + k < t * 128 := by omega
        simp [hi, this]
      · have : ¬ 128 * i + k < t * 128 := by omega
        simp [hi, this]
    have hgL' : ∀ i, gL i < 2 ^ 112 := fun i => by
      simp only [hgL]
      split
      · exact hg i
      · positivity
    have hgLz : ∀ i, t ≤ i → gL i = 0 := fun i hi => by
      simp only [hgL]
      exact if_neg (by omega)
    have hrvL : ∀ i < t, rv gL i = rv g i := fun i hi => by
      funext j
      unfold rv
      simp only [hgL, if_pos hi]
    generalize Nat.mod X (Nat.shiftLeft 1 (Nat.mul t 128)) = L at hL
    rw [hv]
    by_cases hv0 : g t = 0
    · have hb' : Nat.beq (g t) 0 = true := by rw [hv0]; rfl
      rw [hb']
      dsimp only
      rw [ih (by omega) L gL rk hL hgL' hgLz]
      congr 1
      rw [rkS_congr hrvL]
      unfold rkS
      have hw : rv g t = 0 := by
        funext j
        simp [rv, hv0]
      rw [img_succ, hw, Submodule.span_insert_zero]
    have hb' : Nat.beq (g t) 0 = false := by
      cases h : Nat.beq (g t) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hv0
    rw [hb']
    dsimp only
    rw [CFSG.KC.J4Q.strictN_eq]
    obtain ⟨p, hlb, hpt, -⟩ := lowBit_spec hv0
    have hp112 : p < 112 := by
      by_contra hp
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg t)
        (Nat.pow_le_pow_right (by omega) (by omega)))] at hpt
      exact Bool.false_ne_true hpt
    rw [hlb]
    have hcF := (fld_bsum (h := fun _ => 1) (fun _ => by omega) 112).1
    rw [← c_eq] at hcF
    have hx : Fld 128 (Nat.land (Nat.div L (2 ^ p)) (rep 1 128 112)) (fun i => if i < 112 then
        (if (gL i).testBit p then 1 else 0) else 0) := by
      intro i j hj
      have hc' := hcF i j hj
      dsimp only at hc' ⊢
      change ((L / 2 ^ p) &&& rep 1 128 112).testBit (128 * i + j) = _
      rw [Nat.testBit_and, Nat.testBit_div_two_pow, hc']
      by_cases hi : i < 112
      · rw [ite_eq_left hi, ite_eq_left hi, one_bit]
        by_cases hj0 : j = 0
        · subst hj0
          rw [Nat.add_zero, hL i p (by omega)]
          cases (gL i).testBit p <;> simp
        · cases (gL i).testBit p <;> simp [hj0, one_bit]
      · rw [ite_eq_right hi, ite_eq_right hi]
        simp
    have hxe := fld_eq (by omega : 0 < 128) hx
      (fld_bsum (h := fun i : Nat => if (gL i).testBit p then 1 else 0)
        (fun i => Nat.lt_of_le_of_lt (by split <;> omega) (by omega : 1 < 2 ^ 128)) 112).1
    have hxb : ∀ i : Nat, (if (gL i).testBit p then 1 else 0) * (2 ^ 112 - 1) < 2 ^ 128 := by
      intro i
      cases (gL i).testBit p <;> simp
    have h1 : Fld 128 (Nat.mul (Nat.land (Nat.div L (2 ^ p)) (rep 1 128 112)) (2 ^ 112 - 1))
        (fun i => if i < 112 then
          (if (gL i).testBit p then 1 else 0) * (2 ^ 112 - 1) else 0) := by
      change Fld 128 ((Nat.land (Nat.div L (2 ^ p)) (rep 1 128 112)) * (2 ^ 112 - 1)) _
      rw [hxe, bsum_mul]
      exact (fld_bsum hxb 112).1
    have h2 : Fld 128 (Nat.mul (g t) (rep 1 128 112))
        (fun i => if i < 112 then 1 * g t else 0) := by
      change Fld 128 (g t * rep 1 128 112) _
      rw [c_eq, Nat.mul_comm, bsum_mul]
      exact (fld_bsum (fun _ => Nat.lt_of_lt_of_le (by have := hg t; omega)
        (Nat.pow_le_pow_right (by omega) (by omega : 112 ≤ 128))) 112).1
    set g' : Nat → Nat := fun i => if i < t then g i ^^^ (if (g i).testBit p then g t else 0)
      else 0 with hg'
    have hL' : Fld 128 (Nat.xor L (Nat.land (Nat.mul (Nat.land (Nat.div L (2 ^ p))
        G.c) G.rm) (Nat.mul (g t) G.c))) g' := by
      rw [hc, hrm]
      refine fld_congr (fld_xor hL (fld_and h1 h2)) fun i => ?_
      rw [hg', hgL]
      by_cases hi : i < t
      · have hi' : i < 112 := by omega
        simp only [hi, hi', ↓reduceIte]
        cases (g i).testBit p
        · simp
        · simp only [↓reduceIte, Nat.one_mul]
          rw [Nat.and_comm, Nat.and_two_pow_sub_one_of_lt_two_pow (hg t)]
      · simp only [hi, ↓reduceIte, Nat.zero_testBit, Bool.false_eq_true, Nat.zero_mul,
          Nat.zero_and, Nat.zero_xor]
        split <;> simp
    have hg'b : ∀ i, g' i < 2 ^ 112 := fun i => by
      simp only [hg']
      split
      · refine Nat.xor_lt_two_pow (hg i) ?_
        split
        · exact hg t
        · positivity
      · positivity
    have hg'z : ∀ i, t ≤ i → g' i = 0 := fun i hi => by
      simp only [hg']
      exact if_neg (by omega)
    rw [ih (by omega) _ g' (Nat.succ rk) hL' hg'b hg'z]
    have hwp : rv g t ⟨p, hp112⟩ = 1 := by
      unfold rv
      simp [hpt]
    have hrv' : ∀ i < t, rv g' i = rv g i + rv g i ⟨p, hp112⟩ • rv g t := fun i hi => by
      funext j
      have e : g' i = g i ^^^ (if (g i).testBit p then g t else 0) := by
        simp only [hg', if_pos hi]
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      unfold rv
      rw [e, Nat.testBit_xor]
      cases hb1 : (g i).testBit p <;> cases hb2 : (g i).testBit j <;>
        cases hb3 : (g t).testBit j <;> simp [hb1, hb2, hb3]
      all_goals decide
    have hU'p : ∀ u ∈ rv g' '' {i | i < t}, u ⟨p, hp112⟩ = 0 := by
      rintro _ ⟨i, hi, rfl⟩
      rw [hrv' i hi, Pi.add_apply, Pi.smul_apply, hwp, smul_eq_mul, mul_one]
      unfold rv
      split <;> decide
    have hspan : Submodule.span (ZMod 2) (insert (rv g t) (rv g '' {i | i < t})) =
        Submodule.span (ZMod 2) (insert (rv g t) (rv g' '' {i | i < t})) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ (rfl | ⟨i, hi, rfl⟩)
        · exact Submodule.subset_span (Set.mem_insert _ _)
        · have e : rv g i = rv g' i - rv g i ⟨p, hp112⟩ • rv g t := by
            rw [hrv' i hi]
            abel
          rw [e]
          exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      · rw [Submodule.span_le]
        rintro _ (rfl | ⟨i, hi, rfl⟩)
        · exact Submodule.subset_span (Set.mem_insert _ _)
        · rw [hrv' i hi]
          exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
    unfold rkS
    rw [img_succ, hspan, finrank_insert_pivot ⟨p, hp112⟩ hwp hU'p]
    omega

end RankPf

theorem gRank_spec {G : Mats} (hc : G.c = rep 1 128 112) (hrm : G.rm = 2 ^ 112 - 1) {Y : Array V2}
    (hY : WfA Y) : gRank G (encR Y) = (rowsMatrix Y).rank := by
  have hYw : ∀ i (h : i < Y.size), Y[i].wf = true := fun i h => Array.all_eq_true.1 hY.2 i h
  set g : Nat → Nat := fun i => if i < 112 then v2N (Y[i]?.getD V2.zero) else 0 with hgdef
  have hX : CFSG.KS.PackFld.Fld 128 (encR Y) g := encR_fld Y
  have hg : ∀ i, g i < 2 ^ 112 := fun i => by
    simp only [hgdef]
    split
    · exact v2N_lt112 (wf_getD hYw i)
    · positivity
  have hz : ∀ i, 112 ≤ i → g i = 0 := fun i hi => by
    simp only [hgdef]
    exact if_neg (by omega)
  have h := gRank_fold hc hrm 112 le_rfl (encR Y) g 0 hX hg hz
  have hset : rv g '' {i | i < 112} = Set.range (rowsMatrix Y) := by
    have hrow : ∀ (i : Nat) (hi : i < 112), rowsMatrix Y ⟨i, hi⟩ = rv g i := fun i hi => by
      funext j
      rw [rowsMatrix_apply, V2.toVec_apply, testBit_V2 _ (by omega : j.val < 128)]
      simp only [rv, hgdef, if_pos hi]
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, hrow i hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, (hrow i.val i.isLt).symm⟩
  unfold gRank
  rw [h, Nat.zero_add, Matrix.rank_eq_finrank_span_row]
  unfold rkS
  rw [hset]
  rfl

theorem fixDim_add_rank (A : Matrix (Fin 112) (Fin 112) (ZMod 2)) :
    QT2.fixDim (A + 1) + A.rank = 112 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : QT2.fixPhi (A + 1) = A.vecMulLinear := by
    unfold QT2.fixPhi
    rw [add_sub_cancel_right]
  have h := LinearMap.finrank_range_add_finrank_ker (QT2.fixPhi (A + 1))
  rw [Module.finrank_fin_fun] at h
  have hr : Module.finrank (ZMod 2) (LinearMap.range (QT2.fixPhi (A + 1))) = A.rank := by
    have e2 : A.vecMulLinear = A.transpose.mulVecLin := by
      apply LinearMap.ext
      intro x
      simp [Matrix.mulVec_transpose]
    rw [e, e2, ← Matrix.rank_transpose A]
    rfl
  unfold QT2.fixDim
  omega

theorem packMs_cons (x : Nat) (l : List Nat) :
    packMs (x :: l) = Nat.lor x (Nat.shiftLeft (packMs l) 14336) := by
  change strictN (packMs l) (fun p => Nat.lor x (Nat.shiftLeft p (nat_lit 14336))) = _
  rw [strictN_eq]

set_option exponentiation.threshold 16384 in
theorem testBit_getP (P m i : Nat) :
    (getP P m).testBit i = (decide (i < 14336) && P.testBit (m * 14336 + i)) := by
  have e : getP P m = (P >>> (m * 14336)) &&& (1 <<< 14336 - 1) := rfl
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

set_option exponentiation.threshold 16384 in
theorem testBit_packMs : ∀ (l : List Nat), (∀ x ∈ l, x < 1 <<< 14336) → ∀ (m i : Nat),
    i < 14336 → (packMs l).testBit (m * 14336 + i) = (l.getD m 0).testBit i
  | [], _, m, i, _ => by
    change (0 : Nat).testBit _ = _
    simp
  | x :: l, hl, m, i, hi => by
    rw [packMs_cons]
    change (x ||| (packMs l <<< 14336)).testBit _ = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    have hx := hl x List.mem_cons_self
    rw [Nat.one_shiftLeft] at hx
    rcases m with _ | m
    · have h1 : ¬ (14336 ≤ i) := by omega
      simp [h1]
    · have h1 : (m + 1) * 14336 + i ≥ 14336 := by omega
      have h2 : x.testBit ((m + 1) * 14336 + i) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h1))
      have h3 : (m + 1) * 14336 + i - 14336 = m * 14336 + i := by omega
      rw [h2, Bool.false_or, h3, testBit_packMs l (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        m i hi]
      simp [h1]

set_option exponentiation.threshold 16384 in
theorem getP_packMs {l : List Nat} (hl : ∀ x ∈ l, x < 1 <<< 14336) (m : Nat) :
    getP (packMs l) m = l.getD m 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_getP]
  by_cases hi : i < 14336
  · rw [testBit_packMs l hl m i hi]
    simp [hi]
  · have hlt : l.getD m 0 < 1 <<< 14336 := by
      rcases Nat.lt_or_ge m l.length with h | h
      · rw [List.getD_eq_getElem _ _ h]
        exact hl _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h, Nat.one_shiftLeft]
        exact Nat.two_pow_pos _
    rw [Nat.one_shiftLeft] at hlt
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega)
      (by omega : 14336 ≤ i)))]
    simp [hi]

end CFSG.KC.J4TreeCol

end
