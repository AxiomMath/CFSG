
module

public import Certificates.Data.Kernel.SpinOrbK
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverAltBase
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KC.SpinOrb

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.LQT
open CFSG.ComponentClassification.Sol76.Sig CFSG.ComponentClassification.Sol76.Sig.GSYard02
open CFSG.Alternating.Multipliers.Spin
open Subgroup Matrix
open scoped commutatorElement

@[expose] noncomputable def gamMat (N g : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun r c => if gP g r = (c : ℕ) then (if gS g r = 1 then -1 else 1) else 0

@[expose] noncomputable def gamM (N : ℕ) (G : List ℕ) (k : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  gamMat N (G.getD k 0)

@[expose] noncomputable def colM (N : ℕ) (R : List (ℕ × ℕ)) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun r j =>
    ((lane 64 (R.getD j (0, 0)).1 r : ℕ) : ℚ) - ((lane 64 (R.getD j (0, 0)).2 r : ℕ) : ℚ)

@[expose] noncomputable def vecT (N b : ℕ) : Fin N → ℚ :=
  fun r => (((lane 64 b r : ℕ) : ℚ) - 128) / 4

@[expose] noncomputable def sig (S Sg l k : ℕ) : ℕ := lane 8 (lane (8 * S) Sg l) k

@[expose] noncomputable def parOf (Tr k : ℕ) : ℕ := Nat.land (lane 16 Tr k) 255

@[expose] noncomputable def labOf (Tr k : ℕ) : ℕ := Nat.shiftRight (lane 16 Tr k) 8

@[expose] noncomputable def kp (K idx : ℕ) : ℕ := Nat.land (lane 32 K idx) 255
@[expose] noncomputable def kq (K idx : ℕ) : ℕ := Nat.land (Nat.shiftRight (lane 32 K idx) 8) 255
@[expose] noncomputable def kr (K idx : ℕ) : ℕ := Nat.land (Nat.shiftRight (lane 32 K idx) 16) 255
@[expose] noncomputable def kpar (K idx : ℕ) : ℕ := Nat.shiftRight (lane 32 K idx) 24

@[expose] noncomputable def emb : (Fin 32 → ℚ) →ₗ[ℚ] (Fin 64 → ℚ) where
  toFun u i := if i.val % 2 = 0 then u ⟨i.val / 2, by have := i.isLt; omega⟩ else 0
  map_add' u w := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem allPairs_iff (l : List (List Q4 × List Q4)) (f : List Q4 × List Q4 → Bool) :
    allPairs l f = true ↔ ∀ p ∈ l, f p = true := by
  induction l with
  | nil => simp [allPairs]
  | cons x xs ih =>
    change CFSG.KC.Ord.andB (f x) (allPairs xs f) = true ↔ _
    rw [P.andB_iff, ih]
    simp

theorem gamMat_apply_eq {N g : ℕ} (r c : Fin N) :
    gamMat N g r c = if gP g r = (c : ℕ) then (if gS g r = 1 then (-1 : ℚ) else 1) else 0 := rfl

theorem gamMat_mul_apply {N g : ℕ} (hg : ∀ r < N, gP g r < N) (B : Matrix (Fin N) (Fin N) ℚ)
    (r c : Fin N) :
    (gamMat N g * B) r c = (if gS g r = 1 then (-1 : ℚ) else 1) * B ⟨gP g r, hg r r.isLt⟩ c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨gP g r, hg r r.isLt⟩]
  · rw [gamMat_apply_eq, if_pos rfl]
  · intro t _ ht
    have : gP g r ≠ (t : ℕ) := fun e => ht (Fin.ext e.symm)
    rw [gamMat_apply_eq, if_neg this, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem gS_le_one (g r : ℕ) : gS g r ≤ 1 := Nat.and_le_right

theorem sgn_mul_sgn {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    (if a = 1 then (-1 : ℚ) else 1) * (if b = 1 then (-1 : ℚ) else 1) =
      if (a + b) % 2 = 1 then -1 else 1 := by
  interval_cases a <;> interval_cases b <;> norm_num

theorem gamRelK_sound {n N : ℕ} {G : List ℕ} (h : gamRelK n N G = true) :
    GammaRel (gamM N G) n := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨hlen, hall⟩ := P.andB_iff.1 h1
  have hlen' : G.length = n := P.beq_iff.1 hlen
  have hpi : ∀ i < n, ∀ r < N, gP (G.getD i 0) r < N := by
    intro i hi r hr
    have hmem : G.getD i 0 ∈ G := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    obtain ⟨-, h3⟩ := P.andB_iff.1 ((P.allL_iff _ _).1 hall _ hmem)
    exact Nat.blt_eq.mp ((P.allN_iff _ _).1 h3 r hr)
  have hrel := (P.allN_iff _ _).1 h2
  intro i hi j hj
  have hr := (P.allN_iff _ _).1 ((P.allN_iff _ _).1 (hrel i hi) j hj)
  ext r c
  have hrr := hr r r.isLt
  unfold relAt at hrr
  simp only [P.letB_eq] at hrr
  simp only [Matrix.add_apply, gamM, gamMat_mul_apply (hpi i hi), gamMat_mul_apply (hpi j hj),
    gamMat_apply_eq, Fin.val_mk]
  by_cases hij : i = j
  · subst hij
    rw [show Nat.beq i i = true from P.beq_iff.2 rfl] at hrr
    obtain ⟨h5, h6⟩ := P.andB_iff.1 hrr
    have e5 := P.beq_iff.1 h5
    have e6 := P.beq_iff.1 h6
    rw [e5, ← e6, if_pos rfl, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hrc : r = c
    · subst hrc
      rw [if_pos rfl, if_pos rfl, sgn_mul_sgn (gS_le_one _ _) (gS_le_one _ _)]
      split_ifs <;> first | omega | norm_num
    · rw [if_neg (fun e => hrc (Fin.ext e)), if_neg hrc]
      ring
  · have hb : Nat.beq i j = false := by
      cases hc : Nat.beq i j
      · rfl
      · exact absurd (P.beq_iff.1 hc) hij
    rw [hb] at hrr
    obtain ⟨h5, h6⟩ := P.andB_iff.1 hrr
    have e5 := P.beq_iff.1 h5
    have e6 := P.notB_iff.1 h6
    rw [e5, if_neg hij, Matrix.zero_apply]
    by_cases hc : gP (G.getD i 0) (gP (G.getD j 0) r) = c
    · rw [if_pos hc, if_pos hc, sgn_mul_sgn (gS_le_one _ _) (gS_le_one _ _), sgn_mul_sgn (gS_le_one _ _) (gS_le_one _ _)]
      have hne : (gS (G.getD i 0) r + gS (G.getD j 0) (gP (G.getD i 0) r)) % 2 ≠
          (gS (G.getD j 0) r + gS (G.getD i 0) (gP (G.getD j 0) r)) % 2 :=
        fun e => e6 (P.beq_iff.2 e)
      split_ifs <;> first | omega | norm_num
    · rw [if_neg hc, if_neg hc]
      ring

theorem wordsOK_sound {n : ℕ} {p : List Q4 × List Q4} (h : wordsOK n p = true) :
    (∀ q ∈ p.1, ValidQ n q) ∧ (∀ q ∈ p.2, ValidQ n q) := by
  have hall : ∀ (l : List Q4) (f : Q4 → Bool), wordsOK.allLQ l f = true → ∀ q ∈ l, f q = true := by
    intro l f hl
    induction l with
    | nil => exact fun q hq => absurd hq List.not_mem_nil
    | cons x l ih =>
      obtain ⟨h1, h2⟩ := P.andB_iff.1 hl
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h1
      · exact ih h2 q hq
  obtain ⟨h1, -⟩ := P.andB_iff.1 h
  have hv : ∀ q ∈ p.1 ++ p.2, ValidQ n q := by
    intro q hq
    have hq' := hall _ _ h1 q hq
    simp only [P.andB_iff, P.notB_iff, P.beq_iff, Nat.blt_eq] at hq'
    exact hq'
  exact ⟨fun q hq => hv q (List.mem_append_left _ hq),
    fun q hq => hv q (List.mem_append_right _ hq)⟩

theorem lane_eq_div (w x i : ℕ) : lane w x i = x / 2 ^ (w * i) % 2 ^ w := by
  unfold lane
  rw [show Nat.shiftLeft 1 w = 2 ^ w from (Nat.shiftLeft_eq 1 w).trans (one_mul _)]
  change (x >>> (w * i)) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem lane_lt_two_pow (w x i : ℕ) : lane w x i < 2 ^ w := by
  rw [lane_eq_div]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem ofLanes_succ (w S : ℕ) (f : ℕ → ℕ) :
    ofLanes w (S + 1) f = ofLanes w S f + f S * 2 ^ (w * S) := by
  change ofLanes w S f + f S <<< (w * S) = _
  rw [Nat.shiftLeft_eq]

theorem ofLanes_lt {w : ℕ} {f : ℕ → ℕ} : ∀ {S : ℕ}, (∀ i < S, f i < 2 ^ w) →
    ofLanes w S f < 2 ^ (w * S)
  | 0, _ => Nat.one_pos
  | S + 1, hf => by
    rw [ofLanes_succ]
    have hA := ofLanes_lt (S := S) fun i hi => hf i (by omega)
    calc ofLanes w S f + f S * 2 ^ (w * S) < 2 ^ (w * S) + f S * 2 ^ (w * S) :=
          Nat.add_lt_add_right hA _
      _ = (f S + 1) * 2 ^ (w * S) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * S) := Nat.mul_le_mul_right _ (hf S (by omega))
      _ = 2 ^ (w * (S + 1)) := by rw [← pow_add]; ring_nf

theorem lane_ofLanes {w : ℕ} {f : ℕ → ℕ} : ∀ {S j : ℕ}, (∀ i < S, f i < 2 ^ w) → j < S →
    lane w (ofLanes w S f) j = f j
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | S + 1, j, hf, hj => by
    have hA := ofLanes_lt (S := S) (f := f) fun i hi => hf i (by omega)
    rw [ofLanes_succ, lane_eq_div]
    rcases Nat.lt_or_ge j S with hjS | hjS
    · have e : 2 ^ (w * S) = 2 ^ (w * (S - j - 1)) * 2 ^ w * 2 ^ (w * j) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have : S = (S - j - 1) + 1 + j := by omega
        conv_lhs => rw [this]
        ring
      rw [e, ← mul_assoc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), ← mul_assoc,
        Nat.add_mul_mod_self_right, ← lane_eq_div]
      exact lane_ofLanes (fun i hi => hf i (by omega)) hjS
    · have hjS' : j = S := by omega
      subst hjS'
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hA, zero_add,
        Nat.mod_eq_of_lt (hf j (by omega))]

theorem add_div_lanes (w x y : ℕ) : ∀ i, (∀ i' < i, lane w x i' + lane w y i' < 2 ^ w) →
    (x + y) / 2 ^ (w * i) = x / 2 ^ (w * i) + y / 2 ^ (w * i)
  | 0, _ => by simp
  | i + 1, h => by
    have ih := add_div_lanes w x y i fun i' hi' => h i' (by omega)
    have hi := h i (by omega)
    rw [lane_eq_div, lane_eq_div] at hi
    have e : ∀ z, z / 2 ^ (w * (i + 1)) = z / 2 ^ (w * i) / 2 ^ w := fun z => by
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      congr 2
    rw [e, e, e, ih, Nat.add_div (Nat.two_pow_pos w), if_neg (by omega), add_zero]

theorem lane_add {w x y i : ℕ} (h : ∀ i' ≤ i, lane w x i' + lane w y i' < 2 ^ w) :
    lane w (x + y) i = lane w x i + lane w y i := by
  have hd := add_div_lanes w x y i fun i' hi' => h i' hi'.le
  have hi := h i le_rfl
  simp only [lane_eq_div] at hi ⊢
  rw [hd, Nat.add_mod, Nat.mod_eq_of_lt hi]

theorem add_lt_of_lanes {w n x y : ℕ} (hx : x < 2 ^ (w * n)) (hy : y < 2 ^ (w * n))
    (h : ∀ i < n, lane w x i + lane w y i < 2 ^ w) : x + y < 2 ^ (w * n) := by
  have hd := add_div_lanes w x y n h
  rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy] at hd
  by_contra hc
  have := Nat.div_pos (not_lt.1 hc) (Nat.two_pow_pos (w * n))
  omega

@[expose] noncomputable def pkE (N X r j : ℕ) : ℕ := lane 64 (lane (64 * N) X r) j

@[expose] noncomputable def pkV (N X Y : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun r j => ((pkE N X r j : ℕ) : ℚ) - ((pkE N Y r j : ℕ) : ℚ)

@[expose] def PkB (N B X : ℕ) : Prop := ∀ r < N, ∀ j < N, pkE N X r j ≤ B

theorem pkE_add {N X Y r j : ℕ} (hr : r < N) (hj : j < N)
    (h : ∀ r' < N, ∀ j' < N, pkE N X r' j' + pkE N Y r' j' < 2 ^ 64) :
    pkE N (X + Y) r j = pkE N X r j + pkE N Y r j := by
  unfold pkE
  have hrow : lane (64 * N) (X + Y) r = lane (64 * N) X r + lane (64 * N) Y r :=
    lane_add fun r' hr' => add_lt_of_lanes (lane_lt_two_pow _ _ _) (lane_lt_two_pow _ _ _)
      fun j' hj' => h r' (by omega) j' hj'
  rw [hrow]
  exact lane_add fun j' hj' => h r hr j' (by omega)

theorem pkE_permP {N g X Y r j : ℕ} (hr : r < N) :
    pkE N (permP (64 * N) N g X Y) r j = pkE N (if gS g r = 1 then Y else X) (gP g r) j := by
  unfold pkE permP
  rw [lane_ofLanes (fun i _ => lane_lt_two_pow _ _ _) hr]
  by_cases h : gS g r = 1
  · have hb : Nat.beq (gS g r) (nat_lit 1) = true := P.beq_iff.2 h
    rw [hb, if_pos h]
  · have hb : Nat.beq (gS g r) (nat_lit 1) = false := by
      cases hc : Nat.beq (gS g r) (nat_lit 1)
      · rfl
      · exact absurd (P.beq_iff.1 hc) h
    rw [hb, if_neg h]

theorem pkB_mono {N B B' X : ℕ} (h : PkB N B X) (hB : B ≤ B') : PkB N B' X :=
  fun r hr j hj => (h r hr j hj).trans hB

theorem pkB_permP {N g B X Y : ℕ} (hg : ∀ r < N, gP g r < N) (hX : PkB N B X)
    (hY : PkB N B Y) : PkB N B (permP (64 * N) N g X Y) := by
  intro r hr j hj
  rw [pkE_permP hr]
  split_ifs
  · exact hY _ (hg r hr) j hj
  · exact hX _ (hg r hr) j hj

theorem pkV_permP {N g X Y : ℕ} (hg : ∀ r < N, gP g r < N) :
    pkV N (permP (64 * N) N g X Y) (permP (64 * N) N g Y X) = gamMat N g * pkV N X Y := by
  ext r c
  rw [gamMat_mul_apply hg]
  simp only [pkV, Matrix.of_apply, pkE_permP r.isLt, Fin.val_mk]
  split_ifs <;> ring

theorem pkB_add {N B X Y : ℕ} (hB : B + B < 2 ^ 64) (hX : PkB N B X) (hY : PkB N B Y) :
    PkB N (B + B) (X + Y) := by
  intro r hr j hj
  rw [pkE_add hr hj fun r' hr' j' hj' => by
    have := hX r' hr' j' hj'
    have := hY r' hr' j' hj'
    omega]
  have := hX r hr j hj
  have := hY r hr j hj
  omega

theorem pkV_add {N B X1 Y1 X2 Y2 : ℕ} (hB : B + B < 2 ^ 64) (h1 : PkB N B X1) (h2 : PkB N B Y1)
    (h3 : PkB N B X2) (h4 : PkB N B Y2) :
    pkV N (X1 + Y2) (Y1 + X2) = pkV N X1 Y1 - pkV N X2 Y2 := by
  have hb : ∀ {X Y : ℕ}, PkB N B X → PkB N B Y →
      ∀ r' < N, ∀ j' < N, pkE N X r' j' + pkE N Y r' j' < 2 ^ 64 := by
    intro X Y hX hY r' hr' j' hj'
    have := hX r' hr' j' hj'
    have := hY r' hr' j' hj'
    omega
  ext r j
  simp only [pkV, Matrix.of_apply, Matrix.sub_apply, pkE_add r.isLt j.isLt (hb h1 h4),
    pkE_add r.isLt j.isLt (hb h2 h3)]
  push_cast
  ring

theorem ddA_spec {n N B : ℕ} {G : List ℕ} {q : Q4}
    (hpi : ∀ i < n, ∀ r < N, gP (G.getD i 0) r < N) (hq : ValidQ n q) (hB : B * 4 < 2 ^ 64)
    {P M : ℕ} (hP : PkB N B P) (hM : PkB N B M) :
    ∃ P' M', PkB N (B * 4) P' ∧ PkB N (B * 4) M' ∧
      pkV N P' M' = (2 : ℚ) • (SpinM.Mdd (gamM N G) q * pkV N P M) ∧
      ∀ k, ddA (64 * N) N G q P M k = k P' M' := by
  have ha := hpi _ hq.1
  have hb := hpi _ hq.2.1
  have hc := hpi _ hq.2.2.1
  have hd := hpi _ hq.2.2.2.1
  have hB1 : B + B < 2 ^ 64 := by omega
  have hB2 : B + B + (B + B) < 2 ^ 64 := by omega
  have hc1 := pkB_permP hc hP hM
  have hc2 := pkB_permP hc hM hP
  have hd1 := pkB_permP hd hP hM
  have hd2 := pkB_permP hd hM hP
  have hu1 := pkB_add hB1 hc1 hd2
  have hu2 := pkB_add hB1 hc2 hd1
  have ha1 := pkB_permP ha hu1 hu2
  have ha2 := pkB_permP ha hu2 hu1
  have hb1 := pkB_permP hb hu1 hu2
  have hb2 := pkB_permP hb hu2 hu1
  refine ⟨_, _, pkB_mono (pkB_add hB2 ha1 hb2) (by omega),
    pkB_mono (pkB_add hB2 ha2 hb1) (by omega), ?_, fun k => by
      unfold ddA gamA
      simp only [CFSG.KC.LQT.P.letB_eq]
      rfl⟩
  rw [pkV_add hB2 ha1 ha2 hb1 hb2, pkV_permP ha, pkV_permP hb, pkV_add hB1 hc1 hc2 hd1 hd2,
    pkV_permP hc, pkV_permP hd]
  have hne : ¬ (q.1 = q.2.1 ∨ q.2.2.1 = q.2.2.2) := fun h => h.elim hq.2.2.2.2.1 hq.2.2.2.2.2
  rw [SpinM.Mdd, if_neg hne, Matrix.smul_mul, smul_smul,
    show (2 : ℚ) * (1 / 2) = 1 by norm_num, one_smul]
  unfold gamM
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem wordA_spec {n N : ℕ} {G : List ℕ} (hpi : ∀ i < n, ∀ r < N, gP (G.getD i 0) r < N)
    (w : List Q4) (hw : ∀ q ∈ w, ValidQ n q) {B P M : ℕ} (hB : B * 4 ^ w.length < 2 ^ 64)
    (hP : PkB N B P) (hM : PkB N B M) :
    ∃ P' M', PkB N (B * 4 ^ w.length) P' ∧ PkB N (B * 4 ^ w.length) M' ∧
      pkV N P' M' = (2 : ℚ) ^ w.length • (SpinM.Mw (gamM N G) w * pkV N P M) ∧
      ∀ k, wordA (64 * N) N G w P M k = k P' M' := by
  induction w generalizing B P M with
  | nil =>
    refine ⟨P, M, by simpa using hP, by simpa using hM, ?_, fun k => rfl⟩
    simp [SpinM.Mw]
  | cons q w ih =>
    have hlen : (q :: w).length = w.length + 1 := rfl
    have hB' : B * 4 ^ w.length * 4 < 2 ^ 64 := by
      rw [hlen, pow_succ, ← mul_assoc] at hB
      exact hB
    obtain ⟨P1, M1, h1, h2, h3, h4⟩ :=
      ih (fun q' hq' => hw q' (List.mem_cons_of_mem _ hq')) (by omega) hP hM
    obtain ⟨P2, M2, h5, h6, h7, h8⟩ := ddA_spec hpi (hw q List.mem_cons_self) hB' h1 h2
    have e : B * 4 ^ (q :: w).length = B * 4 ^ w.length * 4 := by
      rw [hlen, pow_succ, ← mul_assoc]
    refine ⟨P2, M2, e ▸ h5, e ▸ h6, ?_, fun k => (h4 _).trans (h8 k)⟩
    have e2 : SpinM.Mw (gamM N G) (q :: w) = SpinM.Mdd (gamM N G) q * SpinM.Mw (gamM N G) w := by
      simp [SpinM.Mw]
    rw [h7, h3, e2, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hlen, pow_succ, mul_comm]

theorem pkE_zero (N r j : ℕ) : pkE N 0 r j = 0 := by
  simp [pkE, lane_eq_div]

theorem pkE_idM {N r j : ℕ} (hr : r < N) (hj : j < N) :
    pkE N (idM N) r j = if r = j then 1 else 0 := by
  unfold pkE idM
  have hsh : ∀ i, Nat.shiftLeft 1 (64 * i) = 2 ^ (64 * i) := fun i =>
    (Nat.shiftLeft_eq 1 _).trans (one_mul _)
  have hpow : ∀ i < N, Nat.shiftLeft 1 (64 * i) < 2 ^ (64 * N) := by
    intro i hi
    rw [hsh]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  change lane 64 (lane (64 * N) (ofLanes (64 * N) N fun i => Nat.shiftLeft 1 (64 * i)) r) j = _
  rw [lane_ofLanes hpow hr, hsh, lane_eq_div]
  rcases lt_trichotomy r j with h | rfl | h
  · rw [if_neg (by omega), Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)),
      Nat.zero_mod]
  · rw [if_pos rfl, Nat.div_self (Nat.two_pow_pos _)]
    norm_num
  · rw [if_neg (by omega), Nat.pow_div (by omega) (by norm_num),
      show 64 * r - 64 * j = 64 + (64 * r - 64 * j - 64) by omega, pow_add, Nat.mul_mod_right]

theorem pkB_idM (N : ℕ) : PkB N 1 (idM N) := by
  intro r hr j hj
  rw [pkE_idM hr hj]
  split_ifs <;> omega

theorem pkB_zero (N B : ℕ) : PkB N B 0 := by
  intro r _ j _
  rw [pkE_zero]
  exact Nat.zero_le _

theorem pkV_idM (N : ℕ) : pkV N (idM N) 0 = 1 := by
  ext r j
  simp only [pkV, Matrix.of_apply, pkE_idM r.isLt j.isLt, pkE_zero, Matrix.one_apply,
    Fin.ext_iff]
  split_ifs <;> norm_num

theorem colsOK_spec {N X Y e : ℕ} : ∀ (R : List (ℕ × ℕ)) (j0 : ℕ), colsOK N X Y e R j0 = true →
    ∀ t < R.length, ∀ r < N, pkE N X r (j0 + t) + lane 64 (R.getD t (0, 0)).2 r * 2 ^ e =
      pkE N Y r (j0 + t) + lane 64 (R.getD t (0, 0)).1 r * 2 ^ e
  | [], _, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | c :: R, j0, h, t, ht => by
    obtain ⟨h1, h2⟩ := P.andB_iff.1 h
    cases t with
    | zero =>
      intro r hr
      have e1 := P.beq_iff.1 ((P.allN_iff _ _).1 (P.andB_iff.1 h1).2 r hr)
      change lane 64 (lane (64 * N) X r) j0 + Nat.shiftLeft (lane 64 c.2 r) e =
        lane 64 (lane (64 * N) Y r) j0 + Nat.shiftLeft (lane 64 c.1 r) e at e1
      have hsl : ∀ a b : ℕ, Nat.shiftLeft a b = a * 2 ^ b := fun a b => Nat.shiftLeft_eq a b
      rw [hsl, hsl] at e1
      exact e1
    | succ t =>
      have ht' : t < R.length := by simp only [List.length_cons] at ht; omega
      have := colsOK_spec R (j0 + 1) h2 t ht'
      intro r hr
      rw [show j0 + (t + 1) = j0 + 1 + t by omega]
      exact this r hr

theorem invW_eq_native (w : List Q4) : CFSG.KC.SpinOrb.invW w = SpinNative.invW w := by
  induction w with
  | nil => rfl
  | cons q w ih =>
    change CFSG.KC.SpinOrb.invW w ++ [(q.2.2.1, q.2.2.2, q.1, q.2.1)] = _
    rw [ih]
    simp [SpinNative.invW]

theorem Mw_append {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (a b : List Q4) :
    SpinM.Mw Γ (a ++ b) = SpinM.Mw Γ a * SpinM.Mw Γ b := by
  simp [SpinM.Mw, List.map_append, List.prod_append]

theorem matOK_sound {n N : ℕ} {G : List ℕ} {p : List Q4 × List Q4} {R : List (ℕ × ℕ)}
    (hG : gamRelK n N G = true) (hw : wordsOK n p = true) (h : matOK N G p R = true) :
    (4 : ℚ) • SpinM.Mcomm (gamM N G) p = colM N R := by
  obtain ⟨hRl, hw'⟩ := P.andB_iff.1 h
  have hRl' : R.length = N := P.beq_iff.1 hRl
  obtain ⟨h1, -⟩ := P.andB_iff.1 hG
  obtain ⟨hlen, hall⟩ := P.andB_iff.1 h1
  have hlen' : G.length = n := P.beq_iff.1 hlen
  have hpi : ∀ i < n, ∀ r < N, gP (G.getD i 0) r < N := by
    intro i hi r hr
    have hmem : G.getD i 0 ∈ G := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    obtain ⟨-, h3⟩ := P.andB_iff.1 ((P.allL_iff _ _).1 hall _ hmem)
    exact Nat.blt_eq.mp ((P.allN_iff _ _).1 h3 r hr)
  obtain ⟨hv1, hv2⟩ := wordsOK_sound hw
  have hinv : ∀ w : List Q4, (∀ q ∈ w, ValidQ n q) →
      ∀ q ∈ CFSG.KC.SpinOrb.invW w, ValidQ n q := by
    intro w hw q hq
    rw [invW_eq_native] at hq
    simp only [SpinNative.invW, List.mem_map, List.mem_reverse] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact validQ_swap (hw q' hq')
  have hval : ∀ q ∈ seqW p, ValidQ n q := by
    intro q hq
    simp only [seqW, List.mem_append] at hq
    rcases hq with hq | hq | hq | hq
    · exact hv1 q hq
    · exact hv2 q hq
    · exact hinv _ hv1 q hq
    · exact hinv _ hv2 q hq
  obtain ⟨-, hL⟩ := P.andB_iff.1 hw
  obtain ⟨hL2, hL24⟩ := P.andB_iff.1 hL
  have hL2' : 2 ≤ (seqW p).length := Nat.le_of_ble_eq_true hL2
  have hL24' : (seqW p).length ≤ 24 := Nat.le_of_ble_eq_true hL24
  have hB : 1 * 4 ^ (seqW p).length < 2 ^ 64 :=
    calc 1 * 4 ^ (seqW p).length ≤ 4 ^ 24 := by
          rw [one_mul]
          exact Nat.pow_le_pow_right (by norm_num) hL24'
      _ < 2 ^ 64 := by norm_num
  obtain ⟨P', M', -, -, hV, hk⟩ := wordA_spec hpi (seqW p) hval hB (pkB_idM N) (pkB_zero N 1)
  have hcol := (hk _).symm.trans hw'
  rw [P.letB_eq] at hcol
  change colsOK N P' M' ((seqW p).length - 2) R 0 = true at hcol
  have hspec := colsOK_spec R 0 hcol
  have hMw : SpinM.Mw (gamM N G) (seqW p) = SpinM.Mcomm (gamM N G) p := by
    simp only [seqW, Mw_append, SpinM.Mcomm, invW_eq_native, Matrix.mul_assoc]
  rw [pkV_idM, Matrix.mul_one, hMw] at hV
  ext r j
  have e1 := hspec j (by rw [hRl']; exact j.isLt) r r.isLt
  rw [zero_add] at e1
  have e2 : ((pkE N P' r j : ℕ) : ℚ) + ((lane 64 (R.getD j (0, 0)).2 r : ℕ) : ℚ) *
      2 ^ ((seqW p).length - 2) =
      ((pkE N M' r j : ℕ) : ℚ) + ((lane 64 (R.getD j (0, 0)).1 r : ℕ) : ℚ) *
      2 ^ ((seqW p).length - 2) := by
    exact_mod_cast e1
  have e3 := congrFun (congrFun hV r) j
  simp only [pkV, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at e3
  simp only [colM, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have e4 : (2 : ℚ) ^ (seqW p).length = 2 ^ ((seqW p).length - 2) * 4 := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hL2']
  rw [e4] at e3
  have hpos : (0 : ℚ) < 2 ^ ((seqW p).length - 2) := by positivity
  have e5 : (2 : ℚ) ^ ((seqW p).length - 2) * (4 * SpinM.Mcomm (gamM N G) p r j) =
      2 ^ ((seqW p).length - 2) * (((lane 64 (R.getD j (0, 0)).1 r : ℕ) : ℚ) -
        ((lane 64 (R.getD j (0, 0)).2 r : ℕ) : ℚ)) := by
    linear_combination e2 - e3
  exact mul_left_cancel₀ hpos.ne' e5

theorem ddA_cps (W N : ℕ) (G : List ℕ) (q : Q4) (X Y : ℕ) :
    ∃ X' Y', ∀ k, ddA W N G q X Y k = k X' Y' :=
  ⟨_, _, fun k => by
    unfold ddA gamA
    simp only [P.letB_eq]
    rfl⟩

theorem wordA_cps (W N : ℕ) (G : List ℕ) :
    ∀ (w : List Q4) (P M : ℕ), ∃ P' M', ∀ k, wordA W N G w P M k = k P' M'
  | [], P, M => ⟨P, M, fun _ => rfl⟩
  | q :: w, P, M => by
    obtain ⟨P1, M1, h1⟩ := wordA_cps W N G w P M
    obtain ⟨P2, M2, h2⟩ := ddA_cps W N G q P1 M1
    exact ⟨P2, M2, fun k => (h1 _).trans (h2 k)⟩

theorem smallK_lane {w b N x : ℕ} (h : smallK w b N x = true) : ∀ i < N, lane w x i < 2 ^ b := by
  intro i hi
  have := Nat.blt_eq.mp ((P.allN_iff _ _).1 (P.andB_iff.1 h).2 i hi)
  rwa [show Nat.shiftLeft 1 b = 2 ^ b from (Nat.shiftLeft_eq 1 b).trans (one_mul _)] at this

theorem colsOK_small {N X Y e : ℕ} : ∀ (R : List (ℕ × ℕ)) (j0 : ℕ), colsOK N X Y e R j0 = true →
    ∀ t < R.length, smallK 64 16 N (R.getD t (0, 0)).1 = true ∧
      smallK 64 16 N (R.getD t (0, 0)).2 = true
  | [], _, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | c :: R, j0, h, t, ht => by
    obtain ⟨h1, h2⟩ := P.andB_iff.1 h
    cases t with
    | zero => exact P.andB_iff.1 (P.andB_iff.1 h1).1
    | succ t =>
      have ht' : t < R.length := by simp only [List.length_cons] at ht; omega
      exact colsOK_small R (j0 + 1) h2 t ht'

def LnB (N B X : ℕ) : Prop := ∀ i < N, lane 64 X i ≤ B

theorem lnB_add {N B1 B2 X Y : ℕ} (hB : B1 + B2 < 2 ^ 64) (hX : LnB N B1 X) (hY : LnB N B2 Y) :
    LnB N (B1 + B2) (X + Y) ∧ ∀ i < N, lane 64 (X + Y) i = lane 64 X i + lane 64 Y i := by
  have e : ∀ i < N, lane 64 (X + Y) i = lane 64 X i + lane 64 Y i := fun i hi =>
    lane_add fun i' hi' => by
      have := hX i' (by omega)
      have := hY i' (by omega)
      omega
  refine ⟨fun i hi => ?_, e⟩
  rw [e i hi]
  have := hX i hi
  have := hY i hi
  omega

theorem lnB_mul {N B X : ℕ} (hX : LnB N B X) : ∀ v : ℕ, v * B < 2 ^ 64 →
    LnB N (v * B) (v * X) ∧ ∀ i < N, lane 64 (v * X) i = v * lane 64 X i
  | 0, _ => ⟨fun i _ => by simp [lane_eq_div], fun i _ => by simp [lane_eq_div]⟩
  | v + 1, h => by
    have hB : v * B + B < 2 ^ 64 := by rwa [← Nat.succ_mul]
    obtain ⟨h1, h2⟩ := lnB_mul hX v (by omega)
    obtain ⟨h3, h4⟩ := lnB_add hB h1 hX
    rw [Nat.succ_mul, Nat.succ_mul]
    refine ⟨h3, fun i hi => ?_⟩
    rw [h4 i hi, h2 i hi, Nat.succ_mul]

theorem lnB_sum {N B : ℕ} (f : ℕ → ℕ) : ∀ m : ℕ, (∀ j < m, LnB N B (f j)) → m * B < 2 ^ 64 →
    LnB N (m * B) (∑ j ∈ Finset.range m, f j) ∧
      ∀ i < N, lane 64 (∑ j ∈ Finset.range m, f j) i = ∑ j ∈ Finset.range m, lane 64 (f j) i
  | 0, _, _ => ⟨fun i _ => by simp [lane_eq_div], fun i _ => by simp [lane_eq_div]⟩
  | m + 1, hf, h => by
    have hB : m * B + B < 2 ^ 64 := by rwa [← Nat.succ_mul]
    obtain ⟨h1, h2⟩ := lnB_sum f m (fun j hj => hf j (by omega)) (by omega)
    obtain ⟨h3, h4⟩ := lnB_add hB h1 (hf m (by omega))
    simp only [Finset.sum_range_succ]
    rw [Nat.succ_mul]
    refine ⟨h3, fun i hi => ?_⟩
    rw [h4 i hi, h2 i hi]

noncomputable def mvAL (k : ℕ → ℕ → Bool) (R : List (ℕ × ℕ)) : ℕ → ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → Bool) (fun _ A B => k A B)
    (fun c _ ih x A B => P.letB (Nat.land x (nat_lit 18446744073709551615)) fun v =>
      P.letB (Nat.add A (Nat.add (Nat.mul v c.1) (Nat.mul (nat_lit 128) c.2))) fun A' =>
        P.letB (Nat.add B (Nat.add (Nat.mul v c.2) (Nat.mul (nat_lit 128) c.1))) fun B' =>
          ih (Nat.shiftRight x (nat_lit 64)) A' B') R

theorem lane_shift64 (x j : ℕ) : lane 64 (Nat.shiftRight x 64) j = lane 64 x (j + 1) := by
  rw [lane_eq_div, lane_eq_div,
    show Nat.shiftRight x 64 = x / 2 ^ 64 from Nat.shiftRight_eq_div_pow x 64,
    Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  ring

theorem land_mask64 (x : ℕ) : Nat.land x 18446744073709551615 = lane 64 x 0 := by
  rw [lane_eq_div]
  have := Nat.and_two_pow_sub_one_eq_mod x 64
  norm_num at this ⊢
  exact this

theorem mvAL_eq (k : ℕ → ℕ → Bool) : ∀ (R : List (ℕ × ℕ)) (x A B : ℕ), mvAL k R x A B =
    k (A + ∑ j ∈ Finset.range R.length,
        (lane 64 x j * (R.getD j (0, 0)).1 + 128 * (R.getD j (0, 0)).2))
      (B + ∑ j ∈ Finset.range R.length,
        (lane 64 x j * (R.getD j (0, 0)).2 + 128 * (R.getD j (0, 0)).1))
  | [], x, A, B => by simp only [List.length_nil, Finset.range_zero, Finset.sum_empty, add_zero]; rfl
  | c :: R, x, A, B => by
    have e : mvAL k (c :: R) x A B = mvAL k R (Nat.shiftRight x 64)
        (A + (lane 64 x 0 * c.1 + 128 * c.2)) (B + (lane 64 x 0 * c.2 + 128 * c.1)) := by
      rw [← land_mask64]
      simp only [mvAL, P.letB_eq]
      try rfl
    rw [e, mvAL_eq k R]
    simp only [List.length_cons, Finset.sum_range_succ', lane_shift64, List.getD_cons_succ,
      List.getD_cons_zero]
    congr 1 <;> ring

theorem mvOK_sound {N : ℕ} {G : List ℕ} {p : List Q4 × List Q4} {R : List (ℕ × ℕ)} {b c : ℕ}
    (hN : N ≤ 128) (hm : matOK N G p R = true) (hb : smallK 64 8 N b = true)
    (h : mvOK N R b c = true) :
    colM N R *ᵥ vecT N b = (4 : ℚ) • vecT N c := by
  obtain ⟨hRl, hw'⟩ := P.andB_iff.1 hm
  have hRl' : R.length = N := P.beq_iff.1 hRl
  obtain ⟨P', M', hk⟩ := wordA_cps (Nat.mul 64 N) N G (seqW p) (idM N) 0
  have hcol := (hk _).symm.trans hw'
  rw [P.letB_eq] at hcol
  have hsm := colsOK_small R 0 hcol
  obtain ⟨hc, hmv⟩ := P.andB_iff.1 h
  change mvAL (fun A B => Nat.beq (Nat.add A (Nat.mul 512 (ones N))) (Nat.add B (Nat.mul 4 c)))
    R b 0 0 = true at hmv
  rw [mvAL_eq, zero_add, zero_add, hRl'] at hmv
  have hmv' := P.beq_iff.1 hmv
  have hbl := smallK_lane hb
  have hcl : ∀ i < N, lane 64 c i < 2 ^ 8 := smallK_lane hc
  have hC : ∀ j < N, LnB N 65535 (R.getD j (0, 0)).1 ∧ LnB N 65535 (R.getD j (0, 0)).2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hsm j (by omega)
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := smallK_lane h1 i hi
      omega
    · have := smallK_lane h2 i hi
      omega
  have hT : ∀ (D1 D2 : ℕ → ℕ), (∀ j < N, LnB N 65535 (D1 j) ∧ LnB N 65535 (D2 j)) →
      LnB N (N * (255 * 65535 + 128 * 65535))
        (∑ j ∈ Finset.range N, (lane 64 b j * D1 j + 128 * D2 j)) ∧
      ∀ i < N, lane 64 (∑ j ∈ Finset.range N, (lane 64 b j * D1 j + 128 * D2 j)) i =
        ∑ j ∈ Finset.range N, (lane 64 b j * lane 64 (D1 j) i + 128 * lane 64 (D2 j) i) := by
    intro D1 D2 hD
    have hterm : ∀ j < N, LnB N (255 * 65535 + 128 * 65535) (lane 64 b j * D1 j + 128 * D2 j) ∧
        ∀ i < N, lane 64 (lane 64 b j * D1 j + 128 * D2 j) i =
          lane 64 b j * lane 64 (D1 j) i + 128 * lane 64 (D2 j) i := by
      intro j hj
      have hv := hbl j hj
      obtain ⟨m1, m2⟩ := lnB_mul (hD j hj).1 (lane 64 b j) (by omega)
      obtain ⟨m3, m4⟩ := lnB_mul (hD j hj).2 128 (by norm_num)
      have hle : LnB N (255 * 65535) (lane 64 b j * D1 j) := fun i hi =>
        (m1 i hi).trans (Nat.mul_le_mul_right _ (by omega))
      obtain ⟨a1, a2⟩ := lnB_add (by norm_num) hle m3
      exact ⟨a1, fun i hi => by rw [a2 i hi, m2 i hi, m4 i hi]⟩
    obtain ⟨s1, s2⟩ := lnB_sum _ N (fun j hj => (hterm j hj).1)
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ hN) (by norm_num))
    refine ⟨s1, fun i hi => ?_⟩
    rw [s2 i hi]
    exact Finset.sum_congr rfl fun j hj => (hterm j (Finset.mem_range.1 hj)).2 i hi
  obtain ⟨tA1, tA2⟩ := hT (fun j => (R.getD j (0, 0)).1) (fun j => (R.getD j (0, 0)).2) hC
  obtain ⟨tB1, tB2⟩ := hT (fun j => (R.getD j (0, 0)).2) (fun j => (R.getD j (0, 0)).1)
    fun j hj => (hC j hj).symm
  beta_reduce at tA1 tA2 tB1 tB2
  have hones : LnB N 1 (ones N) ∧ ∀ i < N, lane 64 (ones N) i = 1 := by
    have e : ∀ i < N, lane 64 (ones N) i = 1 := fun i hi =>
      lane_ofLanes (f := fun _ => 1) (fun _ _ => by norm_num) hi
    exact ⟨fun i hi => (e i hi).le, e⟩
  obtain ⟨o1, o2⟩ := lnB_mul hones.1 512 (by norm_num)
  have hcB : LnB N 255 c := fun i hi => by have := hcl i hi; omega
  obtain ⟨c1, c2⟩ := lnB_mul hcB 4 (by norm_num)
  have hbound : N * (255 * 65535 + 128 * 65535) ≤ 128 * (255 * 65535 + 128 * 65535) :=
    Nat.mul_le_mul_right _ hN
  obtain ⟨-, eA⟩ := lnB_add (lt_of_le_of_lt (Nat.add_le_add_right hbound _) (by norm_num)) tA1 o1
  obtain ⟨-, eB⟩ := lnB_add (lt_of_le_of_lt (Nat.add_le_add_right hbound _) (by norm_num)) tB1 c1
  funext r
  have hr := congrArg (fun z => lane 64 z r) hmv'
  beta_reduce at hr
  change lane 64 (_ + 512 * ones N) r = lane 64 (_ + 4 * c) r at hr
  rw [eA r r.isLt, eB r r.isLt, tA2 r r.isLt, tB2 r r.isLt, o2 r r.isLt, hones.2 r r.isLt,
    c2 r r.isLt] at hr
  have hq : (∑ j ∈ Finset.range N, ((lane 64 b j : ℚ) * (lane 64 (R.getD j (0, 0)).1 r : ℚ) +
      128 * (lane 64 (R.getD j (0, 0)).2 r : ℚ))) + 512 =
      (∑ j ∈ Finset.range N, ((lane 64 b j : ℚ) * (lane 64 (R.getD j (0, 0)).2 r : ℚ) +
      128 * (lane 64 (R.getD j (0, 0)).1 r : ℚ))) + 4 * (lane 64 c r : ℚ) := by
    exact_mod_cast hr
  simp only [Matrix.mulVec, dotProduct, colM, vecT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j => (((lane 64 (R.getD j (0, 0)).1 r : ℕ) : ℚ) -
      ((lane 64 (R.getD j (0, 0)).2 r : ℕ) : ℚ)) * ((((lane 64 b j : ℕ) : ℚ) - 128) / 4)) N]
  have e : ∑ j ∈ Finset.range N, ((((lane 64 (R.getD j (0, 0)).1 r : ℕ) : ℚ) -
      ((lane 64 (R.getD j (0, 0)).2 r : ℕ) : ℚ)) * ((((lane 64 b j : ℕ) : ℚ) - 128) / 4)) =
      ((∑ j ∈ Finset.range N, ((lane 64 b j : ℚ) * (lane 64 (R.getD j (0, 0)).1 r : ℚ) +
        128 * (lane 64 (R.getD j (0, 0)).2 r : ℚ))) -
       (∑ j ∈ Finset.range N, ((lane 64 b j : ℚ) * (lane 64 (R.getD j (0, 0)).2 r : ℚ) +
        128 * (lane 64 (R.getD j (0, 0)).1 r : ℚ)))) / 4 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  linear_combination hq / 4

theorem lamOK_sound {S Sg Tr L k : ℕ} (hS : S ≤ 256) (h : lamOK S Sg Tr L k = true) (j : ℕ)
    (hj : j < S) :
    lamAt S L k j = if k = 0 then j else sig S Sg (labOf Tr k) (lamAt S L (parOf Tr k) j) := by
  unfold lamOK at h
  simp only [P.letB_eq] at h
  have e1 : lamAt S L k j = lane 8 (lane (8 * S) L k) j := rfl
  rw [e1]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have h' : Nat.beq (lane (8 * S) L 0) (ofLanes 8 S fun j => j) = true := h
    rw [P.beq_iff.1 h', lane_ofLanes _ hj]
    exact fun i hi => lt_of_lt_of_le hi (hS.trans (by norm_num))
  · rw [if_neg hk]
    have hb : Nat.beq k 0 = false := by
      cases k with
      | zero => exact absurd rfl hk
      | succ k => rfl
    rw [hb] at h
    have h' : Nat.beq (lane (8 * S) L k) (ofLanes 8 S fun j =>
        lane 8 (lane (8 * S) Sg (Nat.shiftRight (lane 16 Tr k) 8))
          (lane 8 (lane (8 * S) L (Nat.land (lane 16 Tr k) 255)) j)) = true := h
    rw [P.beq_iff.1 h', lane_ofLanes _ hj]
    · rfl
    · exact fun i _ => lane_lt_two_pow _ _ _

theorem treeOK_sound {S nL Sg Tr k : ℕ} (h : treeOK S nL Sg Tr k = true) (hk : k ≠ 0) :
    parOf Tr k < k ∧ labOf Tr k < nL ∧ sig S Sg (labOf Tr k) (parOf Tr k) = k := by
  unfold treeOK at h
  have hb : Nat.beq k 0 = false := by
    cases k with
    | zero => exact absurd rfl hk
    | succ k => rfl
  simp only [P.letB_eq, hb] at h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨h2, h3⟩ := P.andB_iff.1 h2
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, P.beq_iff.1 h3⟩

theorem gamMat_mulVec_apply {N g : ℕ} (v : Fin N → ℚ) (r : Fin N) (hr : gP g r < N) :
    (gamMat N g *ᵥ v) r = (if gS g r = 1 then (-1 : ℚ) else 1) * v ⟨gP g r, hr⟩ := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ⟨gP g r, hr⟩]
  · rw [gamMat_apply_eq, if_pos rfl]
  · intro t _ ht
    have : gP g r ≠ (t : ℕ) := fun e => ht (Fin.ext e.symm)
    rw [gamMat_apply_eq, if_neg this, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem gP_eq (g r : ℕ) : gP g r = lane 8 g r / 2 := by
  change lane 8 g r >>> 1 = _
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem gS_eq (g r : ℕ) : gS g r = lane 8 g r % 2 := by
  change lane 8 g r &&& 1 = _
  rw [Nat.and_one_is_mod]

theorem kronE_eq (e s : ℕ) : kronIK.kronE e s = 4 * (e / 2) + 2 * (s % 2) + e % 2 := by
  change 4 * (e >>> 1) + (2 * (s &&& 1) + (e &&& 1)) = _
  rw [Nat.shiftRight_eq_div_pow, pow_one, Nat.and_one_is_mod, Nat.and_one_is_mod]
  omega

theorem emb_apply (u : Fin 32 → ℚ) (i : Fin 64) :
    emb u i = if i.val % 2 = 0 then u ⟨i.val / 2, by have := i.isLt; omega⟩ else 0 := rfl

theorem kronIK_sound {G G' : List ℕ} (hG : gamRelK 10 32 G = true) (h : kronIK 10 32 G G' = true) :
    ∀ k < 10, ∀ u : Fin 32 → ℚ, gamM 64 G' k *ᵥ emb u = emb (gamM 32 G k *ᵥ u) := by
  intro k hk u
  obtain ⟨h1, -⟩ := P.andB_iff.1 hG
  obtain ⟨hlen, hall⟩ := P.andB_iff.1 h1
  have hlen' : G.length = 10 := P.beq_iff.1 hlen
  have hmem : G.getD k 0 ∈ G := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hpi : ∀ r < 32, gP (G.getD k 0) r < 32 := by
    obtain ⟨-, h3⟩ := P.andB_iff.1 ((P.allL_iff _ _).1 hall _ hmem)
    exact fun r hr => Nat.blt_eq.mp ((P.allN_iff _ _).1 h3 r hr)
  have hk' := P.beq_iff.1 ((P.allN_iff _ _).1 h k hk)
  have hkr : ∀ s < 32 + 32, kronIK.kronE (lane 8 (G.getD k 0) (s >>> 1)) s < 2 ^ 8 := by
    intro s hs
    have h2 := hpi (s >>> 1) (by rw [Nat.shiftRight_eq_div_pow]; omega)
    rw [gP_eq] at h2
    rw [kronE_eq]
    omega
  have hl : ∀ s < 64, lane 8 (G'.getD k 0) s =
      kronIK.kronE (lane 8 (G.getD k 0) (s / 2)) s := by
    intro s hs
    have e1 : lane 8 (G'.getD k 0) s = kronIK.kronE (lane 8 (G.getD k 0) (s >>> 1)) s := by
      rw [hk']
      exact lane_ofLanes hkr hs
    rw [e1, Nat.shiftRight_eq_div_pow, pow_one]
  funext s
  have hs := s.isLt
  have hr : s.val / 2 < 32 := by omega
  have hP' : gP (G'.getD k 0) s = 2 * gP (G.getD k 0) (s.val / 2) + s.val % 2 := by
    rw [gP_eq, hl s hs, kronE_eq, gP_eq]
    omega
  have hS' : gS (G'.getD k 0) s = gS (G.getD k 0) (s.val / 2) := by
    rw [gS_eq, hl s hs, kronE_eq, gS_eq]
    omega
  have hlt : gP (G'.getD k 0) s < 64 := by
    have := hpi _ hr
    omega
  have hlt0 : gP (G.getD k 0) (s.val / 2) < 32 := hpi _ hr
  rw [gamM, gamM, gamMat_mulVec_apply _ _ hlt, emb_apply, emb_apply]
  by_cases he : s.val % 2 = 0
  · have he' : (gP (G'.getD k 0) s) % 2 = 0 := by omega
    rw [if_pos he', if_pos he]
    rw [gamMat_mulVec_apply _ ⟨s.val / 2, hr⟩ hlt0, hS']
    congr 2
    apply Fin.ext
    change gP (G'.getD k 0) s / 2 = gP (G.getD k 0) (s.val / 2)
    omega
  · have he' : ¬ (gP (G'.getD k 0) s) % 2 = 0 := by omega
    rw [if_neg he', if_neg he, mul_zero]

theorem gensEq_sound {n : ℕ} {ps : List (List Q4 × List Q4)} {gs : List ℕ}
    (h : gensEq n ps gs = true) :
    gs.length = ps.length ∧ ∀ j < ps.length, gs.getD j 0 = psiC n (ps.getD j ([], [])) := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  have hl := P.beq_iff.1 h1
  refine ⟨hl.symm, ?_⟩
  clear h h1
  induction ps generalizing gs with
  | nil => exact fun j hj => absurd hj (Nat.not_lt_zero _)
  | cons p ps ih =>
    intro j hj
    obtain ⟨h3, h4⟩ := P.andB_iff.1 h2
    cases gs with
    | nil => exact absurd hl (by simp)
    | cons g gs =>
      simp only [List.length_cons] at hl hj
      cases j with
      | zero => simpa using P.beq_iff.1 h3
      | succ j => simpa using ih (gs := gs) h4 (by omega) j (by omega)

theorem abelOK_sound {S nF Tr L : ℕ} {A : List ℕ} (h : abelOK S nF Tr L A = true) :
    0 ∈ A ∧ A.Nodup ∧ (∀ g < nF, parOf Tr (g + 1) = 0 ∧ labOf Tr (g + 1) = g) ∧
      ∀ a ∈ A, a < S ∧ lamAt S L a a = 0 ∧ (∀ b ∈ A, lamAt S L a b ∈ A) ∧
        ∀ g < nF, ∃ b ∈ A, lamAt S L (g + 1) a = lamAt S L b (g + 1) := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨h0, hT⟩ := P.andB_iff.1 h1
  obtain ⟨hs, hA⟩ := P.andB_iff.1 h2
  have hT' := (P.allN_iff _ _).1 hT
  have hA' := (P.allL_iff _ _).1 hA
  have hstr : ∀ (l : List ℕ) (p : ℕ), List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun x _ ih p => andB (Nat.blt p x) (ih x)) l p = true →
      (∀ x ∈ l, p < x) ∧ l.Pairwise (· < ·) := by
    intro l
    induction l with
    | nil => exact fun _ _ => ⟨fun x hx => absurd hx List.not_mem_nil, List.Pairwise.nil⟩
    | cons x l ih =>
      intro p hp
      obtain ⟨hpx, hl⟩ := P.andB_iff.1 hp
      obtain ⟨hl1, hl2⟩ := ih x hl
      have hpx' := Nat.blt_eq.mp hpx
      refine ⟨fun y hy => ?_, List.Pairwise.cons hl1 hl2⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hpx'
      · exact lt_trans hpx' (hl1 y hy)
  cases A with
  | nil => exact absurd (P.beq_iff.1 h0) (by simp)
  | cons a0 rest =>
    have ha0 : a0 = 0 := P.beq_iff.1 h0
    subst ha0
    obtain ⟨hs1, hs2⟩ := hstr rest 0 hs
    refine ⟨List.mem_cons_self, List.Pairwise.imp ne_of_lt (List.Pairwise.cons hs1 hs2), ?_, ?_⟩
    · intro g hg
      have e : lane 16 Tr (g + 1) = 256 * g := P.beq_iff.1 (hT' g hg)
      constructor
      · change Nat.land (lane 16 Tr (g + 1)) (2 ^ 8 - 1) = 0
        rw [e]
        change (256 * g) &&& (2 ^ 8 - 1) = 0
        rw [Nat.and_two_pow_sub_one_eq_mod]
        norm_num
      · change Nat.shiftRight (lane 16 Tr (g + 1)) 8 = g
        rw [e]
        change (256 * g) >>> 8 = g
        rw [Nat.shiftRight_eq_div_pow]
        norm_num
    · intro a ha
      have := hA' a ha
      simp only [P.andB_iff, P.allL_iff, P.anyL_iff, P.allN_iff, P.beq_iff, Nat.blt_eq] at this
      obtain ⟨h1, h2, h3, h4⟩ := this
      refine ⟨h1, h2, fun b hb => ?_, h4⟩
      obtain ⟨c, hc, e⟩ := h3 b hb
      rw [e]
      exact hc

theorem kleinAt_sound {S L K idx : ℕ} (h : kleinAt S L K idx = true) :
    kp K idx < S ∧ kq K idx < S ∧ lamAt S L (kp K idx) (kp K idx) = 0 ∧
      lamAt S L (kq K idx) (kq K idx) = 0 ∧
      lamAt S L (kp K idx) (kq K idx) = lamAt S L (kq K idx) (kp K idx) ∧ kp K idx ≠ 0 ∧
      kq K idx ≠ 0 ∧ kp K idx ≠ kq K idx ∧ kr K idx = lamAt S L (kp K idx) (kq K idx) ∧
      (idx ≠ 0 → kpar K idx < idx ∧
        lamAt S L (kp K idx) (kp K (kpar K idx)) = lamAt S L (kp K (kpar K idx)) (kp K idx) ∧
        lamAt S L (kp K idx) (kq K (kpar K idx)) = lamAt S L (kq K (kpar K idx)) (kp K idx) ∧
        lamAt S L (kq K idx) (kp K (kpar K idx)) = lamAt S L (kp K (kpar K idx)) (kq K idx) ∧
        lamAt S L (kq K idx) (kq K (kpar K idx)) = lamAt S L (kq K (kpar K idx)) (kq K idx)) := by
  unfold kleinAt at h
  simp only [P.letB_eq] at h
  obtain ⟨h0, h⟩ := P.andB_iff.1 h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h0
  obtain ⟨h3, h⟩ := P.andB_iff.1 h
  obtain ⟨h4, h⟩ := P.andB_iff.1 h
  obtain ⟨h5, h⟩ := P.andB_iff.1 h
  obtain ⟨h6, h⟩ := P.andB_iff.1 h
  obtain ⟨h7, h⟩ := P.andB_iff.1 h
  obtain ⟨h8, h⟩ := P.andB_iff.1 h
  obtain ⟨h9, h10⟩ := P.andB_iff.1 h
  refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, P.beq_iff.1 h3, P.beq_iff.1 h4, P.beq_iff.1 h5,
    fun e => P.notB_iff.1 h6 (P.beq_iff.2 e), fun e => P.notB_iff.1 h7 (P.beq_iff.2 e),
    fun e => P.notB_iff.1 h8 (P.beq_iff.2 e), P.beq_iff.1 h9, fun hidx => ?_⟩
  have hb : Nat.beq idx 0 = false := by
    cases idx with
    | zero => exact absurd rfl hidx
    | succ idx => rfl
  rw [hb] at h10
  obtain ⟨h11, h⟩ := P.andB_iff.1 h10
  obtain ⟨h12, h13⟩ := P.andB_iff.1 h
  obtain ⟨h14, h15⟩ := P.andB_iff.1 h12
  obtain ⟨h16, h17⟩ := P.andB_iff.1 h13
  exact ⟨Nat.blt_eq.mp h11, P.beq_iff.1 h14, P.beq_iff.1 h15, P.beq_iff.1 h16, P.beq_iff.1 h17⟩

theorem invAt_sound {S L i : ℕ} {I : List ℕ} (h : invAt S L I i = true) :
    (lamAt S L i i = 0 ∧ i ≠ 0) ↔ i ∈ I := by
  have key : ∀ a b : Bool, Nat.beq (Bool.rec (motive := fun _ => ℕ) 0 1 a)
      (Bool.rec (motive := fun _ => ℕ) 0 1 b) = true → a = b := by
    intro a b hab
    cases a <;> cases b <;> first | rfl | exact absurd hab (by decide)
  have hab : andB (Nat.beq (lamAt S L i i) 0) (notB (Nat.beq i 0)) =
      P.anyL I (fun x => Nat.beq x i) := key _ _ h
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : andB (Nat.beq (lamAt S L i i) 0) (notB (Nat.beq i 0)) = true :=
      P.andB_iff.2 ⟨P.beq_iff.2 h1, P.notB_iff.2 (fun e => h2 (P.beq_iff.1 e))⟩
    rw [hab, P.anyL_iff] at h3
    obtain ⟨x, hx, e⟩ := h3
    rwa [← P.beq_iff.1 e]
  · intro hi
    have h3 : P.anyL I (fun x => Nat.beq x i) = true :=
      (P.anyL_iff _ _).2 ⟨i, hi, P.beq_iff.2 rfl⟩
    rw [← hab] at h3
    obtain ⟨h1, h2⟩ := P.andB_iff.1 h3
    exact ⟨P.beq_iff.1 h1, fun e => P.notB_iff.1 h2 (P.beq_iff.2 e)⟩

theorem pairsAt_sound {S L K nK Wt a : ℕ} {I : List ℕ} (h : pairsAt S L K nK I Wt a = true) :
    ∀ b < I.length, I.getD a 0 = I.getD b 0 ∨
      lamAt S L (I.getD a 0) (I.getD b 0) ≠ lamAt S L (I.getD b 0) (I.getD a 0) ∨
      (lane 8 Wt (a * I.length + b) < nK ∧
        (I.getD a 0 = 0 ∨ I.getD a 0 = kp K (lane 8 Wt (a * I.length + b)) ∨
          I.getD a 0 = kq K (lane 8 Wt (a * I.length + b)) ∨
          I.getD a 0 = kr K (lane 8 Wt (a * I.length + b))) ∧
        (I.getD b 0 = 0 ∨ I.getD b 0 = kp K (lane 8 Wt (a * I.length + b)) ∨
          I.getD b 0 = kq K (lane 8 Wt (a * I.length + b)) ∨
          I.getD b 0 = kr K (lane 8 Wt (a * I.length + b)))) := by
  have hrec : ∀ {Q : ℕ → ℕ → Bool} (J : List ℕ) (b0 : ℕ),
      List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun j _ ih b => andB (Q b j) (ih (Nat.succ b))) J b0 = true →
      ∀ t < J.length, Q (b0 + t) (J.getD t 0) = true := by
    intro Q J
    induction J with
    | nil => exact fun _ _ t ht => absurd ht (Nat.not_lt_zero _)
    | cons j J ih =>
      intro b0 hJ t ht
      obtain ⟨h1, h2⟩ := P.andB_iff.1 hJ
      cases t with
      | zero => simpa using h1
      | succ t =>
        have := ih (Nat.succ b0) h2 t (by simp only [List.length_cons] at ht; omega)
        rw [show b0 + (t + 1) = Nat.succ b0 + t by omega]
        simpa using this
  unfold pairsAt at h
  rw [P.letB_eq] at h
  intro b hb
  have hQ := hrec I 0 h b hb
  rw [Nat.zero_add] at hQ
  simp only [P.orB_iff, P.notB_iff, P.beq_iff, P.letB_eq, P.andB_iff, Nat.blt_eq, inRec] at hQ
  exact hQ

theorem prefixK_sound {m : ℕ} {G G' : List ℕ} (h : prefixK m G G' = true) :
    ∀ k < m, gamM 16 G' k = gamM 16 G k := by
  intro k hk
  have := (P.allN_iff _ _).1 h k hk
  unfold gamM
  rw [Nat.eq_of_beq_eq_true this]

theorem sigOK_sound {N S T Sg k l : ℕ} {R : List (List (ℕ × ℕ))}
    (h : sigOK N S R T Sg k l = true) :
    sig S Sg l k < S ∧ mvOK N (R.getD l []) (blk N T k) (blk N T (sig S Sg l k)) = true := by
  unfold sigOK at h
  simp only [P.letB_eq] at h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  exact ⟨Nat.blt_eq.mp h1, h2⟩

theorem invOK_sound {S nF Sg k l : ℕ} (h : invOK S nF Sg k l = true) :
    sig S Sg (nF + l) k < S ∧ sig S Sg l (sig S Sg (nF + l) k) = k := by
  unfold invOK at h
  simp only [P.letB_eq] at h
  obtain ⟨h1, -⟩ := P.andB_iff.1 h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h1
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem orbAt_split {N S T Sg k : ℕ} {R : List (List (ℕ × ℕ))}
    (h : orbAt N S R T Sg k = true) :
    smallK 64 8 N (blk N T k) = true ∧ (∀ l < R.length, sigOK N S R T Sg k l = true) ∧
      ∀ l < R.length, invOK S R.length Sg k l = true := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨h2, h3⟩ := P.andB_iff.1 h2
  exact ⟨h1, (P.allN_iff _ _).1 h2, (P.allN_iff _ _).1 h3⟩

theorem orbitK_split {N S T Sg Tr L SG k : ℕ} {R : List (List (ℕ × ℕ))}
    (h : orbitK N S R T Sg Tr L SG k = true) :
    orbAt N S R T Sg k = true ∧ treeOK S (R.length + R.length) Sg Tr k = true ∧
      lamOK S Sg Tr L k = true ∧ sortAt S (blk N T) (lane 8 SG) k = true := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨h1, h3⟩ := P.andB_iff.1 h1
  obtain ⟨h2, h4⟩ := P.andB_iff.1 h2
  exact ⟨h1, h3, h2, h4⟩

theorem psiAt_split {n N E PA SG CT k : ℕ} {gs : List ℕ} (h : psiAt n N gs E PA SG CT k = true) :
    treeAt (P.mul n) (P.one n) (fun j => gs.getD j 0) gs.length (lane 64 E) (lane 32 PA) k = true ∧
      sortAt N (lane 64 E) (lane 8 SG) k = true ∧
      closedAt (P.mul n) (fun j => gs.getD j 0) gs.length N (lane 64 E) (lane 8 CT) k = true := by
  obtain ⟨h1, h3⟩ := P.andB_iff.1 h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h1
  exact ⟨h1, h2, h3⟩

theorem shiftLeft_one (w : ℕ) : Nat.shiftLeft 1 w = 2 ^ w :=
  (Nat.shiftLeft_eq 1 w).trans (one_mul _)

theorem lane_lt (w x i : ℕ) : lane w x i < 2 ^ w := by
  unfold lane
  rw [shiftLeft_one]
  change (x >>> (w * i)) &&& (2 ^ w - 1) < 2 ^ w
  exact lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)

theorem testBit_lane (w x i s : ℕ) (hs : s < w) :
    (lane w x i).testBit s = x.testBit (w * i + s) := by
  unfold lane
  rw [shiftLeft_one]
  change ((x >>> (w * i)) &&& (2 ^ w - 1)).testBit s = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  simp [hs]

theorem eq_of_lanes {w N x y : ℕ} (hw : 0 < w) (hx : x < 2 ^ (w * N)) (hy : y < 2 ^ (w * N))
    (h : ∀ i < N, lane w x i = lane w y i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < w * N
  · have hi : t / w < N := by
      rw [Nat.div_lt_iff_lt_mul hw, mul_comm]
      exact ht
    have hs : t % w < w := Nat.mod_lt _ hw
    have e : w * (t / w) + t % w = t := Nat.div_add_mod t w
    have := congrArg (fun z => z.testBit (t % w)) (h (t / w) hi)
    simp only [testBit_lane _ _ _ _ hs, e] at this
    exact this
  · push Not at ht
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right two_pos ht)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right two_pos ht))]

theorem blk_eq_of_vecT {N T a b : ℕ} (h : vecT N (blk N T a) = vecT N (blk N T b)) :
    blk N T a = blk N T b := by
  have hx : blk N T a < 2 ^ (64 * N) := lane_lt _ _ _
  have hy : blk N T b < 2 ^ (64 * N) := lane_lt _ _ _
  refine eq_of_lanes (by norm_num) hx hy fun i hi => ?_
  have h1 := congrFun h ⟨i, hi⟩
  simp only [vecT] at h1
  have h2 : ((lane 64 (blk N T a) i : ℕ) : ℚ) = ((lane 64 (blk N T b) i : ℕ) : ℚ) := by linarith
  exact_mod_cast h2

theorem emb_apply_two (u : Fin 32 → ℚ) (r : Fin 32) :
    emb u ⟨2 * r.val, by have := r.isLt; omega⟩ = u r := by
  show (if (2 * r.val) % 2 = 0 then u ⟨2 * r.val / 2, _⟩ else 0) = u r
  rw [if_pos (by omega)]
  congr 1
  ext
  show 2 * r.val / 2 = r.val
  omega

theorem emb_injective : Function.Injective emb := by
  intro u w h
  funext r
  have := congrFun h ⟨2 * r.val, by have := r.isLt; omega⟩
  rwa [emb_apply_two, emb_apply_two] at this

@[expose] def Intw {M N : ℕ} (ι : (Fin M → ℚ) →ₗ[ℚ] (Fin N → ℚ)) (A : Matrix (Fin N) (Fin N) ℚ)
    (B : Matrix (Fin M) (Fin M) ℚ) : Prop :=
  ∀ u, A *ᵥ ι u = ι (B *ᵥ u)

section Intw

variable {M N : ℕ} {ι : (Fin M → ℚ) →ₗ[ℚ] (Fin N → ℚ)}

theorem Intw.mul {A A' : Matrix (Fin N) (Fin N) ℚ} {B B' : Matrix (Fin M) (Fin M) ℚ}
    (h1 : Intw ι A B) (h2 : Intw ι A' B') : Intw ι (A * A') (B * B') := by
  intro u
  rw [← Matrix.mulVec_mulVec, h2, h1, Matrix.mulVec_mulVec]

theorem Intw.sub {A A' : Matrix (Fin N) (Fin N) ℚ} {B B' : Matrix (Fin M) (Fin M) ℚ}
    (h1 : Intw ι A B) (h2 : Intw ι A' B') : Intw ι (A - A') (B - B') := by
  intro u
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, map_sub, h1, h2]

theorem Intw.smul {A : Matrix (Fin N) (Fin N) ℚ} {B : Matrix (Fin M) (Fin M) ℚ} (c : ℚ)
    (h1 : Intw ι A B) : Intw ι (c • A) (c • B) := by
  intro u
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, map_smul, h1]

theorem Intw.one : Intw ι (1 : Matrix (Fin N) (Fin N) ℚ) (1 : Matrix (Fin M) (Fin M) ℚ) := by
  intro u
  rw [Matrix.one_mulVec, Matrix.one_mulVec]

theorem intw_Mdd {n0 : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {Γ0 : ℕ → Matrix (Fin M) (Fin M) ℚ}
    (hk : ∀ k < n0, Intw ι (Γ k) (Γ0 k)) (q : Q4) (hq : ValidQ n0 q) :
    Intw ι (SpinM.Mdd Γ q) (SpinM.Mdd Γ0 q) := by
  unfold SpinM.Mdd
  split_ifs
  · exact Intw.one
  · exact (((hk _ hq.1).sub (hk _ hq.2.1)).mul
      ((hk _ hq.2.2.1).sub (hk _ hq.2.2.2.1))).smul _

theorem intw_Mw {n0 : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {Γ0 : ℕ → Matrix (Fin M) (Fin M) ℚ}
    (hk : ∀ k < n0, Intw ι (Γ k) (Γ0 k)) (w : List Q4) (hw : ∀ q ∈ w, ValidQ n0 q) :
    Intw ι (SpinM.Mw Γ w) (SpinM.Mw Γ0 w) := by
  induction w with
  | nil =>
    simp only [SpinM.Mw, List.map_nil, List.prod_nil]
    exact Intw.one
  | cons q w ih =>
    simp only [SpinM.Mw, List.map_cons, List.prod_cons] at ih ⊢
    exact (intw_Mdd hk q (hw q List.mem_cons_self)).mul
      (ih fun q' hq' => hw q' (List.mem_cons_of_mem _ hq'))

theorem validQ_invW {n0 : ℕ} {w : List Q4} (hw : ∀ q ∈ w, ValidQ n0 q) :
    ∀ q ∈ SpinNative.invW w, ValidQ n0 q := by
  intro q hq
  simp only [SpinNative.invW, List.mem_map, List.mem_reverse] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  exact validQ_swap (hw q' hq')

theorem intw_Mcomm {n0 : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ}
    {Γ0 : ℕ → Matrix (Fin M) (Fin M) ℚ} (hk : ∀ k < n0, Intw ι (Γ k) (Γ0 k))
    (p : List Q4 × List Q4) (h1 : ∀ q ∈ p.1, ValidQ n0 q) (h2 : ∀ q ∈ p.2, ValidQ n0 q) :
    Intw ι (SpinM.Mcomm Γ p) (SpinM.Mcomm Γ0 p) := by
  unfold SpinM.Mcomm
  exact (((intw_Mw hk _ h1).mul (intw_Mw hk _ h2)).mul (intw_Mw hk _ (validQ_invW h1))).mul
    (intw_Mw hk _ (validQ_invW h2))

end Intw

section Core

variable {G : Type} [Group G]

@[expose] noncomputable def xs (gs : List G) (par lab : ℕ → ℕ) : ℕ → G
  | 0 => 1
  | k + 1 =>
    if h : par (k + 1) < k + 1 then gs.getD (lab (k + 1)) 1 * xs gs par lab (par (k + 1)) else 1
termination_by k => k

theorem xs_zero (gs : List G) (par lab : ℕ → ℕ) : xs gs par lab 0 = 1 := by
  rw [xs]

theorem xs_pos (gs : List G) (par lab : ℕ → ℕ) {k : ℕ} (hk : k ≠ 0) (hp : par k < k) :
    xs gs par lab k = gs.getD (lab k) 1 * xs gs par lab (par k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [xs, dif_pos hp]

theorem tree_core [Finite G] {N : ℕ} (θ : G →* Matrix (Fin N) (Fin N) ℚ) (gs : List G) (S : ℕ)
    (v : ℕ → Fin N → ℚ) (σ : ℕ → ℕ → ℕ) (par lab : ℕ → ℕ)
    (hact : ∀ l < gs.length, ∀ k < S, σ l k < S ∧ θ (gs.getD l 1) *ᵥ v k = v (σ l k))
    (htree : ∀ k < S, k ≠ 0 → par k < k ∧ lab k < gs.length ∧ σ (lab k) (par k) = k)
    (hinj : ∀ a < S, ∀ b < S, v a = v b → a = b)
    (hcard : Nat.card (closure {g | g ∈ gs}) ≤ S) :
    (∀ k < S, xs gs par lab k ∈ closure {g | g ∈ gs} ∧ θ (xs gs par lab k) *ᵥ v 0 = v k) ∧
      Nat.card (closure {g | g ∈ gs}) = S ∧
      (∀ y ∈ closure {g | g ∈ gs}, ∃ k < S, y = xs gs par lab k) ∧
      (∀ a < S, ∀ b < S, xs gs par lab a = xs gs par lab b → a = b) := by
  have hgen : ∀ l < gs.length, gs.getD l 1 ∈ closure {g | g ∈ gs} := fun l hl =>
    subset_closure (show gs.getD l 1 ∈ gs by
      rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl)
  have hA : ∀ k < S, xs gs par lab k ∈ closure {g | g ∈ gs} ∧
      θ (xs gs par lab k) *ᵥ v 0 = v k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases h0 : k = 0
      · subst h0
        rw [xs_zero, map_one, Matrix.one_mulVec]
        exact ⟨one_mem _, rfl⟩
      · obtain ⟨hp, hl, hσ⟩ := htree k hk h0
        obtain ⟨ih1, ih2⟩ := ih _ hp (hp.trans hk)
        rw [xs_pos gs par lab h0 hp]
        refine ⟨mul_mem (hgen _ hl) ih1, ?_⟩
        rw [map_mul, ← Matrix.mulVec_mulVec, ih2, (hact _ hl _ (hp.trans hk)).2, hσ]
  have hxinj : ∀ a < S, ∀ b < S, xs gs par lab a = xs gs par lab b → a = b := fun a ha b hb h =>
    hinj a ha b hb (by rw [← (hA a ha).2, ← (hA b hb).2, h])
  let F : Fin S → closure {g | g ∈ gs} := fun k => ⟨xs gs par lab k, (hA k k.isLt).1⟩
  have hF : Function.Injective F := fun a b h =>
    Fin.ext (hxinj a a.isLt b b.isLt (congrArg Subtype.val h))
  have hge : S ≤ Nat.card (closure {g | g ∈ gs}) := by
    simpa using Nat.card_le_card_of_injective F hF
  have hc : Nat.card (closure {g | g ∈ gs}) = S := le_antisymm hcard hge
  have hbij : Function.Bijective F := hF.bijective_of_nat_card_le (by simp [hc])
  refine ⟨hA, hc, fun y hy => ?_, hxinj⟩
  obtain ⟨k, hk⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨k, k.isLt, (congrArg Subtype.val hk).symm⟩

theorem tree_mul [Finite G] {N : ℕ} (θ : G →* Matrix (Fin N) (Fin N) ℚ) (gs : List G) (S : ℕ)
    (v : ℕ → Fin N → ℚ) (σ : ℕ → ℕ → ℕ) (par lab : ℕ → ℕ)
    (hact : ∀ l < gs.length, ∀ k < S, σ l k < S ∧ θ (gs.getD l 1) *ᵥ v k = v (σ l k))
    (htree : ∀ k < S, k ≠ 0 → par k < k ∧ lab k < gs.length ∧ σ (lab k) (par k) = k)
    (hinj : ∀ a < S, ∀ b < S, v a = v b → a = b)
    (hcard : Nat.card (closure {g | g ∈ gs}) ≤ S) (Λ : ℕ → ℕ → ℕ)
    (hlam : ∀ i < S, ∀ j < S, Λ i j = if i = 0 then j else σ (lab i) (Λ (par i) j)) :
    ∀ i < S, ∀ j < S, Λ i j < S ∧ xs gs par lab i * xs gs par lab j = xs gs par lab (Λ i j) := by
  obtain ⟨hA, -, hall, -⟩ := tree_core θ gs S v σ par lab hact htree hinj hcard
  have hB : ∀ i < S, ∀ j < S, Λ i j < S ∧ θ (xs gs par lab i) *ᵥ v j = v (Λ i j) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi j hj
      by_cases h0 : i = 0
      · subst h0
        rw [hlam 0 hi j hj, if_pos rfl, xs_zero, map_one, Matrix.one_mulVec]
        exact ⟨hj, rfl⟩
      · obtain ⟨hp, hl, -⟩ := htree i hi h0
        obtain ⟨ih1, ih2⟩ := ih _ hp (hp.trans hi) j hj
        obtain ⟨hs1, hs2⟩ := hact _ hl _ ih1
        rw [hlam i hi j hj, if_neg h0, xs_pos gs par lab h0 hp, map_mul, ← Matrix.mulVec_mulVec,
          ih2, hs2]
        exact ⟨hs1, rfl⟩
  intro i hi j hj
  obtain ⟨hl, hv⟩ := hB i hi j hj
  refine ⟨hl, ?_⟩
  obtain ⟨k, hk, hke⟩ := hall _ (mul_mem (hA i hi).1 (hA j hj).1)
  have : k = Λ i j := hinj k hk _ hl (by
    rw [← (hA k hk).2, ← hke, map_mul, ← Matrix.mulVec_mulVec, (hA j hj).2, hv])
  rw [hke, this]

theorem mem_normalizer_of_conj [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨a, ha, hay⟩ := hy
  have : a = y := by simpa [MulAut.conj_apply] using hay
  rwa [← this]

theorem exists_sylow_eq [Finite G] (S0 : Subgroup G) {e k : ℕ} (hS0 : Nat.card S0 = 2 ^ e)
    (hG : Nat.card G = 2 ^ e * k) (hodd : ¬ 2 ∣ k) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = S0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S0.index := by
    have h1 := S0.card_mul_index
    rw [hS0, hG] at h1
    rw [Nat.eq_of_mul_eq_mul_left (by positivity) h1]
    exact hodd
  exact ⟨(IsPGroup.of_card hS0).toSylow hidx, rfl⟩

theorem normal_finish [Finite G] (S0 : Subgroup G) (S : ℕ) (x : ℕ → G) (nF : ℕ) (gs : List G)
    (hS0 : S0 = closure {g | g ∈ gs}) (hlen : gs.length = nF + nF)
    (hbw : ∀ l < nF, gs.getD (nF + l) 1 = (gs.getD l 1)⁻¹)
    (hfw : ∀ l < nF, x (l + 1) = gs.getD l 1) (hnF : nF < S) (Λ : ℕ → ℕ → ℕ)
    (hmul : ∀ i < S, ∀ j < S, Λ i j < S ∧ x i * x j = x (Λ i j)) (hx0 : x 0 = 1)
    (hxinj : ∀ a < S, ∀ b < S, x a = x b → a = b) (A : List ℕ) (h0A : 0 ∈ A) (hnd : A.Nodup)
    (hA8 : 8 ≤ A.length)
    (hAf : ∀ a ∈ A, a < S ∧ Λ a a = 0 ∧ (∀ b ∈ A, Λ a b ∈ A) ∧
      ∀ g < nF, ∃ b ∈ A, Λ (g + 1) a = Λ b (g + 1))
    (P : Sylow 2 G) (hP : (P : Subgroup G) = S0) : SylowFourJoined G := by
  have hsq : ∀ a ∈ A, x a * x a = 1 := fun a ha => by
    rw [(hmul a (hAf a ha).1 a (hAf a ha).1).2, (hAf a ha).2.1, hx0]
  let Asub : Subgroup G :=
    { carrier := {y | ∃ a ∈ A, y = x a}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨Λ a b, (hAf a ha).2.2.1 b hb, (hmul a (hAf a ha).1 b (hAf b hb).1).2⟩
      one_mem' := ⟨0, h0A, hx0.symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a, ha, inv_eq_of_mul_eq_one_right (hsq a ha)⟩ }
  have hA2 : ∀ y ∈ Asub, y * y = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hsq a ha
  have hcard : 8 ≤ Nat.card Asub := by
    let F : Fin A.length → Asub := fun i => ⟨x (A[i.1]'i.2), ⟨A[i.1]'i.2, List.getElem_mem i.2, rfl⟩⟩
    have hF : Function.Injective F := by
      intro i j h
      have h' : x (A[i.1]'i.2) = x (A[j.1]'j.2) := congrArg Subtype.val h
      have := hxinj _ (hAf _ (List.getElem_mem i.2)).1 _ (hAf _ (List.getElem_mem j.2)).1 h'
      exact List.nodup_iff_injective_getElem.1 hnd this
    have := Nat.card_le_card_of_injective F hF
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  have hnorm : ∀ l < nF, gs.getD l 1 ∈ normalizer (Asub : Set G) := by
    intro l hl
    apply mem_normalizer_of_conj
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := (hAf a ha).2.2.2 l hl
    refine ⟨b, hb, ?_⟩
    have hl1 : l + 1 < S := by omega
    have key : x (l + 1) * x a = x b * x (l + 1) := by
      rw [(hmul (l + 1) hl1 a (hAf a ha).1).2, hab, ← (hmul b (hAf b hb).1 (l + 1) hl1).2]
    rw [← hfw l hl, key, mul_inv_cancel_right]
  have hSA : S0 ≤ normalizer (Asub : Set G) := by
    rw [hS0, closure_le]
    intro g hg
    obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 (show g ∈ gs from hg)
    rw [← List.getD_eq_getElem _ 1 hl]
    by_cases hl' : l < nF
    · exact hnorm l hl'
    · obtain ⟨l', rfl⟩ : ∃ l', l = nF + l' := ⟨l - nF, by omega⟩
      rw [hbw l' (by omega)]
      exact inv_mem (hnorm l' (by omega))
  exact sylowFourJoined_of_normal_elemAbelian P (A := Asub) (by rw [hP]; exact hSA) hA2 hcard

theorem klein_finish [Finite G] (S0 : Subgroup G) (S : ℕ) (hS : 0 < S) (x : ℕ → G)
    (hmemS : ∀ y, y ∈ S0 ↔ ∃ k < S, y = x k) (hx0 : x 0 = 1)
    (hxinj : ∀ a < S, ∀ b < S, x a = x b → a = b) (nK : ℕ) (kp kq kr kpar : ℕ → ℕ)
    (hK1 : ∀ idx < nK, kp idx < S ∧ kq idx < S ∧ x (kp idx) * x (kp idx) = 1 ∧
      x (kq idx) * x (kq idx) = 1 ∧ x (kp idx) * x (kq idx) = x (kq idx) * x (kp idx) ∧
      kp idx ≠ kq idx ∧ kp idx ≠ 0 ∧ kq idx ≠ 0 ∧ x (kr idx) = x (kp idx) * x (kq idx))
    (hK2 : ∀ idx < nK, idx ≠ 0 → kpar idx < idx ∧
      x (kp idx) * x (kp (kpar idx)) = x (kp (kpar idx)) * x (kp idx) ∧
      x (kp idx) * x (kq (kpar idx)) = x (kq (kpar idx)) * x (kp idx) ∧
      x (kq idx) * x (kp (kpar idx)) = x (kp (kpar idx)) * x (kq idx) ∧
      x (kq idx) * x (kq (kpar idx)) = x (kq (kpar idx)) * x (kq idx))
    (I : List ℕ) (hK3 : ∀ i < S, x i * x i = 1 → i ≠ 0 → i ∈ I)
    (hK4 : ∀ i ∈ I, ∀ j ∈ I, i < S → j < S → i = j ∨ x i * x j ≠ x j * x i ∨
      ∃ w < nK, (i = 0 ∨ i = kp w ∨ i = kq w ∨ i = kr w) ∧
        (j = 0 ∨ j = kp w ∨ j = kq w ∨ j = kr w))
    (P : Sylow 2 G) (hP : (P : Subgroup G) = S0) : SylowFourJoined G := by
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℕ → Subgroup G, ∀ idx, Kc idx =
      closure ({x (kp idx), x (kq idx)} : Set G) := ⟨fun idx => closure {x (kp idx), x (kq idx)},
    fun _ => rfl⟩
  have hne1 : ∀ i < S, i ≠ 0 → x i ≠ 1 := fun i hi h0 h =>
    h0 (hxinj i hi 0 hS (h.trans hx0.symm))
  have hKlein : ∀ idx < nK, IsKleinFour (Kc idx) ∧ Nat.card (Kc idx) = 4 := by
    intro idx hidx
    obtain ⟨hp, hq, h1, h2, h3, h6, h4, h5, -⟩ := hK1 idx hidx
    rw [hKc idx]
    exact CoverAltGroup.isKleinFour_closure_pair h1 h2 h3 (hne1 _ hp h4) (hne1 _ hq h5)
      (fun h => h6 (hxinj _ hp _ hq h))
  have hmemGen : ∀ idx < nK, ∀ t, (t = 0 ∨ t = kp idx ∨ t = kq idx ∨ t = kr idx) →
      x t ∈ Kc idx := by
    intro idx hidx t ht
    rw [hKc idx]
    rcases ht with rfl | rfl | rfl | rfl
    · rw [hx0]; exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · rw [(hK1 idx hidx).2.2.2.2.2.2.2.2]
      exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hcover : ∀ E' : Subgroup G, IsKleinFour E' → E' ≤ S0 → ∃ idx < nK, E' = Kc idx := by
    intro E' hE' hle
    obtain ⟨a, b, ha, hb, ha2, hb2, hab, ha1, hb1, hne, hEq⟩ :=
      CoverAltGroup.exists_pair_of_isKleinFour E' hE'
    obtain ⟨i, hi, rfl⟩ := (hmemS a).1 (hle ha)
    obtain ⟨j, hj, rfl⟩ := (hmemS b).1 (hle hb)
    have hi0 : i ≠ 0 := fun h => ha1 (by rw [h, hx0])
    have hj0 : j ≠ 0 := fun h => hb1 (by rw [h, hx0])
    have hij : i ≠ j := fun h => hne (by rw [h])
    rcases hK4 i (hK3 i hi ha2 hi0) j (hK3 j hj hb2 hj0) hi hj with h | h | ⟨w, hw, hiw, hjw⟩
    · exact absurd h hij
    · exact absurd hab h
    · have hsub : closure ({x i, x j} : Set G) ≤ Kc w := by
        rw [closure_le]
        intro y hy
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hmemGen w hw i hiw
        · exact hmemGen w hw j hjw
      refine ⟨w, hw, ?_⟩
      have hsubE : E' ≤ Kc w := by rw [hEq]; exact hsub
      exact Subgroup.eq_of_le_of_card_ge hsubE ((hKlein w hw).2.trans hE'.card_four.symm).le
  have hedge : ∀ idx, idx < nK → idx ≠ 0 →
      kpar idx < idx ∧ CommFourAdj G (Kc idx) (Kc (kpar idx)) := by
    intro idx hidx h0
    obtain ⟨hpar, c1, c2, c3, c4⟩ := hK2 idx hidx h0
    refine ⟨hpar, (hKlein idx hidx).1, (hKlein _ (lt_trans hpar hidx)).1, ?_⟩
    rw [hKc idx, hKc (kpar idx)]
    exact le_centralizer_pair c1 c2 c3 c4
  have hchain : ∀ idx, idx < nK → Relation.ReflTransGen (CommFourAdj G) (Kc idx) (Kc 0) :=
    reflTransGen_chain _ Kc kpar hedge
  refine sylowFourJoined_of_sylow P ?_
  intro E' F' hE' hES hF' hFS
  rw [hP] at hES hFS
  obtain ⟨i, hi, rfl⟩ := hcover E' hE' hES
  obtain ⟨j, hj, rfl⟩ := hcover F' hF' hFS
  exact (hchain i hi).trans (reflTransGen_commFourAdj_symm (hchain j hj))

end Core

section Spin

variable {m : ℕ}

@[expose] noncomputable def phiE (m : ℕ) : E (m + 2) →* Equiv.Perm (Fin (m + 2)) :=
  (permH (n := m + 2)).comp (E (m + 2)).subtype

@[expose] noncomputable def psiGens (m : ℕ) (ps : List (List Q4 × List Q4)) :
    List (Equiv.Perm (Fin (m + 2))) :=
  ps.map fun p => phiE m (liftE (m + 2) p.1 p.2)

@[expose] noncomputable def xE (m : ℕ) (ps : List (List Q4 × List Q4)) (Tr : ℕ) :
    ℕ → E (m + 2) :=
  xs (gensE (m + 2) ps) (parOf Tr) (labOf Tr)

theorem card_le_phi (hm : 6 ≤ m) (K : Subgroup (E (m + 2))) :
    Nat.card K ≤ 2 * Nat.card (K.map (phiE m)) := by
  haveI := finite_E hm
  obtain ⟨hfin, hker⟩ := card_ker_psi_le (m := m) hm
  haveI := hfin
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((phiE m).comp K.subtype).ker
  have h2 : Nat.card (K ⧸ ((phiE m).comp K.subtype).ker) =
      Nat.card ((phiE m).comp K.subtype).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ((phiE m).comp K.subtype)).toEquiv
  have h3 : Nat.card ((phiE m).comp K.subtype).range ≤ Nat.card (K.map (phiE m)) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  have h4 : Nat.card ((phiE m).comp K.subtype).ker ≤ Nat.card (psi (m := m)).ker := by
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1.1, ?_⟩) ?_
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have hy := y.2
      rw [MonoidHom.mem_ker] at hy
      exact hy
    · intro a b hab
      have h' := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h')
  rw [h1, h2]
  calc Nat.card ((phiE m).comp K.subtype).range * Nat.card ((phiE m).comp K.subtype).ker
      ≤ Nat.card (K.map (phiE m)) * 2 := Nat.mul_le_mul h3 (h4.trans hker)
    _ = 2 * Nat.card (K.map (phiE m)) := mul_comm _ _

theorem map_closure_gensE (ps : List (List Q4 × List Q4)) :
    (closure {g | g ∈ gensE (m + 2) ps}).map (phiE m) = closure {σ | σ ∈ psiGens m ps} := by
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ gensE (m + 2) ps := hg
    unfold gensE at hg'
    rcases List.mem_append.1 hg' with hg' | hg'
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg'
      exact subset_closure (show _ ∈ psiGens m ps from List.mem_map.2 ⟨p, hp, rfl⟩)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg'
      rw [← liftE_inv, map_inv]
      exact inv_mem (subset_closure (show _ ∈ psiGens m ps from List.mem_map.2 ⟨p, hp, rfl⟩))
  · apply Subgroup.closure_mono
    intro σ hσ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (show σ ∈ psiGens m ps from hσ)
    exact ⟨liftE (m + 2) p.1 p.2,
      show _ ∈ gensE (m + 2) ps from List.mem_append.2 (Or.inl (List.mem_map.2 ⟨p, hp, rfl⟩)), rfl⟩

theorem psiW_eq {n : ℕ} (hn : n ≤ 32) (w : List Q4) (hw : ∀ q ∈ w, ValidQ n q) :
    psiW n w = P.code (permH (n := n) (wordH n w)) := by
  induction w with
  | nil =>
    show P.one n = _
    rw [show wordH n [] = 1 from rfl, map_one]
    exact P.code_one
  | cons q w ih =>
    have hq := hw q List.mem_cons_self
    have ih' := ih fun q' h => hw q' (List.mem_cons_of_mem _ h)
    show P.mul n (P.mul n (P.swap n q.1 q.2.1) (P.swap n q.2.2.1 q.2.2.2)) (psiW n w) = _
    have hw' : wordH n (q :: w) = ddH n q * wordH n w := by simp [wordH]
    have hdd : permH (n := n) (ddH n q) =
        Equiv.swap (⟨q.1, hq.1⟩ : Fin n) ⟨q.2.1, hq.2.1⟩ *
          Equiv.swap (⟨q.2.2.1, hq.2.2.1⟩ : Fin n) ⟨q.2.2.2, hq.2.2.2.1⟩ := by
      unfold ddH
      rw [dif_pos hq]
      exact perm_dd _ _
    rw [hw', map_mul, ih', hdd,
      show P.swap n q.1 q.2.1 = P.code (Equiv.swap (⟨q.1, hq.1⟩ : Fin n) ⟨q.2.1, hq.2.1⟩) from
        P.code_swap (n := n) ⟨q.1, hq.1⟩ ⟨q.2.1, hq.2.1⟩,
      show P.swap n q.2.2.1 q.2.2.2 =
        P.code (Equiv.swap (⟨q.2.2.1, hq.2.2.1⟩ : Fin n) ⟨q.2.2.2, hq.2.2.2.1⟩) from
        P.code_swap (n := n) ⟨q.2.2.1, hq.2.2.1⟩ ⟨q.2.2.2, hq.2.2.2.1⟩,
      P.code_mul hn, P.code_mul hn]

theorem psiC_eq (hn : m + 2 ≤ 32) (p : List Q4 × List Q4) (h1 : ∀ q ∈ p.1, ValidQ (m + 2) q)
    (h2 : ∀ q ∈ p.2, ValidQ (m + 2) q) :
    psiC (m + 2) p = P.code (phiE m (liftE (m + 2) p.1 p.2)) := by
  unfold psiC
  rw [psiW_eq hn _ h1, psiW_eq hn _ h2, P.code_inv hn, P.code_inv hn, P.code_mul hn,
    P.code_mul hn, P.code_mul hn]
  congr 1
  show _ = permH (n := m + 2) ⁅wordH (m + 2) p.1, wordH (m + 2) p.2⁆
  rw [map_commutatorElement, commutatorElement_def]

theorem gensE_getD_lt {n : ℕ} (ps : List (List Q4 × List Q4)) {l : ℕ} (hl : l < ps.length) :
    (gensE n ps).getD l 1 = liftE n (ps.getD l ([], [])).1 (ps.getD l ([], [])).2 := by
  unfold gensE
  have h1 : l < (ps.map fun p => liftE n p.1 p.2).length := by simpa using hl
  rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, List.getElem_map,
    List.getD_eq_getElem _ _ hl]

theorem gensE_getD_ge {n : ℕ} (ps : List (List Q4 × List Q4)) {l : ℕ} (hl : l < ps.length) :
    (gensE n ps).getD (ps.length + l) 1 =
      (liftE n (ps.getD l ([], [])).1 (ps.getD l ([], [])).2)⁻¹ := by
  unfold gensE
  have h0 : (ps.map fun p => liftE n p.1 p.2).length ≤ ps.length + l := by simp
  have h1 : l < (ps.map fun p => liftE n p.2 p.1).length := by simpa using hl
  rw [List.getD_append_right _ _ _ _ h0, List.length_map, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ h1, List.getElem_map, List.getD_eq_getElem _ _ hl, liftE_inv]

theorem gensE_length {n : ℕ} (ps : List (List Q4 × List Q4)) :
    (gensE n ps).length = ps.length + ps.length := by
  simp [gensE]

theorem gamRelK_le {n N : ℕ} {G : List ℕ} (h : gamRelK n N G = true) (hn : 0 < n) :
    N ≤ 128 := by
  by_contra hc
  have hr := (P.allN_iff _ _).1 ((P.allN_iff _ _).1 ((P.allN_iff _ _).1 (P.andB_iff.1 h).2 0 hn)
    0 hn) 128 (by omega)
  unfold relAt at hr
  simp only [P.letB_eq] at hr
  rw [show Nat.beq 0 0 = true from P.beq_iff.2 rfl] at hr
  have e := P.beq_iff.1 (P.andB_iff.1 hr).1
  have hl := lane_lt_two_pow 8 (G.getD 0 0) (gP (G.getD 0 0) 128)
  rw [gP_eq] at e
  omega

theorem wordsOK_pos {n : ℕ} {p : List Q4 × List Q4} (h : wordsOK n p = true) : 0 < n := by
  obtain ⟨hv1, hv2⟩ := wordsOK_sound h
  have hL2 : 2 ≤ (seqW p).length :=
    Nat.le_of_ble_eq_true (P.andB_iff.1 (P.andB_iff.1 h).2).1
  rcases p with ⟨_ | ⟨q, _⟩, _ | ⟨q', _⟩⟩
  · exact absurd hL2 (by decide)
  · exact Nat.zero_lt_of_lt (hv2 q' List.mem_cons_self).1
  · exact Nat.zero_lt_of_lt (hv1 q List.mem_cons_self).1
  · exact Nat.zero_lt_of_lt (hv1 q List.mem_cons_self).1

theorem orbit_E (hm : 6 ≤ m) (hn32 : m + 2 ≤ 32) {N M : ℕ} (G' G0 : List ℕ) (n0 : ℕ)
    (ι : (Fin M → ℚ) →ₗ[ℚ] (Fin N → ℚ)) (hι : Function.Injective ι)
    (hG' : gamRelK (m + 2) N G' = true) (hG0 : gamRelK n0 M G0 = true)
    (hint : ∀ k < n0, Intw ι (gamM N G' k) (gamM M G0 k))
    (ps : List (List Q4 × List Q4)) (hw0 : allPairs ps (wordsOK n0) = true)
    (hw : allPairs ps (wordsOK (m + 2)) = true)
    (R : List (List (ℕ × ℕ))) (hRl : R.length = ps.length)
    (hmat : ∀ j < ps.length, matOK M G0 (ps.getD j ([], [])) (R.getD j []) = true)
    (S : ℕ) (hS : S ≤ 256) (T Sg Tr L SG : ℕ)
    (horb : ∀ k < S, orbitK M S R T Sg Tr L SG k = true)
    (PG : List ℕ) (NP PE PA PS PC : ℕ) (hNP : 0 < NP) (h2 : 2 * NP ≤ S)
    (hgens : gensEq (m + 2) ps PG = true)
    (hpsi : ∀ k < NP, psiAt (m + 2) NP PG PE PA PS PC k = true) :
    (∀ y, y ∈ closure {g | g ∈ gensE (m + 2) ps} ↔ ∃ k < S, y = xE m ps Tr k) ∧
      Nat.card (closure {g | g ∈ gensE (m + 2) ps}) = S ∧ xE m ps Tr 0 = 1 ∧
      (∀ a < S, ∀ b < S, xE m ps Tr a = xE m ps Tr b → a = b) ∧
      (∀ i < S, ∀ j < S, lamAt S L i j < S ∧
        xE m ps Tr i * xE m ps Tr j = xE m ps Tr (lamAt S L i j)) := by
  haveI := finite_E hm
  have hrel := gamRelK_sound hG'
  have hval : ∀ p ∈ ps, (∀ q ∈ p.1, ValidQ (m + 2) q) ∧ (∀ q ∈ p.2, ValidQ (m + 2) q) :=
    fun p hp => wordsOK_sound ((allPairs_iff _ _).1 hw p hp)
  have hval0 : ∀ p ∈ ps, (∀ q ∈ p.1, ValidQ n0 q) ∧ (∀ q ∈ p.2, ValidQ n0 q) :=
    fun p hp => wordsOK_sound ((allPairs_iff _ _).1 hw0 p hp)
  have hpget : ∀ j < ps.length, ps.getD j ([], []) ∈ ps := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have horb' := fun k (hk : k < S) => orbitK_split (horb k hk)
  have hfw : ∀ l < ps.length, ∀ k < S, sig S Sg l k < S ∧
      thetaM hrel ((gensE (m + 2) ps).getD l 1) *ᵥ ι (vecT M (blk M T k)) =
        ι (vecT M (blk M T (sig S Sg l k))) := by
    intro l hl k hk
    obtain ⟨hsm, hsig, -⟩ := orbAt_split (horb' k hk).1
    obtain ⟨hlt, hmv⟩ := sigOK_sound (hsig l (hRl ▸ hl))
    refine ⟨hlt, ?_⟩
    have hp := hpget l hl
    rw [gensE_getD_lt ps hl, thetaM_liftE hrel _ _ (hval _ hp).1 (hval _ hp).2]
    have h4 := matOK_sound hG0 ((allPairs_iff _ _).1 hw0 _ hp) (hmat l hl)
    have h5 := mvOK_sound (gamRelK_le hG0 (wordsOK_pos ((allPairs_iff _ _).1 hw0 _ hp)))
      (hmat l hl) hsm hmv
    rw [← h4, Matrix.smul_mulVec] at h5
    have h6 := smul_right_injective _ (by norm_num : (4 : ℚ) ≠ 0) h5
    rw [intw_Mcomm hint _ (hval0 _ hp).1 (hval0 _ hp).2]
    exact congrArg ι h6
  have hbw : ∀ l < ps.length, ∀ k < S, sig S Sg (ps.length + l) k < S ∧
      sig S Sg l (sig S Sg (ps.length + l) k) = k := by
    intro l hl k hk
    obtain ⟨-, -, hinv⟩ := orbAt_split (horb' k hk).1
    have := invOK_sound (hinv l (hRl ▸ hl))
    rw [hRl] at this
    exact this
  have hact : ∀ l < (gensE (m + 2) ps).length, ∀ k < S, sig S Sg l k < S ∧
      thetaM hrel ((gensE (m + 2) ps).getD l 1) *ᵥ ι (vecT M (blk M T k)) =
        ι (vecT M (blk M T (sig S Sg l k))) := by
    intro l hl k hk
    rw [gensE_length] at hl
    by_cases hlt : l < ps.length
    · exact hfw l hlt k hk
    · obtain ⟨l', rfl⟩ : ∃ l', l = ps.length + l' := ⟨l - ps.length, by omega⟩
      have hl' : l' < ps.length := by omega
      obtain ⟨h1, h2⟩ := hbw l' hl' k hk
      refine ⟨h1, ?_⟩
      have e := (hfw l' hl' _ h1).2
      rw [h2, gensE_getD_lt ps hl'] at e
      rw [gensE_getD_ge ps hl', ← e, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mulVec]
  have htree : ∀ k < S, k ≠ 0 → parOf Tr k < k ∧ labOf Tr k < (gensE (m + 2) ps).length ∧
      sig S Sg (labOf Tr k) (parOf Tr k) = k := by
    intro k hk h0
    have := treeOK_sound (horb' k hk).2.1 h0
    rw [gensE_length, ← hRl]
    exact this
  have hinj : ∀ a < S, ∀ b < S, ι (vecT M (blk M T a)) = ι (vecT M (blk M T b)) → a = b := by
    intro a ha b hb h
    have hs : ∀ i < S, sortAt S (blk M T) (lane 8 SG) i = true := fun i hi => (horb' i hi).2.2.2
    exact sort_distinct hs a ha b hb (blk_eq_of_vecT (hι h))
  have hpsiC : Nat.card (closure {σ | σ ∈ psiGens m ps}) = NP := by
    obtain ⟨hlenPG, hPG⟩ := gensEq_sound hgens
    have hglen : (psiGens m ps).length = PG.length := by simp [psiGens, hlenPG]
    have hG : ∀ j < (psiGens m ps).length, PG.getD j 0 = pcode ((psiGens m ps).getD j 1) := by
      intro j hj
      have hj' : j < ps.length := by simpa [psiGens] using hj
      rw [hPG j hj', psiC_eq hn32 _ (hval _ (hpget j hj')).1 (hval _ (hpget j hj')).2,
        List.getD_eq_getElem _ _ hj']
      unfold psiGens
      have h1 : j < (ps.map fun p => phiE m (liftE (m + 2) p.1 p.2)).length := by simpa using hj'
      rw [List.getD_eq_getElem _ _ h1, List.getElem_map]
      rfl
    have ht : ∀ k < NP, treeAt (P.mul (m + 2)) (P.one (m + 2)) (fun j => PG.getD j 0)
        (psiGens m ps).length (lane 64 PE) (lane 32 PA) k = true := fun k hk => by
      rw [hglen]; exact (psiAt_split (hpsi k hk)).1
    have hs : ∀ k < NP, sortAt NP (lane 64 PE) (lane 8 PS) k = true := fun k hk =>
      (psiAt_split (hpsi k hk)).2.1
    have hc : ∀ k < NP, closedAt (P.mul (m + 2)) (fun j => PG.getD j 0) (psiGens m ps).length NP
        (lane 64 PE) (lane 8 PC) k = true := fun k hk => by
      rw [hglen]; exact (psiAt_split (hpsi k hk)).2.2
    obtain ⟨-, -, h3⟩ := clos_card (pcode_enc hn32) (psiGens m ps) hG hNP ht hs
    exact (h3 hc).1
  have hcard : Nat.card (closure {g | g ∈ gensE (m + 2) ps}) ≤ S := by
    refine (card_le_phi hm _).trans ?_
    rw [map_closure_gensE, hpsiC]
    exact h2
  obtain ⟨hA, hc, hall, hxinj⟩ := tree_core (thetaM hrel) (gensE (m + 2) ps) S
    (fun k => ι (vecT M (blk M T k))) (sig S Sg) (parOf Tr) (labOf Tr) hact htree hinj hcard
  have hlam : ∀ i < S, ∀ j < S, lamAt S L i j =
      if i = 0 then j else sig S Sg (labOf Tr i) (lamAt S L (parOf Tr i) j) :=
    fun i hi j hj => lamOK_sound hS (horb' i hi).2.2.1 j hj
  have hmul := tree_mul (thetaM hrel) (gensE (m + 2) ps) S (fun k => ι (vecT M (blk M T k)))
    (sig S Sg) (parOf Tr) (labOf Tr) hact htree hinj hcard (lamAt S L) hlam
  refine ⟨fun y => ⟨fun hy => hall y hy, ?_⟩, hc, xs_zero _ _ _, hxinj, hmul⟩
  rintro ⟨k, hk, rfl⟩
  exact (hA k hk).1

theorem sylow_normal_of_checks (hm : 6 ≤ m) (hn32 : m + 2 ≤ 32) {N M : ℕ} (G' G0 : List ℕ)
    (n0 : ℕ) (ι : (Fin M → ℚ) →ₗ[ℚ] (Fin N → ℚ)) (hι : Function.Injective ι)
    (hG' : gamRelK (m + 2) N G' = true) (hG0 : gamRelK n0 M G0 = true)
    (hint : ∀ k < n0, Intw ι (gamM N G' k) (gamM M G0 k))
    (ps : List (List Q4 × List Q4)) (hw0 : allPairs ps (wordsOK n0) = true)
    (hw : allPairs ps (wordsOK (m + 2)) = true)
    (R : List (List (ℕ × ℕ))) (hRl : R.length = ps.length)
    (hmat : ∀ j < ps.length, matOK M G0 (ps.getD j ([], [])) (R.getD j []) = true)
    (S : ℕ) (hS : S ≤ 256) (T Sg Tr L SG : ℕ)
    (horb : ∀ k < S, orbitK M S R T Sg Tr L SG k = true)
    (PG : List ℕ) (NP PE PA PS PC : ℕ) (hNP : 0 < NP) (h2 : 2 * NP ≤ S)
    (hgens : gensEq (m + 2) ps PG = true)
    (hpsi : ∀ k < NP, psiAt (m + 2) NP PG PE PA PS PC k = true)
    (A : List ℕ) (habel : abelOK S ps.length Tr L A = true) (hA : A.length = 8)
    (hnF : ps.length < S) (e k : ℕ) (hSe : S = 2 ^ e) (hE : Nat.card (E (m + 2)) = 2 ^ e * k)
    (hodd : ¬ 2 ∣ k) : SylowFourJoined (E (m + 2)) := by
  haveI := finite_E hm
  obtain ⟨hmem, hc, hx0, hxinj, hmul⟩ := orbit_E hm hn32 G' G0 n0 ι hι hG' hG0 hint ps hw0 hw R
    hRl hmat S hS T Sg Tr L SG horb PG NP PE PA PS PC hNP h2 hgens hpsi
  obtain ⟨P, hP⟩ := exists_sylow_eq _ (hc.trans hSe) hE hodd
  obtain ⟨h0A, hnd, hrec, hAf⟩ := abelOK_sound habel
  have hfw : ∀ l < ps.length, xE m ps Tr (l + 1) = (gensE (m + 2) ps).getD l 1 := by
    intro l hl
    obtain ⟨hp, hlb⟩ := hrec l hl
    unfold xE
    rw [xs_pos _ _ _ (Nat.succ_ne_zero l) (by rw [hp]; omega), hp, hlb, xs_zero, mul_one]
  refine normal_finish _ S (xE m ps Tr) ps.length (gensE (m + 2) ps) rfl (gensE_length ps)
    (fun l hl => by rw [gensE_getD_ge ps hl, gensE_getD_lt ps hl]) hfw hnF (lamAt S L) hmul hx0
    hxinj A h0A hnd (by omega) hAf P hP

theorem sylow_klein_of_checks (hm : 6 ≤ m) (hn32 : m + 2 ≤ 32) {N M : ℕ} (G' G0 : List ℕ)
    (n0 : ℕ) (ι : (Fin M → ℚ) →ₗ[ℚ] (Fin N → ℚ)) (hι : Function.Injective ι)
    (hG' : gamRelK (m + 2) N G' = true) (hG0 : gamRelK n0 M G0 = true)
    (hint : ∀ k < n0, Intw ι (gamM N G' k) (gamM M G0 k))
    (ps : List (List Q4 × List Q4)) (hw0 : allPairs ps (wordsOK n0) = true)
    (hw : allPairs ps (wordsOK (m + 2)) = true)
    (R : List (List (ℕ × ℕ))) (hRl : R.length = ps.length)
    (hmat : ∀ j < ps.length, matOK M G0 (ps.getD j ([], [])) (R.getD j []) = true)
    (S : ℕ) (hS : S ≤ 256) (T Sg Tr L SG : ℕ)
    (horb : ∀ k < S, orbitK M S R T Sg Tr L SG k = true)
    (PG : List ℕ) (NP PE PA PS PC : ℕ) (hNP : 0 < NP) (h2 : 2 * NP ≤ S)
    (hgens : gensEq (m + 2) ps PG = true)
    (hpsi : ∀ k < NP, psiAt (m + 2) NP PG PE PA PS PC k = true)
    (K nK Wt : ℕ) (I : List ℕ) (hkl : ∀ idx < nK, kleinAt S L K idx = true)
    (hinv : ∀ i < S, invAt S L I i = true)
    (hpairs : ∀ a < I.length, pairsAt S L K nK I Wt a = true)
    (e k : ℕ) (hSe : S = 2 ^ e) (hE : Nat.card (E (m + 2)) = 2 ^ e * k)
    (hodd : ¬ 2 ∣ k) : SylowFourJoined (E (m + 2)) := by
  haveI := finite_E hm
  have hS0 : 0 < S := by have := Nat.two_pow_pos e; omega
  obtain ⟨hmem, hc, hx0, hxinj, hmul⟩ := orbit_E hm hn32 G' G0 n0 ι hι hG' hG0 hint ps hw0 hw R
    hRl hmat S hS T Sg Tr L SG horb PG NP PE PA PS PC hNP h2 hgens hpsi
  obtain ⟨P, hP⟩ := exists_sylow_eq _ (hc.trans hSe) hE hodd
  set x := xE m ps Tr
  have hcomm : ∀ i < S, ∀ j < S, (x i * x j = x j * x i ↔ lamAt S L i j = lamAt S L j i) := by
    intro i hi j hj
    rw [(hmul i hi j hj).2, (hmul j hj i hi).2]
    exact ⟨fun h => hxinj _ (hmul i hi j hj).1 _ (hmul j hj i hi).1 h, fun h => by rw [h]⟩
  have hsq : ∀ i < S, lamAt S L i i = 0 → x i * x i = 1 := fun i hi h => by
    rw [(hmul i hi i hi).2, h, hx0]
  refine klein_finish _ S hS0 x hmem hx0 hxinj nK (kp K) (kq K) (kr K) (kpar K) ?_ ?_ I ?_ ?_ P hP
  · intro idx hidx
    obtain ⟨hp, hq, h1, h2, h3, h4, h5, h6, h7, -⟩ := kleinAt_sound (hkl idx hidx)
    exact ⟨hp, hq, hsq _ hp h1, hsq _ hq h2, (hcomm _ hp _ hq).2 h3, h6, h4, h5,
      by rw [h7, (hmul _ hp _ hq).2]⟩
  · intro idx hidx h0
    obtain ⟨hp, hq, -, -, -, -, -, -, -, hpar⟩ := kleinAt_sound (hkl idx hidx)
    obtain ⟨hlt, c1, c2, c3, c4⟩ := hpar h0
    obtain ⟨hp', hq', -⟩ := kleinAt_sound (hkl _ (lt_trans hlt hidx))
    exact ⟨hlt, (hcomm _ hp _ hp').2 c1, (hcomm _ hp _ hq').2 c2, (hcomm _ hq _ hp').2 c3,
      (hcomm _ hq _ hq').2 c4⟩
  · intro i hi h1 h0
    refine (invAt_sound (hinv i hi)).1 ⟨?_, h0⟩
    rw [(hmul i hi i hi).2, ← hx0] at h1
    exact hxinj _ (hmul i hi i hi).1 0 hS0 h1
  · intro i hiI j hjI hi hj
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hiI
    obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.1 hjI
    have h := pairsAt_sound (hpairs a ha) b hb
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
    rcases h with h | h | ⟨hw, hiw, hjw⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl fun h' => h ((hcomm _ hi _ hj).1 h'))
    · exact Or.inr (Or.inr ⟨_, hw, hiw, hjw⟩)

end Spin

end CFSG.KC.SpinOrb

end
