module

public import CFSG.Certificates.Kernel.DceS5Mat
public import CFSG.Certificates.Kernel.DceLoops

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS
open scoped Classical

set_option exponentiation.threshold 400

abbrev F5 : Type := ZMod 5

@[expose] noncomputable def ln (x : Vec7) : Submodule F5 Vec7 := Submodule.span F5 {x}

@[expose] noncomputable def lk (P k : ℕ) : Submodule F5 Vec7 := ln (v7 (vk P k))

@[expose] noncomputable def pr (a b : Submodule F5 Vec7) : Finset (Submodule F5 Vec7) := {a, b}

abbrev Pt : Type := Finset (Finset (Submodule F5 Vec7))

@[expose] noncomputable def ptS (P : ℕ) : Pt :=
  {pr (lk P 0) (lk P 1), pr (lk P 2) (lk P 3), pr (lk P 4) (lk P 5)}

@[expose] noncomputable def mapL (A : Mat7) (l : Submodule F5 Vec7) : Submodule F5 Vec7 :=
  l.map A.vecMulLinear

@[expose] noncomputable def actP (p : Pt) (y : Mat7ˣ) : Pt :=
  p.image fun s => s.image (mapL (y : Mat7))

theorem mapL_ln (A : Mat7) (x : Vec7) : mapL A (ln x) = ln (Matrix.vecMul x A) := by
  unfold mapL ln
  rw [Submodule.map_span, Set.image_singleton, Matrix.vecMulLinear_apply]

theorem mapL_one (l : Submodule F5 Vec7) : mapL 1 l = l := by
  unfold mapL
  have e : (1 : Mat7).vecMulLinear = LinearMap.id := LinearMap.ext fun x => by simp
  rw [e, Submodule.map_id]

theorem mapL_mul (A B : Mat7) (l : Submodule F5 Vec7) : mapL B (mapL A l) = mapL (A * B) l := by
  unfold mapL
  rw [← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun x => by simp [Matrix.vecMul_vecMul]

theorem actP_one (p : Pt) : actP p 1 = p := by
  unfold actP
  have e : mapL ((1 : Mat7ˣ) : Mat7) = id := funext fun l => by rw [Units.val_one]; exact mapL_one l
  rw [e]
  simp only [Finset.image_id, Finset.image_id']

theorem actP_mul (p : Pt) (a b : Mat7ˣ) : actP (actP p a) b = actP p (a * b) := by
  unfold actP
  rw [Finset.image_image]
  refine Finset.image_congr fun s _ => ?_
  simp only [Function.comp_apply, Finset.image_image, Units.val_mul]
  refine Finset.image_congr fun l _ => ?_
  exact mapL_mul _ _ l

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem cast_ne_zero {l : ℕ} (h1 : 1 ≤ l) (h2 : l < 5) : (l : F5) ≠ 0 := by
  have : ∀ l : ℕ, l < 5 → 1 ≤ l → (l : ZMod 5) ≠ 0 := by decide
  exact this l h2 h1

theorem ln_smul {a : F5} (ha : a ≠ 0) (x : Vec7) : ln (a • x) = ln x :=
  Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 ha) x

theorem allL_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (f k)) n = true ↔ ∀ k < n, f k = true
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    change andB (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (f k)) n) (f n) = true ↔ _
    rw [andL_iff, allL_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact h1 k h
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem notL_iff (b : Bool) : notB b = true ↔ b = false := by
  cases b <;> decide

theorem canonP_spec {P : ℕ} (h : canonP P = true) :
    (∀ k < 6, normV (vk P k) = true) ∧ vk P 0 < vk P 1 ∧ vk P 2 < vk P 3 ∧ vk P 4 < vk P 5 ∧
      vk P 0 < vk P 2 ∧ vk P 2 < vk P 4 := by
  unfold canonP at h
  obtain ⟨h1, h⟩ := andL_iff.1 h
  obtain ⟨h2, h⟩ := andL_iff.1 h
  obtain ⟨h3, h⟩ := andL_iff.1 h
  obtain ⟨h4, h⟩ := andL_iff.1 h
  obtain ⟨h5, h6⟩ := andL_iff.1 h
  exact ⟨(allL_iff (fun k => normV (vk P k)) 6).1 h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, Nat.blt_eq.mp h4,
    Nat.blt_eq.mp h5, Nat.blt_eq.mp h6⟩

theorem hL_bnd (h k : ℕ) : 1 ≤ hL h k ∧ hL h k < 5 := by
  unfold hL
  have := CFSG.Certificates.DceLoop.bitsG_lt h (Nat.add (Nat.mul 5 k) 3) 2
  change 1 ≤ Nat.succ (CFSG.Certificates.DceLoop.bitsG h (Nat.add (Nat.mul 5 k) 3) 2) ∧
    Nat.succ (CFSG.Certificates.DceLoop.bitsG h (Nat.add (Nat.mul 5 k) 3) 2) < 5
  have h4 : CFSG.Certificates.DceLoop.bitsG h (Nat.add (Nat.mul 5 k) 3) 2 < 4 :=
    lt_of_lt_of_eq this (by norm_num)
  omega

theorem actOK_spec {P M Q h : ℕ} (hok : actOK P M Q h = true) :
    (∀ k < 6, hT h k < 6 ∧ vec7 (vk P k) M = scal (hL h k) (vk Q (hT h k))) ∧
      hT h 1 = Nat.xor (hT h 0) 1 ∧ hT h 3 = Nat.xor (hT h 2) 1 ∧ hT h 5 = Nat.xor (hT h 4) 1 ∧
      hT h 0 >>> 1 ≠ hT h 2 >>> 1 ∧ hT h 0 >>> 1 ≠ hT h 4 >>> 1 ∧ hT h 2 >>> 1 ≠ hT h 4 >>> 1 := by
  unfold actOK at hok
  obtain ⟨h1, r⟩ := andL_iff.1 hok
  obtain ⟨h2, r⟩ := andL_iff.1 r
  obtain ⟨h3, r⟩ := andL_iff.1 r
  obtain ⟨h4, r⟩ := andL_iff.1 r
  obtain ⟨h5, r⟩ := andL_iff.1 r
  obtain ⟨h6, h7⟩ := andL_iff.1 r
  refine ⟨fun k hk => ?_, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.ne_of_beq_eq_false ((notL_iff _).1 h5),
    Nat.ne_of_beq_eq_false ((notL_iff _).1 h6), Nat.ne_of_beq_eq_false ((notL_iff _).1 h7)⟩
  have e := (allL_iff (fun k => andB (Nat.blt (hT h k) 6)
    (Nat.beq (vec7 (vk P k) M) (scal (hL h k) (vk Q (hT h k))))) 6).1 h1 k hk
  obtain ⟨e1, e2⟩ := andL_iff.1 e
  exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2⟩

section Act

variable (hc : constsOK7 = true)
include hc

theorem canonP_V7 {P : ℕ} (h : canonP P = true) (k : ℕ) (hk : k < 6) : V7 (vk P k) :=
  (normV_spec hc ((canonP_spec h).1 k hk)).1

theorem lk_act {P M Q h : ℕ} (hok : actOK P M Q h = true) (hP : canonP P = true)
    (hQ : canonP Q = true) (hM : C7 M) (k : ℕ) (hk : k < 6) :
    mapL (m7 M) (lk P k) = lk Q (hT h k) := by
  obtain ⟨ht, he⟩ := (actOK_spec hok).1 k hk
  have hv := vec7_sound hc (canonP_V7 hc hP k hk) hM
  obtain ⟨-, hs⟩ := scal_sound hc (canonP_V7 hc hQ _ ht) (hL_bnd h k).2
  unfold lk
  rw [mapL_ln, ← hv.2, he, hs, ln_smul (cast_ne_zero (hL_bnd h k).1 (hL_bnd h k).2)]

omit hc in
theorem pr_xor (L : ℕ → Submodule F5 Vec7) {t : ℕ} (ht : t < 6) :
    pr (L t) (L (Nat.xor t 1)) = pr (L (2 * (t >>> 1))) (L (2 * (t >>> 1) + 1)) := by
  unfold pr
  interval_cases t <;> first | rfl | exact Finset.pair_comm _ _

omit hc in
theorem perm3 (Pq : ℕ → Finset (Submodule F5 Vec7)) {a b c : ℕ} (ha : a < 3) (hb : b < 3)
    (hc3 : c < 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({Pq a, Pq b, Pq c} : Pt) = {Pq 0, Pq 1, Pq 2} := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | skip
  all_goals
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    try tauto

theorem actOK_sound {P M Q h : ℕ} (hok : actOK P M Q h = true) (hP : canonP P = true)
    (hQ : canonP Q = true) (hM : C7 M) {y : Mat7ˣ} (hy : (y : Mat7) = m7 M) :
    actP (ptS P) y = ptS Q := by
  obtain ⟨hk, h1, h3, h5, d02, d04, d24⟩ := actOK_spec hok
  have hpr : ∀ i < 3, (pr (lk P (2 * i)) (lk P (2 * i + 1))).image (mapL (y : Mat7)) =
      pr (lk Q (2 * (hT h (2 * i) >>> 1))) (lk Q (2 * (hT h (2 * i) >>> 1) + 1)) := by
    intro i hi
    have hx : hT h (2 * i + 1) = Nat.xor (hT h (2 * i)) 1 := by
      interval_cases i
      · exact h1
      · exact h3
      · exact h5
    unfold pr
    rw [Finset.image_insert, Finset.image_singleton, hy, lk_act hc hok hP hQ hM _ (by omega),
      lk_act hc hok hP hQ hM _ (by omega), hx]
    exact pr_xor (lk Q) (hk _ (by omega)).1
  unfold actP ptS
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  rw [hpr 0 (by norm_num), hpr 1 (by norm_num), hpr 2 (by norm_num)]
  have hlt : ∀ k < 6, hT h k >>> 1 < 3 := fun k hk' => by
    have := (hk k hk').1
    rw [Nat.shiftRight_eq_div_pow]
    omega
  exact perm3 (fun t => pr (lk Q (2 * t)) (lk Q (2 * t + 1))) (hlt 0 (by norm_num))
    (hlt 2 (by norm_num)) (hlt 4 (by norm_num)) d02 d04 d24

theorem actOK_zero {P Q h : ℕ} (hok : actOK P 0 Q h = true) (hP : canonP P = true)
    (hQ : canonP Q = true) : False := by
  obtain ⟨ht, he⟩ := (actOK_spec hok).1 0 (by norm_num)
  have hv := vec7_sound hc (canonP_V7 hc hP 0 (by norm_num)) zero7.1
  rw [zero7.2, Matrix.vecMul_zero] at hv
  have hz : vec7 (vk P 0) 0 = 0 := v7_inj hv.1 zeroV.1 (hv.2.trans zeroV.2.symm)
  obtain ⟨hsV, hs⟩ := scal_sound hc (canonP_V7 hc hQ _ ht) (hL_bnd h 0).2
  rw [← he, hz, zeroV.2] at hs
  have h0 : v7 (vk Q (hT h 0)) = 0 := by
    rcases smul_eq_zero.1 hs.symm with h1 | h1
    · exact absurd h1 (cast_ne_zero (hL_bnd h 0).1 (hL_bnd h 0).2)
    · exact h1
  have := v7_inj (canonP_V7 hc hQ _ ht) zeroV.1 (h0.trans zeroV.2.symm)
  have hpos := (normV_spec hc ((canonP_spec hQ).1 _ ht)).2.1
  omega

theorem line_inj {u v : ℕ} (hu : normV u = true) (hv : normV v = true) (h : ln (v7 u) = ln (v7 v)) :
    u = v := by
  obtain ⟨Vu, pu, lu⟩ := normV_spec hc hu
  obtain ⟨Vv, pv, lv⟩ := normV_spec hc hv
  have hmem : ∀ {x y : ℕ}, V7 x → V7 y → 0 < y → (∀ l, 2 ≤ l → l < 5 → x < scal l x) →
      ln (v7 x) = ln (v7 y) → x = y ∨ x < y := by
    intro x y Vx Vy py lx hxy
    have hy : v7 y ∈ ln (v7 x) := by
      rw [hxy]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hy
    have hval : ((a.val : ℕ) : F5) = a := ZMod.natCast_zmod_val a
    have hlt : a.val < 5 := ZMod.val_lt a
    obtain ⟨Vs, hs⟩ := scal_sound hc Vx hlt
    rw [hval, ha] at hs
    have e : scal a.val x = y := v7_inj Vs Vy hs
    rcases Nat.lt_or_ge a.val 2 with h2 | h2
    · interval_cases hav : a.val
      · rw [← e] at py
        have h0 : v7 (scal 0 x) = 0 := by
          rw [(scal_sound hc Vx (by norm_num)).2]
          simp
        have := v7_inj (scal_sound hc Vx (by norm_num)).1 zeroV.1 (h0.trans zeroV.2.symm)
        omega
      · left
        have h1 : v7 (scal 1 x) = v7 x := by
          rw [(scal_sound hc Vx (by norm_num)).2]
          simp
        rw [← e]
        exact (v7_inj (scal_sound hc Vx (by norm_num)).1 Vx h1).symm
    · right
      rw [← e]
      exact lx _ h2 hlt
  rcases hmem Vu Vv pv lu h with e | e
  · exact e
  · rcases hmem Vv Vu pu lv h.symm with e' | e'
    · exact e'.symm
    · omega

omit hc in
theorem pr_eq_pr {a b c d : Submodule F5 Vec7} (h : pr a b = pr c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h' : (({a, b} : Finset _) : Set (Submodule F5 Vec7)) = (({c, d} : Finset _) : Set _) := by
    unfold pr at h
    rw [h]
  rw [Finset.coe_pair, Finset.coe_pair] at h'
  exact Set.pair_eq_pair_iff.1 h'

omit hc in
theorem pairs_eq {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : ℕ}
    (ha : a0 < a1 ∧ a2 < a3 ∧ a4 < a5 ∧ a0 < a2 ∧ a2 < a4)
    (hb : b0 < b1 ∧ b2 < b3 ∧ b4 < b5 ∧ b0 < b2 ∧ b2 < b4)
    (h0 : ((a0 = b0 ∧ a1 = b1) ∨ (a0 = b1 ∧ a1 = b0)) ∨ ((a0 = b2 ∧ a1 = b3) ∨ (a0 = b3 ∧ a1 = b2)) ∨
      ((a0 = b4 ∧ a1 = b5) ∨ (a0 = b5 ∧ a1 = b4)))
    (h1 : ((a2 = b0 ∧ a3 = b1) ∨ (a2 = b1 ∧ a3 = b0)) ∨ ((a2 = b2 ∧ a3 = b3) ∨ (a2 = b3 ∧ a3 = b2)) ∨
      ((a2 = b4 ∧ a3 = b5) ∨ (a2 = b5 ∧ a3 = b4)))
    (h2 : ((a4 = b0 ∧ a5 = b1) ∨ (a4 = b1 ∧ a5 = b0)) ∨ ((a4 = b2 ∧ a5 = b3) ∨ (a4 = b3 ∧ a5 = b2)) ∨
      ((a4 = b4 ∧ a5 = b5) ∨ (a4 = b5 ∧ a5 = b4))) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 := by
  obtain ⟨a01, a23, a45, a02, a24⟩ := ha
  obtain ⟨b01, b23, b45, b02, b24⟩ := hb
  rcases h0 with (⟨e0, e1⟩ | ⟨e0, e1⟩) | (⟨e0, e1⟩ | ⟨e0, e1⟩) | (⟨e0, e1⟩ | ⟨e0, e1⟩) <;>
  rcases h1 with (⟨e2, e3⟩ | ⟨e2, e3⟩) | (⟨e2, e3⟩ | ⟨e2, e3⟩) | (⟨e2, e3⟩ | ⟨e2, e3⟩) <;>
  rcases h2 with (⟨e4, e5⟩ | ⟨e4, e5⟩) | (⟨e4, e5⟩ | ⟨e4, e5⟩) | (⟨e4, e5⟩ | ⟨e4, e5⟩) <;>
  omega

omit hc in
theorem eq_of_vk {P Q : ℕ} (hP : P < 2 ^ 336) (hQ : Q < 2 ^ 336) (h : ∀ k < 6, vk P k = vk Q k) :
    P = Q := by
  have hv : ∀ X k, vk X k = X / 2 ^ (56 * k) % 2 ^ 56 := fun X k => by
    unfold vk
    change (X >>> (56 * k)) &&& 72057594037927935 = _
    rw [show (72057594037927935 : ℕ) = 2 ^ 56 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 336
  · have hk : i / 56 < 6 := by omega
    have e := congrArg (fun x => x.testBit (i % 56)) (h _ hk)
    simp only [hv, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at e
    have e2 : i % 56 + 56 * (i / 56) = i := by omega
    rw [e2] at e
    simpa [Nat.mod_lt i (show 56 > 0 by norm_num)] using e
  · rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem ptS_inj {P Q : ℕ} (hP : canonP P = true) (hQ : canonP Q = true) (hP' : P < 2 ^ 336)
    (hQ' : Q < 2 ^ 336) (h : ptS P = ptS Q) : P = Q := by
  obtain ⟨nP, oP⟩ := canonP_spec hP
  obtain ⟨nQ, oQ⟩ := canonP_spec hQ
  have li : ∀ k < 6, ∀ k' < 6, lk P k = lk Q k' → vk P k = vk Q k' := fun k hk k' hk' e =>
    line_inj hc (nP k hk) (nQ k' hk') e
  have mem : ∀ i < 3, pr (lk P (2 * i)) (lk P (2 * i + 1)) ∈ ptS Q := by
    intro i hi
    rw [← h]
    unfold ptS
    interval_cases i <;> simp
  have key : ∀ i < 3,
      ((vk P (2 * i) = vk Q 0 ∧ vk P (2 * i + 1) = vk Q 1) ∨
        (vk P (2 * i) = vk Q 1 ∧ vk P (2 * i + 1) = vk Q 0)) ∨
      ((vk P (2 * i) = vk Q 2 ∧ vk P (2 * i + 1) = vk Q 3) ∨
        (vk P (2 * i) = vk Q 3 ∧ vk P (2 * i + 1) = vk Q 2)) ∨
      ((vk P (2 * i) = vk Q 4 ∧ vk P (2 * i + 1) = vk Q 5) ∨
        (vk P (2 * i) = vk Q 5 ∧ vk P (2 * i + 1) = vk Q 4)) := by
    intro i hi
    have hm := mem i hi
    unfold ptS at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with e | e | e <;> rcases pr_eq_pr e with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl (Or.inl ⟨li _ (by omega) _ (by norm_num) e1, li _ (by omega) _ (by norm_num) e2⟩)
    · exact Or.inl (Or.inr ⟨li _ (by omega) _ (by norm_num) e1, li _ (by omega) _ (by norm_num) e2⟩)
    · exact Or.inr (Or.inl (Or.inl ⟨li _ (by omega) _ (by norm_num) e1,
        li _ (by omega) _ (by norm_num) e2⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨li _ (by omega) _ (by norm_num) e1,
        li _ (by omega) _ (by norm_num) e2⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨li _ (by omega) _ (by norm_num) e1,
        li _ (by omega) _ (by norm_num) e2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨li _ (by omega) _ (by norm_num) e1,
        li _ (by omega) _ (by norm_num) e2⟩))
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pairs_eq oP oQ (key 0 (by norm_num)) (key 1 (by norm_num))
    (key 2 (by norm_num))
  apply eq_of_vk hP' hQ'
  intro k hk
  interval_cases k
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5

end Act

end CFSG.Certificates.DS5

end
