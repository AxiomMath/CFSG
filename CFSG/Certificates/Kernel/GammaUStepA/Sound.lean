
module

public import Certificates.Data.Kernel.GammaUStepA.Defs
public import CFSG.Certificates.Kernel.GammaUNormSound
public import CFSG.Certificates.Kernel.GammaUSigmaSoundBase
public import CFSG.GF2Type.Smith1979.GammaU.StepABase

public section

namespace CFSG.KC.GUA

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem recAll_iff {α : Type} (f : α → Bool) (l : List α) :
    List.rec (motive := fun _ => Bool) true (fun d _ ih => f d && ih) l = true ↔
      ∀ d ∈ l, f d = true := by
  induction l with
  | nil => exact iff_of_true rfl (by simp)
  | cons a l ih =>
    change (f a && List.rec (motive := fun _ => Bool) true (fun d _ ih => f d && ih) l) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

theorem selX_cons (a : ℕ) (l : List ℕ) (m : ℕ) :
    selX (a :: l) m = (m % 2 * a) ^^^ selX l (m / 2) := rfl

theorem vecOf_bit (m a : ℕ) : vecOf (m % 2 * a) = ((m % 2 : ℕ) : ZMod 2) • vecOf a := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> simp

theorem selX_lt : ∀ (l : List ℕ), (∀ x ∈ l, x < 4096) → ∀ m, selX l m < 4096
  | [], _, _ => by change 0 < 4096; norm_num
  | a :: l, h, m => by
    rw [selX_cons]
    refine xor_lt ?_ (selX_lt l (fun x hx => h x (List.mem_cons_of_mem a hx)) _)
    have ha := h a List.mem_cons_self
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h0 <;> rw [h0] <;> omega

theorem selX_apply {f : V12 →ₗ[ZMod 2] V12} {B C : List ℕ}
    (hBC : List.Forall₂ (fun b c => f (vecOf b) = vecOf c) B C) (m : ℕ) :
    f (vecOf (selX B m)) = vecOf (selX C m) := by
  induction hBC generalizing m with
  | nil => change f (vecOf 0) = vecOf 0; simp
  | cons h _ ih =>
    rw [selX_cons, selX_cons, vecOf_xor, vecOf_xor, map_add, vecOf_bit, vecOf_bit, map_smul, h, ih]

theorem selX_mem {f : V12 →ₗ[ZMod 2] V12} {S : Submodule (ZMod 2) V12} {B : List ℕ}
    (hB : ∀ b ∈ B, f (vecOf b) ∈ S) (m : ℕ) : f (vecOf (selX B m)) ∈ S := by
  induction B generalizing m with
  | nil => change f (vecOf 0) ∈ S; simp
  | cons b B ih =>
    rw [selX_cons, vecOf_xor, map_add, vecOf_bit, map_smul]
    exact S.add_mem (S.smul_mem _ (hB b List.mem_cons_self))
      (ih (fun x hx => hB x (List.mem_cons_of_mem b hx)) _)

theorem vec_add_self (x : V12) : x + x = 0 := by
  rw [← vec_sub_eq_add, sub_self]

theorem vec_add_eq_iff {x y z : V12} : x + y = z ↔ x = y + z := by
  rw [← eq_sub_iff_add_eq, vec_sub_eq_add, add_comm]

theorem a0_ne : vecOf a0 ≠ 0 := fun h =>
  absurd ((vecOf_eq_zero (by decide : a0 < 4096)).1 h) (by decide)

theorem ne_add_a0 (x : V12) : x ≠ x + vecOf a0 := fun h =>
  a0_ne (add_left_cancel (h.symm.trans (add_zero x).symm))

theorem comm_or {l : GL} {d : V12} (h : l d - d = 0 ∨ l d - d = vecOf a0) :
    l d = d ∨ l d = d + vecOf a0 := by
  rcases h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (by rw [← h]; abel)

theorem xor_a0_iff {P d : ℕ} {G : GL} (hP : IsP G P) (hd : d < 4096) :
    ap12 P d ^^^ d = 3072 ↔ G (vecOf d) = vecOf d + vecOf a0 := by
  have hv : vecOf (ap12 P d ^^^ d) = G (vecOf d) + vecOf d := by
    rw [vecOf_xor, hP.apply_code]
  constructor
  · intro h
    rw [h] at hv
    exact vec_add_eq_iff.1 hv.symm
  · intro h
    refine vecOf_inj (xor_lt (ap12_lt _ _) hd) (by norm_num) ?_
    rw [hv, h, add_comm (vecOf d), add_assoc, vec_add_self, add_zero]
    rfl

@[expose] noncomputable def lamM (B : List ℕ) (g : GL) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun d _ ih => (if g (vecOf d) = vecOf d + vecOf a0 then 1 else 0) + 2 * ih) B

theorem lamM_cons (d : ℕ) (B : List ℕ) (g : GL) :
    lamM (d :: B) g = (if g (vecOf d) = vecOf d + vecOf a0 then 1 else 0) + 2 * lamM B g := rfl

theorem lamM_lt (g : GL) : ∀ B : List ℕ, lamM B g < 2 ^ B.length
  | [] => by change 0 < 1; norm_num
  | d :: B => by
    have := lamM_lt g B
    rw [lamM_cons, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem lamM_bit (g : GL) : ∀ (B : List ℕ) (i : ℕ) (hi : i < B.length),
    lamM B g / 2 ^ i % 2 = if g (vecOf B[i]) = vecOf B[i] + vecOf a0 then 1 else 0
  | [], i, hi => absurd hi (by simp)
  | d :: B, 0, _ => by
    rw [lamM_cons, pow_zero, Nat.div_one]
    simp only [List.getElem_cons_zero]
    split_ifs <;> omega
  | d :: B, i + 1, hi => by
    have h2 : ((if g (vecOf d) = vecOf d + vecOf a0 then 1 else 0) + 2 * lamM B g) / 2 =
        lamM B g := by
      split_ifs <;> omega
    rw [lamM_cons, Nat.pow_succ', ← Nat.div_div_eq_div_mul, h2,
      lamM_bit g B i (by simpa using hi)]
    simp only [List.getElem_cons_succ]

theorem comm_bit {g : GL} {d : V12} (h : g d = d ∨ g d = d + vecOf a0) :
    g d = d + (((if g d = d + vecOf a0 then 1 else 0 : ℕ)) : ZMod 2) • vecOf a0 := by
  split_ifs with h'
  · simpa using h'
  · rcases h with h | h
    · simpa using h
    · exact absurd h h'

theorem lamM_one : ∀ B : List ℕ, lamM B 1 = 0
  | [] => rfl
  | d :: B => by
    have hn : ¬ ((1 : GL) (vecOf d) = vecOf d + vecOf a0) := ne_add_a0 (vecOf d)
    simp only [lamM_cons, lamM_one B, hn, if_false, mul_zero, add_zero]

theorem lamM_inj {B : List ℕ} {g h : GL}
    (hg : ∀ b ∈ B, g (vecOf b) = vecOf b ∨ g (vecOf b) = vecOf b + vecOf a0)
    (hh : ∀ b ∈ B, h (vecOf b) = vecOf b ∨ h (vecOf b) = vecOf b + vecOf a0)
    (he : lamM B g = lamM B h) : ∀ b ∈ B, g (vecOf b) = h (vecOf b) := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have e1 := lamM_bit g B i hi
  have e2 := lamM_bit h B i hi
  rw [he, e2] at e1
  rw [comm_bit (hg _ hb), comm_bit (hh _ hb), e1]

theorem lamM_mul {B : List ℕ} {g h : GL} (ha : g (vecOf a0) = vecOf a0)
    (hg : ∀ b ∈ B, g (vecOf b) = vecOf b ∨ g (vecOf b) = vecOf b + vecOf a0)
    (hh : ∀ b ∈ B, h (vecOf b) = vecOf b ∨ h (vecOf b) = vecOf b + vecOf a0) :
    lamM B (g * h) = lamM B g ^^^ lamM B h := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  by_cases hi : i < B.length
  · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      Nat.testBit_eq_decide_div_mod_eq, lamM_bit _ B i hi,
      lamM_bit _ B i hi, lamM_bit _ B i hi]
    have hb := List.getElem_mem hi
    have ne := ne_add_a0
    have aa : ∀ x : V12, x + vecOf a0 + vecOf a0 = x := fun x => by
      rw [add_assoc, vec_add_self, add_zero]
    rw [LinearEquiv.mul_apply]
    rcases hg _ hb with h1 | h1 <;> rcases hh _ hb with h2 | h2
    · rw [h2, h1]; simp [ne]
    · rw [h2, map_add, h1, ha]; simp [ne]
    · rw [h2, h1]; simp [ne]
    · rw [h2, map_add, h1, ha, aa]; simp [ne]
  · have hle : 2 ^ B.length ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (lamM_lt _ B) hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (lamM_lt _ B) hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (lamM_lt _ B) hle)]
    rfl

theorem rhoL_eq {P : ℕ} {G : GL} (hP : IsP G P) :
    ∀ B : List ℕ, (∀ d ∈ B, d < 4096) → rhoL B P = lamM B G
  | [], _ => rfl
  | d :: B, hB => by
    have ih := rhoL_eq hP B fun x hx => hB x (List.mem_cons_of_mem d hx)
    change (bif Nat.beq (ap12 P d ^^^ d) 3072 then 1 else 0) + 2 * rhoL B P = _
    rw [lamM_cons, ih]
    congr 1
    have key := xor_a0_iff hP (hB d List.mem_cons_self)
    cases hc : Nat.beq (ap12 P d ^^^ d) 3072
    · rw [if_neg fun h => Nat.ne_of_beq_eq_false hc (key.2 h)]
      rfl
    · rw [if_pos (key.1 (Nat.eq_of_beq_eq_true hc))]
      rfl

theorem lamM_injL {R5 : List ℕ} {L : Subgroup GL} (H : Hyp (vecOf a0) (spanOf (R5 ++ [a0])) L)
    {l l' : GL} (hl : l ∈ L) (hl' : l' ∈ L) (h : lamM R5 l = lamM R5 l') : l = l' := by
  have hc : ∀ {u : GL}, u ∈ L → ∀ b ∈ R5,
      u (vecOf b) = vecOf b ∨ u (vecOf b) = vecOf b + vecOf a0 := fun hu b hb =>
    comm_or (H.comm _ hu _ (mem_spanOf_of_mem (List.mem_append_left _ hb)))
  have hR : ∀ d ∈ R5 ++ [a0], l (vecOf d) = l' (vecOf d) := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact lamM_inj (hc hl) (hc hl') h d hd
    · rw [List.mem_singleton.1 hd, H.fix l hl, H.fix l' hl']
  have hfix : ∀ y ∈ spanOf (R5 ++ [a0]), (l⁻¹ * l') y = y := by
    intro y hy
    have := eqOn_spanOf (f := (l' : V12 →ₗ[ZMod 2] V12)) (g := (l : V12 →ₗ[ZMod 2] V12))
      (fun d hd => (hR d hd).symm) y hy
    simp only [LinearEquiv.coe_coe] at this
    rw [LinearEquiv.mul_apply, this, inv_apply_apply]
  exact inv_mul_eq_one.1 (H.faithful _ (mul_mem (inv_mem hl) hl') hfix)

@[expose] noncomputable def parN (n x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih x => Nat.xor (Nat.mod x 2) (ih (Nat.div x 2))) n x

theorem parN_succ (n x : ℕ) : parN (n + 1) x = (x % 2) ^^^ parN n (x / 2) := rfl

theorem xor_le_one {u v : ℕ} (hu : u ≤ 1) (hv : v ≤ 1) : u ^^^ v ≤ 1 := by
  interval_cases u <;> interval_cases v <;> decide

theorem parN_le : ∀ n x, parN n x ≤ 1
  | 0, _ => by change 0 ≤ 1; norm_num
  | n + 1, x => by
    rw [parN_succ]
    exact xor_le_one (by omega) (parN_le n _)

theorem cast_xor {u v : ℕ} (hu : u ≤ 1) (hv : v ≤ 1) :
    ((u ^^^ v : ℕ) : ZMod 2) = (u : ZMod 2) + (v : ZMod 2) := by
  interval_cases u <;> interval_cases v <;> decide

theorem land_div_two (a b : ℕ) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ]

theorem land_mod_two (a b : ℕ) : (a &&& b) % 2 = a % 2 * (b % 2) := by
  have h := Nat.testBit_and a b 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one (a &&& b) with hab | hab <;> simp_all

theorem parSel {l : GL} {a : V12} : ∀ (B : List ℕ) (φ : ℕ),
    (∀ i (hi : i < B.length), l (vecOf B[i]) = vecOf B[i] + ((φ / 2 ^ i % 2 : ℕ) : ZMod 2) • a) →
    ∀ m, l (vecOf (selX B m)) = vecOf (selX B m) + ((parN B.length (φ &&& m) : ℕ) : ZMod 2) • a
  | [], φ, _, m => by
    change l (vecOf 0) = vecOf 0 + ((0 : ℕ) : ZMod 2) • a
    simp
  | b :: B, φ, h, m => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, pow_zero, Nat.div_one] at h0
    have h1 : ∀ i (hi : i < B.length),
        l (vecOf B[i]) = vecOf B[i] + (((φ / 2) / 2 ^ i % 2 : ℕ) : ZMod 2) • a := fun i hi => by
      have := h (i + 1) (by simpa using hi)
      rwa [List.getElem_cons_succ, Nat.pow_succ', ← Nat.div_div_eq_div_mul] at this
    have hb : (φ &&& m) % 2 ≤ 1 := by have := Nat.mod_lt (φ &&& m) two_pos; omega
    rw [selX_cons, vecOf_xor, map_add, vecOf_bit, map_smul, h0, parSel B (φ / 2) h1 (m / 2),
      List.length_cons, parN_succ, land_div_two,
      cast_xor (u := (φ &&& m) % 2) (v := parN B.length (φ / 2 &&& m / 2)) hb (parN_le _ _),
      land_mod_two, Nat.cast_mul]
    module

theorem natRec_count (f : ℕ → Bool) (n : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => Nat.add ih (bif f k then 1 else 0)) n =
      ((Finset.range n).filter (fun k => f k = true)).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.add (Nat.rec (motive := fun _ => ℕ) 0
      (fun k ih => Nat.add ih (bif f k then 1 else 0)) n) (bif f n then 1 else 0) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    cases hf : f n
    · simp
    · simp

theorem cntW_eq (W : List (List ℕ)) :
    cntW W = ((Finset.range 32).filter (fun k => vanW W k = true)).card :=
  natRec_count (vanW W) 32

theorem thetaOK_spec (h : thetaOK = true) :
    theta0N 3072 ≠ 0 ∧ theta0N 3072 ≠ 3072 ∧ 48 ∈ d0 ∧ theta0N 48 = 3072 := by
  unfold thetaOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩, -⟩ := h
  refine ⟨fun e => ?_, fun e => ?_, (memN_iff _ _).1 h4, Nat.eq_of_beq_eq_true h5⟩
  · rw [e] at h1
    exact absurd h1 (by decide)
  · rw [e] at h2
    exact absurd h2 (by decide)

theorem fix_of_theta (ht : thetaOK = true) {l : GL} (hu : ∀ x, l (theta0 x) = theta0 (l x))
    {x₁ x₂ : ℕ} (h₁ : x₁ < 4096) (hθ : theta0N x₁ = x₂) {c₁ c₂ : ZMod 2}
    (e₁ : l (vecOf x₁) = vecOf x₁ + c₁ • vecOf a0) (e₂ : l (vecOf x₂) = vecOf x₂ + c₂ • vecOf a0) :
    c₁ = 0 ∧ c₂ = 0 := by
  obtain ⟨t1, t2, -, -⟩ := thetaOK_spec ht
  have hx : theta0 (vecOf x₁) = vecOf x₂ := by rw [← vecOf_theta0N h₁, hθ]
  have e := hu (vecOf x₁)
  rw [hx, e₂, e₁, map_add, map_smul, hx, ← vecOf_theta0N (by decide : a0 < 4096)] at e
  have e' := add_left_cancel e
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hta : theta0N a0 < 4096 := theta0N_lt (by decide)
  rcases hc c₁ with rfl | rfl <;> rcases hc c₂ with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [one_smul, zero_smul] at e'
    exact absurd e' a0_ne
  · simp only [one_smul, zero_smul] at e'
    exact absurd ((vecOf_eq_zero hta).1 e'.symm) t1
  · simp only [one_smul] at e'
    exact absurd (vecOf_inj (by decide) hta e').symm t2

theorem cast_par_eq_zero {p : ℕ} (hp : p ≤ 1) (h : (p : ZMod 2) = 0) : p = 0 := by
  interval_cases p
  · rfl
  · exact absurd h (by decide)

theorem t1_false (ht : thetaOK = true) {R5 : List ℕ} (hlen : R5.length = 5)
    (hlt : ∀ r ∈ R5, r < 4096) {W : List (List ℕ)} (h : t1OK (R5 ++ [a0]) W = true)
    {L : Subgroup GL} (H : Hyp (vecOf a0) (spanOf (R5 ++ [a0])) L) : False := by
  classical
  unfold t1OK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, hcnt⟩ := h
  have hw' := (recAll_iff (fun w => Nat.beq (theta0N (selX (R5 ++ [a0]) (nthD 0 w 0)))
    (selX (R5 ++ [a0]) (nthD 0 w 1))) W).1 hw
  have hcnt' : cntW W < 16 := by simpa using hcnt
  have hRlt : ∀ r ∈ R5 ++ [a0], r < 4096 := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hlt r hr
    · rw [List.mem_singleton.1 hr]; decide
  have hRlen : (R5 ++ [a0]).length = 6 := by simp [hlen]
  have hcB : ∀ {u : GL}, u ∈ L → ∀ b ∈ R5,
      u (vecOf b) = vecOf b ∨ u (vecOf b) = vecOf b + vecOf a0 := fun hu b hb =>
    comm_or (H.comm _ hu _ (mem_spanOf_of_mem (List.mem_append_left _ hb)))
  have hvan : ∀ u ∈ L, (∀ x, u (theta0 x) = theta0 (u x)) → vanW W (lamM R5 u) = true := by
    intro u hu hun
    have hφ : lamM R5 u < 32 := by have := lamM_lt u R5; rwa [hlen] at this
    have hbits : ∀ i (hi : i < (R5 ++ [a0]).length), u (vecOf (R5 ++ [a0])[i]) =
        vecOf (R5 ++ [a0])[i] + ((lamM R5 u / 2 ^ i % 2 : ℕ) : ZMod 2) • vecOf a0 := by
      intro i hi
      rcases (by omega : i < 5 ∨ i = 5) with hi5 | rfl
      · rw [List.getElem_append_left (by omega), lamM_bit u R5 i (by omega)]
        exact comm_bit (hcB hu _ (List.getElem_mem _))
      · have h32 : lamM R5 u / 2 ^ 5 % 2 = 0 := by
          rw [Nat.div_eq_of_lt (by norm_num; exact hφ)]
        have hget : (R5 ++ [a0])[5]'hi = a0 := by
          rw [List.getElem_append_right (by omega)]
          simp [hlen]
        rw [h32, hget, Nat.cast_zero, zero_smul, add_zero]
        exact H.fix u hu
    have hpar := parSel (l := u) (a := vecOf a0) _ _ hbits
    rw [hRlen] at hpar
    refine (recAll_iff _ W).2 fun w hwW => ?_
    have hθ := Nat.eq_of_beq_eq_true (hw' w hwW)
    obtain ⟨c1, c2⟩ := fix_of_theta ht hun (selX_lt _ hRlt _) hθ (hpar _) (hpar _)
    rw [Bool.and_eq_true]
    rw [Nat.beq_eq, Nat.beq_eq]
    exact ⟨cast_par_eq_zero (parN_le 6 _) c1, cast_par_eq_zero (parN_le 6 _) c2⟩
  obtain ⟨g₀, hg₀, hg₀u⟩ : ∃ g₀ ∈ L, ∀ l ∈ L, ¬ (∀ x, l (theta0 x) = theta0 (l x)) →
      ∀ x, (g₀⁻¹ * l) (theta0 x) = theta0 ((g₀⁻¹ * l) x) := by
    by_cases hex : ∃ g₀ ∈ L, ∀ x, g₀ (theta0 x) = theta0 (theta0 (g₀ x))
    · obtain ⟨g₀, hg₀, ha₀⟩ := hex
      refine ⟨g₀, hg₀, fun l hl hnu x => ?_⟩
      have ha : ∀ x, l (theta0 x) = theta0 (theta0 (l x)) :=
        Or.resolve_left (mem_gammaU.1 (H.le hl)).2 hnu
      have hinv : ∀ y, g₀⁻¹ (theta0 (theta0 y)) = theta0 (g₀⁻¹ y) := fun y => by
        have := ha₀ (g₀⁻¹ y)
        rw [apply_inv_apply] at this
        rw [← this, inv_apply_apply]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hinv]
    · refine ⟨1, one_mem _, fun l hl hnu => absurd ⟨l, hl, Or.resolve_left (mem_gammaU.1 (H.le hl)).2 hnu⟩ hex⟩
  set S := (Finset.range 32).filter (fun k => vanW W k = true) with hS
  have hmemS : ∀ u ∈ L, (∀ x, u (theta0 x) = theta0 (u x)) → lamM R5 u ∈ S := fun u hu hun => by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := lamM_lt u R5; rwa [hlen] at this, hvan u hu hun⟩
  let ψ : L → S ⊕ S := fun l =>
    if hU : ∀ x, (l : GL) (theta0 x) = theta0 ((l : GL) x) then
      .inl ⟨lamM R5 l, hmemS _ l.2 hU⟩
    else .inr ⟨lamM R5 (g₀⁻¹ * l), hmemS _ (mul_mem (inv_mem hg₀) l.2) (hg₀u _ l.2 hU)⟩
  have hψ : Function.Injective ψ := by
    intro l l' e
    simp only [ψ] at e
    split_ifs at e
    all_goals first
      | exact (Sum.inl_ne_inr e).elim
      | exact (Sum.inr_ne_inl e).elim
      | exact Subtype.ext (lamM_injL H l.2 l'.2 (congrArg Subtype.val (Sum.inl.inj e)))
      | exact Subtype.ext (mul_left_cancel (lamM_injL H (mul_mem (inv_mem hg₀) l.2)
          (mul_mem (inv_mem hg₀) l'.2) (congrArg Subtype.val (Sum.inr.inj e))))
  have hcard := Nat.card_le_card_of_injective ψ hψ
  rw [H.card, Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_coe, ← cntW_eq] at hcard
  omega

theorem false_of_badOK {rep : List ℕ} (hrep : rep ∈ dReps) (hbad : badOK rep = true)
    {L : Subgroup GL} (H : Hyp (vecOf a0) (spanOf rep) L) : False := by
  have hlt := dReps_lt rep hrep
  have hT : ∀ l ∈ L, ∃ r ∈ tdList rep, (∀ x ∈ r, x < 4096) ∧ ∀ x, l x = linOfRows r x :=
    fun l hl => mem_tdList hlt (H.le hl) (H.fix l hl) (H.perp l hl) (H.comm l hl)
  classical
  set R := (tdList rep).map fun r => rep.map (appN r) with hR
  let ρ : L → R.toFinset := fun l =>
    ⟨rep.map fun d => codeOf ((l : GL) (vecOf d)), by
      obtain ⟨r, hr, hrlt, hl⟩ := hT l l.2
      rw [List.mem_toFinset, hR, List.mem_map]
      refine ⟨r, hr, List.map_congr_left fun d _ => ?_⟩
      rw [hl, ← vecOf_appN, codeOf_vecOf (appN_lt hrlt d)]⟩
  have hinj : Function.Injective ρ := by
    intro l l' h
    have hcodes := congrArg Subtype.val h
    simp only [ρ] at hcodes
    have h' : ∀ d ∈ rep, (l : GL) (vecOf d) = (l' : GL) (vecOf d) := fun d hd => by
      have := List.map_inj_left.1 hcodes d hd
      rw [← vecOf_codeOf ((l : GL) (vecOf d)), this, vecOf_codeOf]
    have hfix : ∀ y ∈ spanOf rep, ((l : GL)⁻¹ * (l' : GL)) y = y := by
      intro y hy
      have := eqOn_spanOf (f := ((l' : GL) : V12 →ₗ[ZMod 2] V12))
        (g := ((l : GL) : V12 →ₗ[ZMod 2] V12)) (fun d hd => (h' d hd).symm) y hy
      simp only [LinearEquiv.coe_coe] at this
      rw [LinearEquiv.mul_apply, this, inv_apply_apply]
    have h1 := H.faithful _ (mul_mem (inv_mem l.2) l'.2) hfix
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  have hcard := Nat.card_le_card_of_injective ρ hinj
  rw [H.card, Nat.card_eq_fintype_card, Fintype.card_coe, List.card_toFinset] at hcard
  have hbad' : R.dedup.length < 32 := by
    rw [hR]
    simpa only [badOK, decide_eq_true_eq] using hbad
  omega

theorem t1_spec (ht : thetaOK = true) (h0 : t1OK (nthD [] dReps 0) W0 = true)
    (h2 : t1OK (nthD [] dReps 2) W2 = true) (h3 : badOK (nthD [] dReps 3) = true)
    (h4 : t1OK (nthD [] dReps 4) W4 = true) (h5 : t1OK (nthD [] dReps 5) W5 = true) :
    ∀ rep ∈ dReps, rep ≠ d0 → ∀ L : Subgroup GL, ¬ Hyp (vecOf a0) (spanOf rep) L := by
  intro rep hrep hne L H
  have hrep' := hrep
  simp only [dReps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hrep'
  rcases hrep' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact t1_false ht (R5 := [960, 48, 9, 5, 3]) rfl (by decide) h0 H
  · exact hne rfl
  · exact t1_false ht (R5 := [1072, 960, 9, 5, 3]) rfl (by decide) h2 H
  · exact false_of_badOK hrep h3 H
  · exact t1_false ht (R5 := [768, 192, 48, 12, 3]) rfl (by decide) h4 H
  · exact t1_false ht (R5 := [1072, 768, 192, 12, 3]) rfl (by decide) h5 H

theorem foldl_rows {G : List (Array ℕ)} (hG : ∀ g ∈ G, ∀ x ∈ g, x < 4096) :
    ∀ acc : List (Array ℕ), (∀ r ∈ acc, r.size = 12 ∧ ∀ x ∈ r, x < 4096) →
      ∀ r ∈ G.foldl (fun acc g => acc ++ acc.map (mulR g)) acc,
        r.size = 12 ∧ ∀ x ∈ r, x < 4096 := by
  induction G with
  | nil => exact fun acc h => h
  | cons g G ih =>
    intro acc hacc
    rw [List.foldl_cons]
    refine ih (fun g' hg' => hG g' (List.mem_cons_of_mem g hg')) _ fun r hr => ?_
    rcases List.mem_append.1 hr with hr | hr
    · exact hacc r hr
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      refine ⟨by rw [mulR, Array.size_map]; exact (hacc r' hr').1, fun x hx => ?_⟩
      rw [mulR] at hx
      obtain ⟨y, -, rfl⟩ := Array.mem_map.1 hx
      exact appN_lt (hG g List.mem_cons_self) y

theorem pinOK_spec (h : pinOK = true) :
    K0P = CFSG.KC.IF4R.packR k0 ∧ CBP = cBasis.map CFSG.KC.IF4R.packR ∧
      THP = CFSG.KC.IF4R.packR SigmaP.thetaRows ∧ GUS.rowsOK k0.toList = true ∧
      (∀ r ∈ cBasis, GUS.rowsOK r.toList = true) ∧ GUS.rowsOK SigmaP.thetaRows.toList = true := by
  unfold pinOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, beq_iff_eq.1 h2, Nat.eq_of_beq_eq_true h3, h4,
    List.all_eq_true.1 h5, h6⟩

theorem cBasis_mem {i : ℕ} (hi : i < 5) : cBasis[i]! ∈ cBasis := by
  rw [getElem!_pos cBasis i (by simp [cBasis]; omega)]
  exact List.getElem_mem _

theorem t3_spec (hpin : pinOK = true) :
    ∀ c < 32, ∀ r ∈ compOf c, r.size = 12 ∧ ∀ x ∈ r, x < 4096 := by
  obtain ⟨-, -, -, hk0r, hcbr, -⟩ := pinOK_spec hpin
  intro c _ r hr
  unfold compOf subsetProducts at hr
  have hid : ∀ r ∈ [idR], r.size = 12 ∧ ∀ x ∈ r, x < 4096 := by
    intro r hr
    obtain rfl := List.mem_singleton.1 hr
    refine ⟨rfl, fun x hx => ?_⟩
    simp only [idR, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  refine foldl_rows ?_ [idR] hid r hr
  intro g hg x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  rw [List.mem_range] at hi
  split_ifs at hx
  · rw [mulR] at hx
    obtain ⟨y, -, rfl⟩ := Array.mem_map.1 hx
    exact appN_lt (GUS.rows_lt hk0r) y
  · exact GUS.rows_lt (hcbr _ (cBasis_mem hi)) x hx

theorem fix_span {g : GL} {s : List ℕ} (h : ∀ d ∈ s, g (vecOf d) = vecOf d) :
    ∀ y ∈ spanOf s, g y = y := fun y hy =>
  eqOn_spanOf (f := (g : V12 →ₗ[ZMod 2] V12)) (g := LinearMap.id) h y hy

theorem land_shr_one (n k : ℕ) : Nat.land (Nat.shiftRight n k) 1 = if n.testBit k then 1 else 0 := by
  change (n >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]

theorem f0_add_right (x y z : V12) : f0 x (y + z) = f0 x y + f0 x z := by
  simp only [f0, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem notPerp_false {n : ℕ} (hx : f0 (vecOf n) (vecOf a0) = 0) : notPerp n = false := by
  have h10 : vecOf (2 ^ 10) = Pi.single (hi 4) 1 := vecOf_two_pow (hi 4)
  have h11 : vecOf (2 ^ 11) = Pi.single (hi 5) 1 := vecOf_two_pow (hi 5)
  have ha : vecOf a0 = vecOf (2 ^ 10) + vecOf (2 ^ 11) := by rw [← vecOf_xor]; rfl
  rw [ha, h10, h11, f0_add_right, f0_unit_hi, f0_unit_hi] at hx
  change (if n.testBit 4 then (1 : ZMod 2) else 0) + (if n.testBit 5 then 1 else 0) = 0 at hx
  have he : n.testBit 4 = n.testBit 5 := by
    revert hx
    generalize n.testBit 4 = b4
    generalize n.testBit 5 = b5
    cases b4 <;> cases b5 <;> decide
  unfold notPerp
  rw [land_shr_one, land_shr_one, he]
  simp

theorem perp_of (hspan : spanOK = true) (hperp : perpOK = true) {P : ℕ} {G : GL} (hP : IsP G P)
    (h : perpD perpB P = true) : ∀ x, f0 x (vecOf a0) = 0 → G x - x ∈ spanOf d0 := by
  have hSD : SD0 = spanList d0 := beq_iff_eq.1 hspan
  let f : V12 →ₗ[ZMod 2] V12 := (G : V12 →ₗ[ZMod 2] V12) - LinearMap.id
  have hB : ∀ b ∈ perpB, f (vecOf b) ∈ spanOf d0 := by
    intro b hb
    have hb' := (recAll_iff (fun b => memN (ap12 P b ^^^ b) SD0) perpB).1 h b hb
    rw [memN_iff, hSD] at hb'
    have hblt : b < 4096 := (by decide : ∀ b ∈ perpB, b < 4096) b hb
    have := (mem_spanList_iff d0_lt (n := ap12 P b ^^^ b) (xor_lt (ap12_lt _ _) hblt)).1 hb'
    rw [vecOf_xor, ← hP.apply_code, ← vec_sub_eq_add] at this
    simpa [f] using this
  intro x hx
  rw [← vecOf_codeOf x] at hx ⊢
  unfold perpOK perpAt at hperp
  have hsel := (allBelow_iff _ _).1 hperp (codeOf x) (codeOf_lt x)
  rw [notPerp_false hx, Bool.false_or, Nat.beq_eq] at hsel
  rw [← hsel]
  simpa [f] using selX_mem (f := f) (S := spanOf d0) hB (pmask (codeOf x))

theorem guOK_of (hTH : ∀ v, linP THP v = theta0 v) {P : ℕ} {G : GL} (hP : IsP G P)
    (hg : G ∈ gammaU) (hu : ∀ x, G (theta0 x) = theta0 (G x)) :
    guOK THP P = true ∧ unitP THP P = true := by
  have hq := (mem_gammaU.1 hg).1
  have hv : ∀ j (hj : j < 12), G (vecOf (2 ^ j)) = vecOf (fld P j) := fun j hj => by
    have e1 : vecOf (2 ^ j) = Pi.single (⟨j, hj⟩ : Fin 12) 1 := vecOf_two_pow ⟨j, hj⟩
    have e2 : linP P (Pi.single (⟨j, hj⟩ : Fin 12) 1) = vecOf (fld P j) := GUS.linP_single P ⟨j, hj⟩
    rw [hP, e1, e2]
  have hu' : unitP THP P = true := by
    unfold unitP
    rw [Nat.beq_eq]
    exact GUS.mulP_eq_of_linP fun v => by rw [linP_mulP, linP_mulP, hTH, hTH, ← hP, ← hP, hu]
  refine ⟨?_, hu'⟩
  simp only [guOK, Bool.and_eq_true, Bool.or_eq_true, allBelow_iff, beq_iff_eq]
  refine ⟨⟨fun j hj => ite_inj ?_, fun j hj k hk => ite_inj ?_⟩, Or.inl hu'⟩
  · rw [← q0_vecOf, ← q0_vecOf, ← hv j hj, hq]
  · rw [← f0_vecOf, ← f0_vecOf, ← hv j hj, ← hv k hk, f0_isometry hq]

theorem inT_spec (hTH : ∀ v, linP THP v = theta0 v) (hspan : spanOK = true) (hperp : perpOK = true)
    {P : ℕ} {G : GL} (hP : IsP G P) (h : inT THP P = true) :
    G ∈ gammaU ∧ G (vecOf a0) = vecOf a0 ∧
      (∀ d ∈ d0, G (vecOf d) = vecOf d ∨ G (vecOf d) = vecOf d + vecOf a0) ∧
      ∀ x, f0 x (vecOf a0) = 0 → G x - x ∈ spanOf d0 := by
  unfold inT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hgu, ha⟩, hc⟩, hp⟩ := h
  refine ⟨guOK_spec hTH hgu hP, ?_, fun d hd => ?_, perp_of hspan hperp hP hp⟩
  · have e := Nat.eq_of_beq_eq_true ha
    change G (vecOf 3072) = vecOf 3072
    rw [hP.apply_code, e]
  · have hd' := (recAll_iff (fun d => Nat.beq (ap12 P d ^^^ d) 0 || Nat.beq (ap12 P d ^^^ d) 3072)
      d0).1 hc d hd
    simp only [Bool.or_eq_true, Nat.beq_eq] at hd'
    have hv : vecOf (ap12 P d ^^^ d) = G (vecOf d) + vecOf d := by rw [vecOf_xor, hP.apply_code]
    rcases hd' with h0 | h1
    · left
      have h00 : vecOf 0 = 0 := (vecOf_eq_zero (by norm_num)).2 rfl
      rw [h0, h00] at hv
      exact (vec_add_eq_iff.1 hv.symm).trans (add_zero _)
    · exact Or.inr ((xor_a0_iff hP (d0_lt d hd)).1 h1)

theorem kerT_of (hTH : ∀ v, linP THP v = theta0 v) (hspan : spanOK = true) {P : ℕ} {G : GL}
    (hP : IsP G P) (hg : G ∈ gammaU) (hu : ∀ x, G (theta0 x) = theta0 (G x))
    (hfix : ∀ d ∈ d0, G (vecOf d) = vecOf d)
    (hperp : ∀ b ∈ perpB, G (vecOf b) - vecOf b ∈ spanOf d0) : kerT THP P = true := by
  obtain ⟨h1, h2⟩ := guOK_of hTH hP hg hu
  have hSD : SD0 = spanList d0 := beq_iff_eq.1 hspan
  simp only [kerT, Bool.and_eq_true]
  refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
  · refine (recAll_iff (fun d => Nat.beq (ap12 P d) d) d0).2 fun d hd => ?_
    rw [Nat.beq_eq]
    exact vecOf_inj (ap12_lt _ _) (d0_lt d hd) (by rw [← hP.apply_code, hfix d hd])
  · refine (recAll_iff (fun b => memN (ap12 P b ^^^ b) SD0) perpB).2 fun b hb => ?_
    have hblt : b < 4096 := (by decide : ∀ b ∈ perpB, b < 4096) b hb
    rw [memN_iff, hSD, mem_spanList_iff d0_lt (xor_lt (ap12_lt _ _) hblt), vecOf_xor,
      ← hP.apply_code, ← vec_sub_eq_add]
    exact hperp b hb

theorem rowsBP_isP (hcoef : coefOK = true) {imgs : List ℕ} (himgs : ∀ x ∈ imgs, x < 4096) {G : GL}
    (hG : List.Forall₂ (fun b c => G (vecOf b) = vecOf c) (B10 ++ [XB, theta0N XB]) imgs) :
    IsP G (rowsBP imgs) := by
  unfold coefOK at hcoef
  simp only [Bool.and_eq_true, allBelow_iff] at hcoef
  have hc := hcoef.2
  have hpack : rowsBP imgs = CFSG.KC.IF4R.packL (coefB.map (selX imgs)) := rfl
  have hlt : ∀ x ∈ coefB.map (selX imgs), x < 4096 := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact selX_lt imgs himgs c
  have hf : (G : V12 →ₗ[ZMod 2] V12) = linP (rowsBP imgs) := linMap_ext fun j => by
    have hj := Nat.eq_of_beq_eq_true (hc j j.2)
    have hlen : (j : ℕ) < coefB.length := lt_of_lt_of_eq j.2 rfl
    calc (G : V12 →ₗ[ZMod 2] V12) (vecOf (2 ^ (j : ℕ)))
        = (G : V12 →ₗ[ZMod 2] V12) (vecOf (selX (B10 ++ [XB, theta0N XB]) (nthD 0 coefB j))) := by
          rw [hj]
          rfl
      _ = vecOf (selX imgs (nthD 0 coefB j)) := selX_apply (f := (G : V12 →ₗ[ZMod 2] V12)) hG _
      _ = linP (rowsBP imgs) (vecOf (2 ^ (j : ℕ))) := by
          rw [vecOf_two_pow j, GUS.linP_single, hpack, GUS.fld_packL _ hlt, ← nthD_eq,
            GUS.nthD_map (selX imgs) 0 coefB 0 hlen, nthD_eq]
  exact fun v => LinearMap.congr_fun hf v

theorem forall₂_fix {g : GL} : ∀ (B : List ℕ), (∀ b ∈ B, g (vecOf b) = vecOf b) →
    ∀ {T T' : List ℕ}, List.Forall₂ (fun b c => g (vecOf b) = vecOf c) T T' →
      List.Forall₂ (fun b c => g (vecOf b) = vecOf c) (B ++ T) (B ++ T')
  | [], _, _, _, h => h
  | b :: B, hB, _, _, h =>
    .cons (hB b List.mem_cons_self) (forall₂_fix B (fun x hx => hB x (List.mem_cons_of_mem b hx)) h)

theorem ker_spec (hTH : ∀ v, linP THP v = theta0 v) (ht : thetaOK = true) (hb10 : b10OK = true)
    (hcoef : coefOK = true) (hspan : spanOK = true) (hker : kerOK THP K0P = true) {K : GL}
    (hK : IsP K K0P) {g : GL} (hg : g ∈ gammaU) (hfix : ∀ y ∈ spanOf d0, g y = y)
    (hperp : ∀ x, f0 x (vecOf a0) = 0 → g x - x ∈ spanOf d0) : g = 1 ∨ g = K := by
  obtain ⟨-, t2, t3, t4⟩ := thetaOK_spec ht
  have hSD : SD0 = spanList d0 := beq_iff_eq.1 hspan
  have hfix' : ∀ d ∈ d0, g (vecOf d) = vecOf d := fun d hd => hfix _ (mem_spanOf_of_mem hd)
  rcases (mem_gammaU.1 hg).2 with hu | ha
  swap
  ·
    exfalso
    have e := ha (vecOf 48)
    rw [← vecOf_theta0N (by norm_num : 48 < 4096), t4, hfix' 48 t3, hfix' 3072 (by decide),
      ← vecOf_theta0N (by norm_num : 48 < 4096), t4,
      ← vecOf_theta0N (by norm_num : 3072 < 4096)] at e
    exact t2 (vecOf_inj (theta0N_lt (by norm_num)) (by norm_num) e.symm)
  have hB : ∀ b ∈ B10, g (vecOf b) = vecOf b := by
    intro b hb
    have h := (recAll_iff (fun b => memN b d0 || memN b (d0.map theta0N)) B10).1 hb10 b hb
    simp only [Bool.or_eq_true, memN_iff] at h
    rcases h with h | h
    · exact hfix' b h
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
      rw [vecOf_theta0N (d0_lt d hd), hu, hfix' d hd]
  have hXB : f0 (vecOf XB) (vecOf a0) = 0 := by
    have : f0b XB a0 = false := by decide
    simp [f0_vecOf, this]
  obtain ⟨dn, hdn_lt, hdn_v⟩ : ∃ dn, dn < 4096 ∧ vecOf dn = g (vecOf XB) - vecOf XB :=
    ⟨_, codeOf_lt _, vecOf_codeOf _⟩
  have hdn : dn ∈ SD0 := by
    rw [hSD, mem_spanList_iff d0_lt hdn_lt, hdn_v]
    exact hperp _ hXB
  have hgx : g (vecOf XB) = vecOf (XB ^^^ dn) := by
    rw [vecOf_xor, hdn_v]
    abel
  have hy : XB ^^^ dn < 4096 := xor_lt (by decide) hdn_lt
  have hgθ : g (vecOf (theta0N XB)) = vecOf (theta0N (XB ^^^ dn)) := by
    rw [vecOf_theta0N (by decide), hu, hgx, vecOf_theta0N hy]
  have hF := forall₂_fix B10 hB (List.Forall₂.cons hgx (List.Forall₂.cons hgθ List.Forall₂.nil))
  have hlt : ∀ x ∈ B10 ++ [XB ^^^ dn, theta0N (XB ^^^ dn)], x < 4096 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact (by decide : ∀ b ∈ B10, b < 4096) x h
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      exacts [hy, theta0N_lt hy]
  have hP : IsP g (candB (XB ^^^ dn)) := rowsBP_isP hcoef hlt hF
  have hperpB : ∀ b ∈ perpB, g (vecOf b) - vecOf b ∈ spanOf d0 := fun b hb => by
    have hf := (by decide : ∀ b ∈ perpB, f0b b a0 = false) b hb
    exact hperp _ (by simp [f0_vecOf, hf])
  have hkT := kerT_of hTH hspan hP hg hu hfix' hperpB
  have hk := (recAll_iff (fun d => kerAt THP K0P (candB (XB ^^^ d))) SD0).1 hker dn hdn
  simp only [kerAt, hkT, cond_true, Bool.or_eq_true, Nat.beq_eq] at hk
  rcases hk with h | h
  · left
    rw [h] at hP
    exact IsP.inj hP IsP.one
  · right
    rw [h] at hP
    exact IsP.inj hP hK

theorem gen_spec (hTH : ∀ v, linP THP v = theta0 v) (ht : thetaOK = true) (hb10 : b10OK = true)
    (hcoef : coefOK = true) (hspan : spanOK = true) (hperp : perpOK = true)
    (hker : kerOK THP K0P = true) {K : GL} (hK : IsP K K0P) (hKK : K * K = 1) {L : Subgroup GL}
    (H : Hyp (vecOf a0) (spanOf d0) L) {C : GL} {P : ℕ} (hC : IsP C P) (hCT : inT THP P = true)
    (hKC : K * C = C * K) {l : GL} (hl : l ∈ L)
    (hm : lamM [961, 48, 9, 5, 3] l = lamM [961, 48, 9, 5, 3] C) : l = C ∨ l = K * C := by
  obtain ⟨hCU, hCa, hCc, hCp⟩ := inT_spec hTH hspan hperp hC hCT
  have hcl : ∀ b ∈ [961, 48, 9, 5, 3],
      l (vecOf b) = vecOf b ∨ l (vecOf b) = vecOf b + vecOf a0 := fun b hb =>
    comm_or (H.comm _ hl _ (mem_spanOf_of_mem (vs := d0) (List.mem_append_left [a0] hb)))
  have hcC : ∀ b ∈ [961, 48, 9, 5, 3],
      C (vecOf b) = vecOf b ∨ C (vecOf b) = vecOf b + vecOf a0 := fun b hb =>
    hCc b (List.mem_append_left [a0] hb)
  have hlinv : l⁻¹ (vecOf a0) = vecOf a0 := by
    calc l⁻¹ (vecOf a0) = l⁻¹ (l (vecOf a0)) := by rw [H.fix l hl]
      _ = vecOf a0 := inv_apply_apply l _
  have hfix : ∀ d ∈ d0, (l⁻¹ * C) (vecOf d) = vecOf d := by
    intro d hd
    rw [LinearEquiv.mul_apply]
    change d ∈ [961, 48, 9, 5, 3] ++ [a0] at hd
    rcases List.mem_append.1 hd with hd | hd
    · rw [← lamM_inj hcl hcC hm d hd, inv_apply_apply]
    · rw [List.mem_singleton.1 hd, hCa, hlinv]
  have hp : ∀ x, f0 x (vecOf a0) = 0 → (l⁻¹ * C) x - x ∈ spanOf d0 := by
    intro x hx
    have he := hCp x hx
    have h1 := H.perp _ (inv_mem hl) x hx
    have h2 : l⁻¹ (C x - x) ∈ spanOf d0 := by
      rcases H.comm _ (inv_mem hl) _ he with h | h
      · rw [sub_eq_zero.1 h]
        exact he
      · have e : l⁻¹ (C x - x) = (C x - x) + vecOf a0 := by
          rw [← h]
          abel
        rw [e]
        exact add_mem he H.mem
    have e : (l⁻¹ * C) x - x = l⁻¹ (C x - x) + (l⁻¹ x - x) := by
      rw [map_sub, LinearEquiv.mul_apply]
      abel
    rw [e]
    exact add_mem h2 h1
  rcases ker_spec hTH ht hb10 hcoef hspan hker hK (mul_mem (inv_mem (H.le hl)) hCU) (fix_span hfix)
    hp with h | h
  · exact Or.inl (inv_mul_eq_one.1 h)
  · right
    have hC' : C = l * K := inv_mul_eq_iff_eq_mul.1 h
    rw [hKC, hC', mul_assoc, hKK, mul_one]

theorem subset_mask {B : List ℕ} {L : Subgroup GL} (H : Hyp (vecOf a0) (spanOf (B ++ [a0])) L) :
    ∀ (gs : List (Array ℕ)) (ms : List ℕ),
      List.Forall₂ (fun g ρ => ∃ l ∈ L, (∀ x, l x = linOfRows g x) ∧ lamM B l = ρ) gs ms →
      ∀ (acc : List (Array ℕ)) (P : ℕ → Prop),
        (∀ m, P m → ∃ r ∈ acc, ∃ l ∈ L, (∀ x, l x = linOfRows r x) ∧ lamM B l = m) →
        ∀ m, P m → ∀ S, ∃ r ∈ gs.foldl (fun acc g => acc ++ acc.map (mulR g)) acc,
          ∃ l ∈ L, (∀ x, l x = linOfRows r x) ∧ lamM B l = m ^^^ selX ms S := by
  have hc : ∀ {u : GL}, u ∈ L → ∀ b ∈ B,
      u (vecOf b) = vecOf b ∨ u (vecOf b) = vecOf b + vecOf a0 := fun hu b hb =>
    comm_or (H.comm _ hu _ (mem_spanOf_of_mem (List.mem_append_left _ hb)))
  intro gs ms hF
  induction hF with
  | nil =>
    intro acc P hP m hm S
    obtain ⟨r, hr, l, hl, hlx, hlm⟩ := hP m hm
    exact ⟨r, hr, l, hl, hlx, hlm.trans (Nat.xor_zero m).symm⟩
  | @cons g ρ gs ms hg _ ih =>
    intro acc P hP m hm S
    obtain ⟨lg, hlg, hlgx, hlgm⟩ := hg
    have hP' : ∀ m', (∃ m₀, P m₀ ∧ (m' = m₀ ∨ m' = ρ ^^^ m₀)) →
        ∃ r ∈ acc ++ acc.map (mulR g), ∃ l ∈ L, (∀ x, l x = linOfRows r x) ∧ lamM B l = m' := by
      rintro m' ⟨m₀, hm₀, he | he⟩
      · obtain ⟨r, hr, l, hl, hlx, hlm⟩ := hP m₀ hm₀
        exact ⟨r, List.mem_append_left _ hr, l, hl, hlx, hlm.trans he.symm⟩
      · obtain ⟨r, hr, l, hl, hlx, hlm⟩ := hP m₀ hm₀
        refine ⟨mulR g r, List.mem_append_right _ (List.mem_map_of_mem hr), lg * l, mul_mem hlg hl,
          fun x => by rw [LinearEquiv.mul_apply, hlx, hlgx, linOfRows_mulR], ?_⟩
        rw [lamM_mul (H.fix lg hlg) (hc hlg) (hc hl), hlgm, hlm, he]
    have hm' : ∃ m₀, P m₀ ∧ (m ^^^ S % 2 * ρ = m₀ ∨ m ^^^ S % 2 * ρ = ρ ^^^ m₀) := by
      refine ⟨m, hm, ?_⟩
      rcases Nat.mod_two_eq_zero_or_one S with h | h
      · left
        rw [h, zero_mul, Nat.xor_zero]
      · right
        rw [h, one_mul, Nat.xor_comm]
    have := ih (acc ++ acc.map (mulR g)) _ hP' _ hm' (S / 2)
    rw [List.foldl_cons, selX_cons, ← Nat.xor_assoc]
    exact this

theorem t2_spec (hpin : pinOK = true) (ht : thetaOK = true) (hb10 : b10OK = true)
    (hcoef : coefOK = true) (hspan : spanOK = true) (hperp : perpOK = true)
    (hker : kerOK THP K0P = true) (hgen : genTOK THP = true) (hcomm : commOK = true)
    (hrho : rhoOK = true) :
    ∀ L : Subgroup GL, Hyp (vecOf a0) (spanOf d0) L →
      ∃ c < 32, ∀ l : GL, l ∈ L ↔ ∃ r ∈ compOf c, ∀ x, l x = linOfRows r x := by
  intro L H
  classical
  obtain ⟨hK0eq, -, hTHeq, hk0r, hcbr, hthr⟩ := pinOK_spec hpin
  have hTH : ∀ v, linP THP v = theta0 v := fun v => by
    rw [hTHeq, linP_eq_of_rowsP (GUS.rowsP_packR hthr), GUS.linOfRows_thetaRows]
  unfold genTOK at hgen
  simp only [Bool.and_eq_true] at hgen
  have hCBT := (recAll_iff (fun g => inT THP g) CBP).1 hgen.2
  have hca : ∀ g ∈ K0P :: CBP, mulP g g = idP ∧ ∀ h ∈ K0P :: CBP, mulP g h = mulP h g := by
    intro g hg
    have hg' := (recAll_iff (fun g => commAt (K0P :: CBP) g) (K0P :: CBP)).1 hcomm g hg
    unfold commAt at hg'
    rw [Bool.and_eq_true, Nat.beq_eq] at hg'
    refine ⟨hg'.1, fun h hh => ?_⟩
    exact Nat.eq_of_beq_eq_true
      ((recAll_iff (fun h => Nat.beq (mulP g h) (mulP h g)) _).1 hg'.2 h hh)
  unfold rhoOK at hrho
  simp only [Bool.and_eq_true, allBelow_iff] at hrho
  have hrhoi := hrho.1.2
  obtain ⟨K, hK⟩ := IsP.exists_of_mul (hca K0P List.mem_cons_self).1
  have hKK : K * K = 1 := by
    have h2 := hK.mul hK
    rw [(hca K0P List.mem_cons_self).1] at h2
    exact IsP.inj h2 IsP.one
  have hKrows : ∀ v, K v = linOfRows k0 v := (GUS.isP_packR hk0r K).1 (hK0eq ▸ hK)
  have hCBi : ∀ i < 5, nthD 0 CBP i = CFSG.KC.IF4R.packR cBasis[i]! := by decide +kernel
  have hRHO : ∀ i < 5, nthD 0 RHO i < 32 := by decide +kernel
  have hsel : ∀ m < 32, ∃ S < 32, selX RHO S = m := by decide +kernel
  have hsurj : ∀ m < 32, ∃ l ∈ L, lamM [961, 48, 9, 5, 3] l = m := by
    let ψ : L → Fin 32 := fun l => ⟨lamM [961, 48, 9, 5, 3] l, lt_of_lt_of_eq (lamM_lt _ _) (by decide)⟩
    have hψ : Function.Injective ψ := fun l l' h =>
      Subtype.ext (lamM_injL (R5 := [961, 48, 9, 5, 3]) H l.2 l'.2 (congrArg Fin.val h))
    have hb := hψ.bijective_of_nat_card_le (by simp [H.card])
    intro m hm
    obtain ⟨l, hl⟩ := hb.2 ⟨m, hm⟩
    exact ⟨l, l.2, congrArg Fin.val hl⟩
  have hgen1 : ∀ i < 5,
      (∃ l ∈ L, (∀ x, l x = linOfRows cBasis[i]! x) ∧ lamM [961, 48, 9, 5, 3] l = nthD 0 RHO i) ∨
      ∃ l ∈ L, (∀ x, l x = linOfRows (mulR k0 cBasis[i]!) x) ∧
        lamM [961, 48, 9, 5, 3] l = nthD 0 RHO i := by
    intro i hi
    have hmem : nthD 0 CBP i ∈ CBP := GUS.nthD_mem 0 (lt_of_lt_of_eq hi rfl)
    obtain ⟨C, hC⟩ := IsP.exists_of_mul (hca _ (List.mem_cons_of_mem _ hmem)).1
    have hCr : ∀ v, C v = linOfRows cBasis[i]! v := by
      refine (GUS.isP_packR (hcbr _ (cBasis_mem hi)) C).1 ?_
      rw [← hCBi i hi]
      exact hC
    have hCm : lamM [961, 48, 9, 5, 3] C = nthD 0 RHO i := by
      rw [← rhoL_eq hC _ (by decide)]
      exact Nat.eq_of_beq_eq_true (hrhoi i hi)
    have hKC : K * C = C * K := by
      have e := (hca K0P List.mem_cons_self).2 _ (List.mem_cons_of_mem _ hmem)
      have h1 := hK.mul hC
      rw [e] at h1
      exact IsP.inj h1 (hC.mul hK)
    obtain ⟨l, hl, hlm⟩ := hsurj _ (hRHO i hi)
    rcases gen_spec hTH ht hb10 hcoef hspan hperp hker hK hKK H hC (hCBT _ hmem) hKC hl
      (hlm.trans hCm.symm) with h | h
    · exact Or.inl ⟨l, hl, fun x => by rw [h, hCr], hlm⟩
    · exact Or.inr ⟨l, hl, fun x => by rw [h, LinearEquiv.mul_apply, hCr, hKrows, linOfRows_mulR],
        hlm⟩
  obtain ⟨c, hc32, hcbits⟩ := bits_five fun i =>
    !decide (∃ l ∈ L, (∀ x, l x = linOfRows cBasis[(i : ℕ)]! x) ∧
      lamM [961, 48, 9, 5, 3] l = nthD 0 RHO i)
  have hgens : ∀ i < 5, ∃ l ∈ L,
      (∀ x, l x = linOfRows (if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]!) x) ∧
        lamM [961, 48, 9, 5, 3] l = nthD 0 RHO i := by
    intro i hi
    have hb := hcbits ⟨i, hi⟩
    simp only at hb
    by_cases hP : ∃ l ∈ L, (∀ x, l x = linOfRows cBasis[i]! x) ∧
        lamM [961, 48, 9, 5, 3] l = nthD 0 RHO i
    · rw [if_neg (by rw [hb, decide_eq_true hP]; decide)]
      exact hP
    · rw [if_pos (by rw [hb, decide_eq_false hP]; rfl)]
      exact (hgen1 i hi).resolve_left hP
  have hF : List.Forall₂ (fun g ρ => ∃ l ∈ L, (∀ x, l x = linOfRows g x) ∧
      lamM [961, 48, 9, 5, 3] l = ρ)
      ((List.range 5).map fun i => if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]!) RHO :=
    .cons (hgens 0 (by norm_num)) (.cons (hgens 1 (by norm_num)) (.cons (hgens 2 (by norm_num))
      (.cons (hgens 3 (by norm_num)) (.cons (hgens 4 (by norm_num)) .nil))))
  have hcov := subset_mask (B := [961, 48, 9, 5, 3]) H _ _ hF [idR] (fun m => m = 0)
    (fun m hm => ⟨idR, List.mem_singleton_self _, 1, one_mem _,
      fun x => by rw [linOfRows_idR]; rfl, by rw [hm, lamM_one]⟩) 0 rfl
  refine ⟨c, hc32, fun l => ⟨fun hl => ?_, fun ⟨r, hr, hrx⟩ => ?_⟩⟩
  · have hm : lamM [961, 48, 9, 5, 3] l < 32 := lt_of_lt_of_eq (lamM_lt l _) (by decide)
    obtain ⟨S, -, hS⟩ := hsel _ hm
    obtain ⟨r, hr, l', hl', hl'x, hl'm⟩ := hcov S
    have e : l = l' :=
      lamM_injL (R5 := [961, 48, 9, 5, 3]) H hl hl' (by rw [hl'm, Nat.zero_xor, hS])
    exact ⟨r, hr, fun x => by rw [e, hl'x]⟩
  · have hr' : r ∈ subsetProducts ((List.range 5).map fun i =>
        if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]!) := hr
    obtain ⟨l', hl', hl'x⟩ := subsetProducts_mem (fun g hg => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      obtain ⟨l, hl, hlx, -⟩ := hgens i (List.mem_range.1 hi)
      exact ⟨l, hl, hlx⟩) r hr'
    have e : l = l' := LinearEquiv.ext fun x => by rw [hrx, hl'x]
    rw [e]
    exact hl'

end CFSG.KC.GUA

end
