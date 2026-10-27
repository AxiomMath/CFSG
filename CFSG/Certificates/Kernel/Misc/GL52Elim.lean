module

public import CFSG.Certificates.Kernel.Misc.GL52Ech
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.KC.Misc.GLM.Ech

open CFSG.KC.Misc.GLM Module

def Desc : List ℕ → ℕ → Prop
  | [], _ => True
  | x :: K, b => ∃ i < b, x.testBit i = true ∧ Low i x ∧ Desc K i

theorem desc_mono : ∀ {K : List ℕ} {b b' : ℕ}, b ≤ b' → Desc K b → Desc K b'
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, hb, ⟨i, hi, h1, h2, h3⟩ => ⟨i, by omega, h1, h2, h3⟩

theorem desc_low : ∀ {K : List ℕ} {b : ℕ}, Desc K b → ∀ x ∈ K, ∀ v, b ≤ v → x.testBit v = false
  | [], _, _, x, hx => by simp at hx
  | y :: K, b, ⟨i, hi, _, hl, hK⟩, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact fun v hv => hl v (by omega)
    · exact fun v hv => desc_low hK x hx v (by omega)

noncomputable def xs : List ℕ → (ℕ → Bool) → ℕ
  | [], _ => 0
  | x :: K, g => Nat.xor (if g 0 then x else 0) (xs K fun i => g (i + 1))

theorem xs_testBit_high : ∀ (K : List ℕ) (g : ℕ → Bool) (v : ℕ),
    (∀ x ∈ K, x.testBit v = false) → (xs K g).testBit v = false
  | [], _, v, _ => Nat.zero_testBit v
  | x :: K, g, v, h => by
    change (Nat.xor (if g 0 then x else 0) (xs K fun i => g (i + 1))).testBit v = false
    rw [xor_testBit, xs_testBit_high K _ v fun y hy => h y (List.mem_cons_of_mem _ hy)]
    split_ifs
    · rw [h x (List.mem_cons_self ..)]
      rfl
    · rw [Nat.zero_testBit]
      rfl

theorem xs_inj : ∀ (K : List ℕ) (b : ℕ), Desc K b → ∀ g g' : ℕ → Bool, xs K g = xs K g' →
    ∀ i < K.length, g i = g' i
  | [], _, _, _, _, _, i, hi => by simp at hi
  | x :: K, b, ⟨t, _, hxt, _, hK⟩, g, g', e, i, hi => by
    change Nat.xor (if g 0 then x else 0) (xs K fun i => g (i + 1)) =
      Nat.xor (if g' 0 then x else 0) (xs K fun i => g' (i + 1)) at e
    have hK0 : ∀ g'' : ℕ → Bool, (xs K g'').testBit t = false := fun g'' =>
      xs_testBit_high K g'' t fun y hy => desc_low hK y hy t le_rfl
    have h0 : g 0 = g' 0 := by
      have e1 := congrArg (fun z => Nat.testBit z t) e
      simp only [xor_testBit, hK0, Bool.xor_false] at e1
      cases hg : g 0 <;> cases hg' : g' 0 <;> simp_all
    rcases i with _ | i
    · exact h0
    · rw [h0] at e
      have e2 : (xs K fun i => g (i + 1)) = xs K fun i => g' (i + 1) := by
        have e3 := congrArg (fun z => Nat.xor (if g' 0 then x else 0) z) e
        have cancel : ∀ a b : ℕ, Nat.xor a (Nat.xor a b) = b := fun a b => by
          change a ^^^ (a ^^^ b) = b
          rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        simp only [cancel] at e3
        exact e3
      exact xs_inj K t hK _ _ e2 i (by simpa using hi)

theorem xs_mem (n o : ℕ) : ∀ (K : List ℕ) (g : ℕ → Bool), bvo n o (xs K g) ∈ sp n o K
  | [], _ => by
    rw [sp_nil, Submodule.mem_bot]
    exact bvo_zero n o
  | x :: K, g => by
    change bvo n o (Nat.xor (if g 0 then x else 0) (xs K fun i => g (i + 1))) ∈ _
    rw [bvo_xor, sp_cons]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (xs_mem n o K _))
    split_ifs
    · exact Submodule.mem_span_singleton_self _
    · rw [bvo_zero]
      exact Submodule.zero_mem _

theorem finrank_desc (n : ℕ) : ∀ (K : List ℕ) (b : ℕ), b ≤ n → Desc K b →
    finrank (ZMod 2) (sp n 0 K) = K.length
  | [], _, _, _ => by
    rw [sp_nil]
    exact finrank_bot _ _
  | x :: K, b, hb, ⟨t, htb, hxt, _, hK⟩ => by
    rw [sp_cons, List.length_cons, ← finrank_desc n K t (by omega) hK]
    refine finrank_span_sup _ fun hmem => ?_
    have hvan : ∀ w ∈ sp n 0 K, w ⟨t, by omega⟩ = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        change (if y.testBit (t + 0) then (1 : ZMod 2) else 0) = 0
        rw [Nat.add_zero, desc_low hK y hy t le_rfl]
        rfl
      | zero => rfl
      | add x y _ _ hx hy => rw [Pi.add_apply, hx, hy, add_zero]
      | smul c x _ hx => rw [Pi.smul_apply, hx, smul_zero]
    have h1 := hvan _ hmem
    change (if x.testBit (t + 0) then (1 : ZMod 2) else 0) = 0 at h1
    rw [Nat.add_zero, hxt] at h1
    exact absurd h1 (by decide)

theorem xsel_go (m : ℕ) : ∀ (K : List ℕ) (j : ℕ),
    (List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
      (fun x _ ih j => Nat.xor (Bool.rec (motive := fun _ => ℕ) 0 x (bitK m j)) (ih (Nat.succ j)))
      K j : ℕ) = xs K fun i => m.testBit (j + i)
  | [], _ => rfl
  | x :: K, j => by
    change Nat.xor (Bool.rec (motive := fun _ => ℕ) 0 x (bitK m j)) _ =
      Nat.xor (if m.testBit (j + 0) then x else 0) (xs K fun i => m.testBit (j + (i + 1)))
    rw [xsel_go m K (Nat.succ j), bitK_testBit, Nat.add_zero]
    have e : (fun i => m.testBit (Nat.succ j + i)) = fun i => m.testBit (j + (i + 1)) := by
      funext i
      congr 1
      omega
    rw [e]
    cases m.testBit j <;> rfl

theorem xsel_eq (K : List ℕ) (m : ℕ) : xsel K m = xs K fun i => m.testBit i := by
  have h := xsel_go m K 0
  simp only [Nat.zero_add] at h
  exact h

variable (W : ℕ) (P : List (ℕ × ℕ)) (L : (Fin 25 → ZMod 2) →ₗ[ZMod 2] (Fin W → ZMod 2))

@[expose] noncomputable def r0 (k : ℕ) : ℕ :=
  Nat.lor (Nat.shiftLeft (imgK P k) 25) (Nat.shiftLeft 1 k)

noncomputable def stepE (k : ℕ) (st : List ℕ × List ℕ) : List ℕ × List ℕ :=
  Bool.rec (motive := fun _ => List ℕ × List ℕ)
    (insK 25 st.1 (W - 1) (redK 25 st.1 (W - 1) (r0 P k)), st.2)
    (st.1, redK 25 st.1 (W - 1) (r0 P k) :: st.2)
    (Nat.blt (redK 25 st.1 (W - 1) (r0 P k)) 33554432)

theorem letB_pair (y : ℕ) (k : ℕ → List ℕ × List ℕ) : elimK.letB y k = k y := by
  cases y <;> rfl

theorem elimK_succ (k : ℕ) : elimK P W (k + 1) = stepE W P k (elimK P W k) := by
  have e : elimK P W (k + 1) = Prod.rec (motive := fun _ => List ℕ × List ℕ)
      (fun slots ker => elimK.letB (r0 P k) fun r0 =>
        elimK.letB (redK 25 slots (Nat.sub W 1) r0) fun r =>
          Bool.rec (motive := fun _ => List ℕ × List ℕ) (insK 25 slots (Nat.sub W 1) r, ker)
            (slots, r :: ker) (Nat.blt r 33554432)) (elimK P W k) := rfl
  rw [e]
  rcases elimK P W k with ⟨S, K⟩
  change elimK.letB (r0 P k) _ = _
  rw [letB_pair, letB_pair]
  rfl

def Aug (k x : ℕ) : Prop :=
  bvo W 25 x = L (bvo 25 0 x) ∧ (∀ v, 25 + W ≤ v → x.testBit v = false) ∧
    ∀ v, k ≤ v → v < 25 → x.testBit v = false

theorem aug_xc (k : ℕ) : XC (Aug W L k) := by
  rintro r s ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
  refine ⟨by rw [bvo_xor, bvo_xor, h1, g1, map_add], fun v hv => ?_, fun v hv hv' => ?_⟩
  · rw [xor_testBit, h2 v hv, g2 v hv]
    rfl
  · rw [xor_testBit, h3 v hv hv', g3 v hv hv']
    rfl

theorem aug_mono {k k' x : ℕ} (hk : k ≤ k') (h : Aug W L k x) : Aug W L k' x :=
  ⟨h.1, h.2.1, fun v hv hv' => h.2.2 v (by omega) hv'⟩

structure Inv (k : ℕ) (S K : List ℕ) : Prop where
  len : S.length = W
  ech : W = 0 ∨ Ech 25 S (W - 1)
  augS : ∀ x ∈ S, Aug W L k x
  augK : ∀ x ∈ K, Aug W L k x ∧ x < 2 ^ 25
  desc : Desc K k
  cnt : cntNZ S + K.length = k

theorem zerosK_spec : ∀ W : ℕ, (zerosK W).length = W ∧ (∀ t, Ech 25 (zerosK W) t) ∧
    (∀ x ∈ zerosK W, x = 0) ∧ cntNZ (zerosK W) = 0
  | 0 => ⟨rfl, fun _ => trivial, by simp [zerosK], rfl⟩
  | W + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := zerosK_spec W
    change (0 :: zerosK W).length = _ ∧ (∀ t, Ech 25 (0 :: zerosK W) t) ∧
      (∀ x ∈ 0 :: zerosK W, x = 0) ∧ cntNZ (0 :: zerosK W) = 0
    refine ⟨by rw [List.length_cons, h1], fun t => And.intro (Or.inl rfl) (h2 _), fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact h3 x hx
    · rw [cntNZ_cons, h4, if_pos rfl]

theorem aug_zero (k : ℕ) : Aug W L k 0 := by
  refine ⟨?_, fun v _ => Nat.zero_testBit v, fun v _ _ => Nat.zero_testBit v⟩
  rw [bvo_zero, bvo_zero, map_zero]

theorem inv_zero : Inv W L 0 (elimK P W 0).1 (elimK P W 0).2 := by
  have e : elimK P W 0 = (zerosK W, []) := rfl
  rw [e]
  obtain ⟨h1, h2, h3, h4⟩ := zerosK_spec W
  exact ⟨h1, Or.inr (h2 _), fun x hx => by rw [h3 x hx]; exact aug_zero W L 0,
    fun x hx => by simp at hx, trivial, by rw [h4]; rfl⟩

theorem r0_testBit (k v : ℕ) (hk : k < 25) :
    (r0 P k).testBit v = ((decide (25 ≤ v) && (imgK P k).testBit (v - 25)) || decide (v = k)) := by
  unfold r0
  change ((imgK P k <<< 25) ||| (1 <<< k)).testBit v = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow]
  have e : decide (k = v) = decide (v = k) := by
    by_cases h : v = k
    · rw [h]
    · rw [decide_eq_false h, decide_eq_false (Ne.symm h)]
  rw [e]

theorem aug_r0 (hlt : ∀ idx < 25, imgK P idx < 2 ^ W)
    (hL : ∀ idx < 25, bvo W 0 (imgK P idx) = L (bvo 25 0 (2 ^ idx))) {k : ℕ} (hk : k < 25) :
    Aug W L (k + 1) (r0 P k) ∧ (r0 P k).testBit k = true := by
  have hb := r0_testBit P k
  refine ⟨⟨?_, fun v hv => ?_, fun v hv hv' => ?_⟩, ?_⟩
  · have e1 : bvo W 25 (r0 P k) = bvo W 0 (imgK P k) := by
      funext p
      change (if (r0 P k).testBit (p + 25) then (1 : ZMod 2) else 0) =
        if (imgK P k).testBit (p + 0) then 1 else 0
      rw [hb _ hk]
      simp only [Nat.add_sub_cancel, Nat.add_zero]
      have h1 : decide (25 ≤ (p : ℕ) + 25) = true := by simp
      have h2 : decide ((p : ℕ) + 25 = k) = false := decide_eq_false (by omega)
      rw [h1, h2, Bool.true_and, Bool.or_false]
    have e2 : bvo 25 0 (r0 P k) = bvo 25 0 (2 ^ k) := by
      funext q
      change (if (r0 P k).testBit (q + 0) then (1 : ZMod 2) else 0) =
        if (2 ^ k).testBit (q + 0) then 1 else 0
      rw [hb _ hk, Nat.add_zero, Nat.testBit_two_pow]
      have h1 : decide (25 ≤ (q : ℕ)) = false := decide_eq_false (by have := q.isLt; omega)
      rw [h1, Bool.false_and, Bool.false_or]
      by_cases hq : (q : ℕ) = k
      · simp [hq]
      · simp [hq, Ne.symm hq]
    rw [e1, e2, hL k hk]
  · rw [hb _ hk]
    have h1 : (imgK P k).testBit (v - 25) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hlt k hk)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h2 : decide (v = k) = false := decide_eq_false (by omega)
    rw [h1, h2]
    simp
  · rw [hb _ hk]
    have h1 : decide (25 ≤ v) = false := decide_eq_false (by omega)
    have h2 : decide (v = k) = false := decide_eq_false (by omega)
    rw [h1, h2]
    rfl
  · rw [hb _ hk]
    simp

theorem inv_step (hlt : ∀ idx < 25, imgK P idx < 2 ^ W)
    (hL : ∀ idx < 25, bvo W 0 (imgK P idx) = L (bvo 25 0 (2 ^ idx))) {k : ℕ} (hk : k < 25)
    {S K : List ℕ} (h : Inv W L k S K) :
    Inv W L (k + 1) (stepE W P k (S, K)).1 (stepE W P k (S, K)).2 := by
  obtain ⟨hlen, hech, haugS, haugK, hdesc, hcnt⟩ := h
  obtain ⟨ha0, hbk⟩ := aug_r0 W P L hlt hL hk
  set r := redK 25 S (W - 1) (r0 P k) with hr
  have hSk : ∀ x ∈ S, x.testBit k = false := fun x hx => (haugS x hx).2.2 k le_rfl hk
  have props : Aug W L (k + 1) r ∧ r.testBit k = true ∧
      (W ≠ 0 → Red 25 r S (W - 1) ∧ Low (W - 1 + 25) r) ∧ (W = 0 → r < 2 ^ 25) := by
    rcases Nat.eq_zero_or_pos W with h0 | hW
    · have hS : S = [] := List.eq_nil_of_length_eq_zero (hlen.trans h0)
      have e : r = r0 P k := by rw [hr, hS]; rfl
      refine ⟨e ▸ ha0, e ▸ hbk, fun h => absurd h0 h, fun _ => ?_⟩
      rw [e]
      apply Nat.lt_pow_two_of_testBit
      intro v hv
      rw [r0_testBit P k v hk]
      have hi : imgK P k = 0 := by
        have := hlt k hk
        rw [h0, pow_zero] at this
        omega
      rw [hi, Nat.zero_testBit]
      have h2 : decide (v = k) = false := decide_eq_false (by omega)
      rw [h2]
      simp
    · have hE : Ech 25 S (W - 1) := hech.resolve_left (by omega)
      obtain ⟨g1, g2, g3, g4⟩ := redK_spec 1 k 25 S (W - 1) (r0 P k) (by omega) hE
      have hsp : sp 1 k S = ⊥ := by
        unfold sp
        rw [Submodule.span_eq_bot]
        rintro _ ⟨x, hx, rfl⟩
        exact bvo_eq_zero' (hSk x hx)
      rw [hsp, Submodule.mem_bot] at g3
      have hbit : r.testBit k = true := by
        have e := congrFun g3 0
        change (if r.testBit (0 + k) then (1 : ZMod 2) else 0) +
          (if (r0 P k).testBit (0 + k) then 1 else 0) = 0 at e
        rw [Nat.zero_add, hbk] at e
        cases hrk : r.testBit k
        · rw [hrk] at e
          exact absurd e (by decide)
        · rfl
      refine ⟨g4 _ (aug_xc W L (k + 1)) (fun x hx => aug_mono W L (Nat.le_succ k) (haugS x hx)) ha0,
        hbit, fun _ => ⟨g2, fun v hv => ?_⟩, fun h => absurd h (by omega)⟩
      rw [g1 v hv]
      exact ha0.2.1 v (by omega)
  obtain ⟨hra, hrk, hrR, hr0⟩ := props
  have e25 : (33554432 : ℕ) = 2 ^ 25 := by norm_num
  have estep : stepE W P k (S, K) = Bool.rec (motive := fun _ => List ℕ × List ℕ)
      (insK 25 S (W - 1) r, K) (S, r :: K) (Nat.blt r 33554432) := rfl
  rw [estep]
  cases hb : Nat.blt r 33554432
  · have hsmall : ¬ r < 33554432 := by
      rw [← Nat.blt_eq, hb]
      decide
    change Inv W L (k + 1) (insK 25 S (W - 1) r) K
    have hW : W ≠ 0 := fun h0 => hsmall (by rw [e25]; exact hr0 h0)
    obtain ⟨hR, hLow⟩ := hrR hW
    have hE : Ech 25 S (W - 1) := hech.resolve_left hW
    obtain ⟨i1, i2, -, i4⟩ := insK_spec W 25 S (W - 1) r (by omega) hE hLow
    have hplace := insK_place 25 S (W - 1) r (by omega) hR hLow (by
      by_contra hno
      apply hsmall
      have : r < 2 ^ 25 := Nat.lt_pow_two_of_testBit r fun v hv => by
        cases h : r.testBit v
        · rfl
        · exact absurd ⟨v, hv, h⟩ hno
      rw [e25]
      exact this)
    refine ⟨i1.trans hlen, Or.inr i2, i4 _ (aug_xc W L (k + 1))
      (fun x hx => aug_mono W L (Nat.le_succ k) (haugS x hx)) hra,
      fun x hx => ⟨aug_mono W L (Nat.le_succ k) (haugK x hx).1, (haugK x hx).2⟩,
      desc_mono (Nat.le_succ k) hdesc, by omega⟩
  · have hsmall : r < 33554432 := by
      rw [← Nat.blt_eq, hb]
    change Inv W L (k + 1) S (r :: K)
    refine ⟨hlen, hech, fun x hx => aug_mono W L (Nat.le_succ k) (haugS x hx), fun x hx => ?_,
      ⟨k, by omega, hrk, fun v hv => ?_, hdesc⟩, by rw [List.length_cons]; omega⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hra, by rw [← e25]; exact hsmall⟩
      · exact ⟨aug_mono W L (Nat.le_succ k) (haugK x hx).1, (haugK x hx).2⟩
    · rcases Nat.lt_or_ge v 25 with h25 | h25
      · exact hra.2.2 v (by omega) h25
      · have hs25 : r < 2 ^ 25 := by
          rw [← e25]
          exact hsmall
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs25 (Nat.pow_le_pow_right (by norm_num) h25))
where
  bvo_eq_zero' {x : ℕ} (h : x.testBit k = false) : bvo 1 k x = 0 := by
    funext p
    change (if x.testBit (p + k) then (1 : ZMod 2) else 0) = 0
    have e : (p : ℕ) + k = k := by omega
    rw [e, h]
    rfl

theorem inv_all (hlt : ∀ idx < 25, imgK P idx < 2 ^ W)
    (hL : ∀ idx < 25, bvo W 0 (imgK P idx) = L (bvo 25 0 (2 ^ idx))) :
    ∀ k ≤ 25, Inv W L k (elimK P W k).1 (elimK P W k).2
  | 0, _ => inv_zero W P L
  | k + 1, hk => by
    rw [elimK_succ]
    have h := inv_all hlt hL k (by omega)
    rcases e : elimK P W k with ⟨S, K⟩
    rw [e] at h
    exact inv_step W P L hlt hL (by omega) h

theorem elim_basis (hlt : ∀ idx < 25, imgK P idx < 2 ^ W)
    (hL : ∀ idx < 25, bvo W 0 (imgK P idx) = L (bvo 25 0 (2 ^ idx))) :
    sp 25 0 (elimK P W 25).2 = LinearMap.ker L ∧
      finrank (ZMod 2) (LinearMap.ker L) = (elimK P W 25).2.length := by
  obtain ⟨hlen, hech, haugS, haugK, hdesc, hcnt⟩ := inv_all W P L hlt hL 25 le_rfl
  set S := (elimK P W 25).1
  set K := (elimK P W 25).2
  have hK : sp 25 0 K ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← (haugK x hx).1.1]
    exact bvo_eq_zero fun v hv => Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (haugK x hx).2
      (Nat.pow_le_pow_right (by norm_num) hv))
  have hS : sp W 25 S ≤ LinearMap.range L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, (haugS x hx).1]
    exact LinearMap.mem_range_self L _
  have fK : finrank (ZMod 2) (sp 25 0 K) = K.length := finrank_desc 25 K 25 le_rfl hdesc
  have fS : finrank (ZMod 2) (sp W 25 S) = cntNZ S := by
    rcases Nat.eq_zero_or_pos W with h0 | hW
    · have hS0 : S = [] := List.eq_nil_of_length_eq_zero (hlen.trans h0)
      rw [hS0, sp_nil]
      exact (finrank_bot _ _).trans rfl
    · exact finrank_ech W 25 S (W - 1) (by omega) (by omega) (hech.resolve_left (by omega))
  have rn := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_fin_fun] at rn
  have m1 := Submodule.finrank_mono hK
  have m2 := Submodule.finrank_mono hS
  have hk : finrank (ZMod 2) (sp 25 0 K) = finrank (ZMod 2) (LinearMap.ker L) := by omega
  exact ⟨Submodule.eq_of_le_of_finrank_eq hK hk, by omega⟩

theorem unitCntR_eq (K : List ℕ) : ∀ n,
    unitCntR K 0 n = ((Finset.range n).filter fun m => rankK (xsel K m) = 5).card
  | 0 => rfl
  | n + 1 => by
    change Nat.add (unitCntR K 0 n) (Bool.rec (motive := fun _ => ℕ) 0 1
      (Nat.beq (rankK (xsel K (Nat.add 0 n))) 5)) = _
    have e0 : Nat.add 0 n = n := Nat.zero_add n
    rw [unitCntR_eq K n, Finset.range_add_one, Finset.filter_insert, e0]
    by_cases h : rankK (xsel K n) = 5
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), h]
      rfl
    · have hb : Nat.beq (rankK (xsel K n)) 5 = false := by
        rw [Bool.eq_false_iff]
        exact fun e => h (Nat.eq_of_beq_eq_true e)
      rw [if_neg h, hb]
      rfl

theorem bvo25_inj {c c' : ℕ} (hc : c < 2 ^ 25) (hc' : c' < 2 ^ 25) (e : bvo 25 0 c = bvo 25 0 c') :
    c = c' := by
  apply Nat.eq_of_testBit_eq
  intro q
  rcases Nat.lt_or_ge q 25 with hq | hq
  · have e1 := congrFun e ⟨q, hq⟩
    change (if c.testBit (q + 0) then (1 : ZMod 2) else 0) = if c'.testBit (q + 0) then 1 else 0 at e1
    rw [Nat.add_zero] at e1
    cases h1 : c.testBit q <;> cases h2 : c'.testBit q <;> rw [h1, h2] at e1 <;> simp_all
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hq)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc' (Nat.pow_le_pow_right (by norm_num) hq))]

open scoped Classical in
theorem elim_count (hlt : ∀ idx < 25, imgK P idx < 2 ^ W)
    (hL : ∀ idx < 25, bvo W 0 (imgK P idx) = L (bvo 25 0 (2 ^ idx))) :
    unitCntK (elimK P W 25).2 =
      ((Finset.range (2 ^ 25)).filter fun c => L (bvo 25 0 c) = 0 ∧ rankK c = 5).card := by
  obtain ⟨-, -, -, haugK, hdesc, -⟩ := inv_all W P L hlt hL 25 le_rfl
  obtain ⟨hsp, hfr⟩ := elim_basis W P L hlt hL
  set K := (elimK P W 25).2 with hKdef
  set d := K.length with hd
  have hK25 : ∀ x ∈ K, ∀ v, 25 ≤ v → x.testBit v = false := fun x hx v hv =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (haugK x hx).2 (Nat.pow_le_pow_right (by norm_num) hv))
  have hxs_lt : ∀ m, xsel K m < 2 ^ 25 := fun m => by
    rw [xsel_eq]
    exact Nat.lt_pow_two_of_testBit _ fun v hv => xs_testBit_high K _ v fun x hx => hK25 x hx v hv
  have hxs_ker : ∀ m, L (bvo 25 0 (xsel K m)) = 0 := fun m => by
    rw [← LinearMap.mem_ker, ← hsp, xsel_eq]
    exact xs_mem 25 0 K _
  set Z := (Finset.range (2 ^ 25)).filter fun c => L (bvo 25 0 c) = 0 with hZ
  have hinj : Set.InjOn (xsel K) ↑(Finset.range (2 ^ d)) := by
    intro m hm m' hm' e
    rw [Finset.coe_range, Set.mem_Iio] at hm hm'
    rw [xsel_eq, xsel_eq] at e
    apply Nat.eq_of_testBit_eq
    intro i
    rcases Nat.lt_or_ge i d with hi | hi
    · exact xs_inj K 25 hdesc _ _ e i hi
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hi)),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by norm_num) hi))]
  have himg_sub : (Finset.range (2 ^ d)).image (xsel K) ⊆ Z := by
    intro c hc
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hc
    rw [hZ, Finset.mem_filter, Finset.mem_range]
    exact ⟨hxs_lt m, hxs_ker m⟩
  have hZcard : Z.card ≤ 2 ^ d := by
    have h1 : Z.card ≤ (Finset.univ.filter fun v : Fin 25 → ZMod 2 => v ∈ LinearMap.ker L).card := by
      refine Finset.card_le_card_of_injOn (bvo 25 0) (fun c hc => ?_) (fun c hc c' hc' e => ?_)
      · rw [hZ, Finset.coe_filter] at hc
        rw [Finset.coe_filter]
        exact ⟨Finset.mem_univ _, LinearMap.mem_ker.2 hc.2⟩
      · rw [hZ, Finset.coe_filter] at hc hc'
        exact bvo25_inj (Finset.mem_range.1 hc.1) (Finset.mem_range.1 hc'.1) e
    have h2 : (Finset.univ.filter fun v : Fin 25 → ZMod 2 => v ∈ LinearMap.ker L).card = 2 ^ d := by
      rw [← Fintype.card_subtype, ← hfr]
      have h3 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker L)
      rw [ZMod.card] at h3
      convert h3
    omega
  have himg : (Finset.range (2 ^ d)).image (xsel K) = Z :=
    Finset.eq_of_subset_of_card_le himg_sub (by rw [Finset.card_image_of_injOn hinj, Finset.card_range]; exact hZcard)
  have e1 : unitCntK K = ((Finset.range (2 ^ d)).filter fun m => rankK (xsel K m) = 5).card := by
    change unitCntR K 0 (Nat.pow 2 K.length) = _
    rw [unitCntR_eq]
    rfl
  rw [e1, ← Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))),
    ← Finset.filter_image (p := fun c => rankK c = 5), himg, hZ, Finset.filter_filter]

end CFSG.KC.Misc.GLM.Ech

end
