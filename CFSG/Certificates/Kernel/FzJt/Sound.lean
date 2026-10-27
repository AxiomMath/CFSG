module

public import Certificates.Data.Kernel.FzJt.Codes
public import Certificates.Data.FzJtCheck

public section

namespace Certificates.FzJt.K

open Certificates.FzJ36
open Certificates.FzFus (mkE z1M z3M IsInvM)

theorem bA_iff {a b : Bool} : bA a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [bA]

theorem bO_iff {a b : Bool} : bO a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [bO]

theorem bI_iff {a b : Bool} : bI a b = true ↔ (a = true → b = true) := by
  cases a <;> simp [bI]

theorem bN_iff {a : Bool} : bN a = true ↔ a = false := by
  cases a <;> simp [bN]

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b := by
  simp

theorem eqL_iff {l₁ l₂ : List Nat} : eqL l₁ l₂ = true ↔ l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [eqL]
  | cons x xs ih =>
    cases l₂ with
    | nil => simp [eqL]
    | cons y ys =>
      have h : eqL (x :: xs) (y :: ys) = bA (Nat.beq x y) (eqL xs ys) := rfl
      rw [h, bA_iff, beq_iff, ih, List.cons.injEq]

theorem mem_filterR {n : Nat} {p : Nat → Bool} {x : Nat} :
    x ∈ filterR n p ↔ ∃ t < n, rep t = x ∧ p (rep t) = true := by
  induction n with
  | zero => simp [filterR]
  | succ n ih =>
    have h : filterR (n + 1) p = Bool.rec (filterR n p) (rep n :: filterR n p) (p (rep n)) := rfl
    rw [h]
    constructor
    · intro hx
      cases hp : p (rep n) <;> rw [hp] at hx
      · obtain ⟨t, ht, h1, h2⟩ := ih.mp hx
        exact ⟨t, by omega, h1, h2⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨n, by omega, rfl, hp⟩
        · obtain ⟨t, ht, h1, h2⟩ := ih.mp hx
          exact ⟨t, by omega, h1, h2⟩
    · rintro ⟨t, ht, rfl, h2⟩
      have hmem : t < n → rep t ∈ filterR n p := fun h => ih.mpr ⟨t, h, rfl, h2⟩
      cases hp : p (rep n)
      · have htn : t ≠ n := by
          rintro rfl
          rw [hp] at h2
          exact Bool.false_ne_true h2
        exact hmem (by omega)
      · by_cases htn : t = n
        · subst htn
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hmem (by omega))

theorem mem_filterL {L : List Nat} {p : Nat → Bool} {x : Nat} :
    x ∈ filterL L p ↔ x ∈ L ∧ p x = true := by
  induction L with
  | nil => simp [filterL]
  | cons y ys ih =>
    have h : filterL (y :: ys) p = Bool.rec (filterL ys p) (y :: filterL ys p) (p y) := rfl
    rw [h]
    cases hp : p y
    · simp only [ih, List.mem_cons]
      constructor
      · exact fun h => ⟨Or.inr h.1, h.2⟩
      · rintro ⟨rfl | h1, h2⟩
        · rw [hp] at h2
          exact absurd h2 Bool.false_ne_true
        · exact ⟨h1, h2⟩
    · simp only [ih, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact ⟨Or.inl rfl, hp⟩
        · exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩

theorem allL_iff {L : List Nat} {f : Nat → Bool} : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allL]
  | cons y ys ih =>
    have h : allL (y :: ys) f = bA (f y) (allL ys f) := rfl
    rw [h, bA_iff, ih, List.forall_mem_cons]

theorem or_ex_cons {p : Nat → Prop} {y : Nat} {ys : List Nat} :
    (p y ∨ ∃ x ∈ ys, p x) ↔ ∃ x ∈ y :: ys, p x := by
  constructor
  · rintro (h | ⟨x, hx, h⟩)
    · exact ⟨y, List.mem_cons_self, h⟩
    · exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
  · rintro ⟨x, hx, h⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, h⟩

theorem anyL_iff{L : List Nat} {f : Nat → Bool} : anyL L f = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => simp [anyL]
  | cons y ys ih =>
    have h : anyL (y :: ys) f = bO (f y) (anyL ys f) := rfl
    rw [h, bO_iff, ih]
    exact or_ex_cons (p := fun x => f x = true)

theorem memL_iff {x : Nat} {L : List Nat} : memL x L = true ↔ x ∈ L := by
  induction L with
  | nil => simp [memL]
  | cons y ys ih =>
    have h : memL x (y :: ys) = bO (Nat.beq x y) (memL x ys) := rfl
    rw [h, bO_iff, beq_iff, ih, List.mem_cons]

theorem allR_iff {n : Nat} {f : Nat → Bool} : allR n f = true ↔ ∀ t < n, f (rep t) = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    have h : allR (n + 1) f = bA (f (rep n)) (allR n f) := rfl
    rw [h, bA_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ t ht
      by_cases htn : t = n
      · exact htn ▸ h1
      · exact h2 t (by omega)
    · intro h
      exact ⟨h n (by omega), fun t ht => h t (by omega)⟩

theorem anyN_iff {n : Nat} {f : Nat → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [anyN]
  | succ n ih =>
    have h : anyN (n + 1) f = bO (f n) (anyN n f) := rfl
    rw [h, bO_iff, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hin : i = n
      · exact Or.inl (hin ▸ h)
      · exact Or.inr ⟨i, by omega, h⟩

theorem mem_lowL {x : Nat} {L : List Nat} : x ∈ lowL L ↔ ∃ y ∈ L, Nat.land y 1023 = x := by
  induction L with
  | nil => simp [lowL]
  | cons y ys ih =>
    have h : lowL (y :: ys) = Nat.land y 1023 :: lowL ys := rfl
    rw [h, List.mem_cons, ih, ← or_ex_cons (p := fun y => Nat.land y 1023 = x)]
    exact or_congr eq_comm Iff.rfl

theorem allRows_iff {R : List (List Nat)} {f : List Nat → Bool} :
    allRows R f = true ↔ ∀ r ∈ R, f r = true := by
  induction R with
  | nil => simp [allRows]
  | cons r rs ih =>
    have h : allRows (r :: rs) f = bA (f r) (allRows rs f) := rfl
    rw [h, bA_iff, ih, List.forall_mem_cons]

theorem mem_heads {R : List (List Nat)} {x : Nat} (h : x ∈ heads R) :
    ∃ t : List Nat, x :: t ∈ R := by
  induction R with
  | nil => simp [heads] at h
  | cons r rs ih =>
    cases r with
    | nil =>
      have h' : heads ([] :: rs) = heads rs := rfl
      rw [h'] at h
      obtain ⟨t, ht⟩ := ih h
      exact ⟨t, List.mem_cons_of_mem _ ht⟩
    | cons v t =>
      have h' : heads ((v :: t) :: rs) = v :: heads rs := rfl
      rw [h', List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨t, List.mem_cons_self⟩
      · obtain ⟨t', ht⟩ := ih h
        exact ⟨t', List.mem_cons_of_mem _ ht⟩

@[expose] def qc : Q8 → Nat
  | .a i => i.val
  | .xa i => 4 + i.val

@[expose] def ec (e : Multiplicative (ZMod 2)) : Nat := (Multiplicative.toAdd e).val

@[expose] def rawc (g : Model) : Nat := mk (qc g.left.1) (qc g.left.2.1) (qc g.left.2.2) (ec g.right)

@[expose] def code (g : Model) : Nat := nz (rawc g)

@[expose] def qd (n : Nat) : Q8 := if n < 4 then .a (n : ZMod 4) else .xa ((n - 4 : Nat) : ZMod 4)

@[expose] def dec (c : Nat) : Model :=
  ⟨(qd (Nat.land c 7), qd (Nat.land (Nat.shiftRight c 3) 7), qd (Nat.land (Nat.shiftRight c 6) 7)),
    Multiplicative.ofAdd ((Nat.shiftRight c 9 : Nat) : ZMod 2)⟩

theorem qc_lt (q : Q8) : qc q < 8 := by
  revert q
  decide

theorem qc_inj {p q : Q8} (h : qc p = qc q) : p = q := by
  revert p q
  decide

theorem qm_qc (p q : Q8) : qm (qc p) (qc q) = qc (p * q) := by
  revert p q
  decide +kernel

theorem qc_mul_a2 (q : Q8) : qc (q * QuaternionGroup.a 2) = Nat.xor (qc q) 2 := by
  revert q
  decide

theorem qc_qd : ∀ n, n < 8 → qc (qd n) = n := by
  decide

theorem zmod2' (e : Multiplicative (ZMod 2)) : e = 1 ∨ e = Multiplicative.ofAdd 1 := by
  revert e
  decide

theorem ec_lt (e : Multiplicative (ZMod 2)) : ec e < 2 := by
  revert e
  decide

theorem ec_inj {e f : Multiplicative (ZMod 2)} (h : ec e = ec f) : e = f := by
  revert e f
  decide

theorem ec_ed : ∀ n, n < 2 → ec (Multiplicative.ofAdd ((n : Nat) : ZMod 2)) = n := by
  decide

theorem lanesF : ∀ x y z : Fin 8, ∀ e : Fin 2,
    mk x y z e < 1024 ∧ Nat.land (mk x y z e) 7 = x ∧
    Nat.land (Nat.shiftRight (mk x y z e) 3) 7 = y ∧
    Nat.land (Nat.shiftRight (mk x y z e) 6) 7 = z ∧ Nat.shiftRight (mk x y z e) 9 = e ∧
    mk (Nat.xor x 2) (Nat.xor y 2) (Nat.xor z 2) e = Nat.xor (mk x y z e) 146 := by
  decide +kernel

theorem lanes (x : Nat) (hx : x < 8) (y : Nat) (hy : y < 8) (z : Nat) (hz : z < 8) (e : Nat)
    (he : e < 2) :
    mk x y z e < 1024 ∧ Nat.land (mk x y z e) 7 = x ∧
    Nat.land (Nat.shiftRight (mk x y z e) 3) 7 = y ∧
    Nat.land (Nat.shiftRight (mk x y z e) 6) 7 = z ∧ Nat.shiftRight (mk x y z e) 9 = e ∧
    mk (Nat.xor x 2) (Nat.xor y 2) (Nat.xor z 2) e = Nat.xor (mk x y z e) 146 :=
  lanesF ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨e, he⟩

theorem mk_lanes : ∀ c, c < 1024 →
    mk (Nat.land c 7) (Nat.land (Nat.shiftRight c 3) 7) (Nat.land (Nat.shiftRight c 6) 7)
      (Nat.shiftRight c 9) = c ∧ Nat.land c 7 < 8 ∧ Nat.land (Nat.shiftRight c 3) 7 < 8 ∧
      Nat.land (Nat.shiftRight c 6) 7 < 8 ∧ Nat.shiftRight c 9 < 2 := by
  decide +kernel

theorem nz_facts : ∀ c, c < 1024 →
    nz (Nat.xor c 146) = nz c ∧ (nz c = c ∨ nz c = Nat.xor c 146) ∧
    Nat.shiftRight (nz c) 9 = Nat.shiftRight c 9 ∧
    Nat.add (Nat.land (nz c) 127) (Nat.shiftLeft (Nat.shiftRight (nz c) 8) 7) < 512 ∧
    rep (Nat.add (Nat.land (nz c) 127) (Nat.shiftLeft (Nat.shiftRight (nz c) 8) 7)) = nz c ∧
    (isC c = true → nz c = c) := by
  decide +kernel

theorem rawc_lanes (g : Model) :
    rawc g < 1024 ∧ Nat.land (rawc g) 7 = qc g.left.1 ∧
    Nat.land (Nat.shiftRight (rawc g) 3) 7 = qc g.left.2.1 ∧
    Nat.land (Nat.shiftRight (rawc g) 6) 7 = qc g.left.2.2 ∧
    Nat.shiftRight (rawc g) 9 = ec g.right ∧
    mk (Nat.xor (qc g.left.1) 2) (Nat.xor (qc g.left.2.1) 2) (Nat.xor (qc g.left.2.2) 2) (ec g.right)
      = Nat.xor (rawc g) 146 :=
  lanes _ (qc_lt _) _ (qc_lt _) _ (qc_lt _) _ (ec_lt _)

theorem rawc_lt (g : Model) : rawc g < 1024 := (rawc_lanes g).1

theorem rawc_inj {g h : Model} (hgh : rawc g = rawc h) : g = h := by
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := rawc_lanes g
  obtain ⟨-, h1', h2', h3', h4', -⟩ := rawc_lanes h
  rw [hgh] at h1 h2 h3 h4
  obtain ⟨⟨g1, g2, g3⟩, e⟩ := g
  obtain ⟨⟨k1, k2, k3⟩, f⟩ := h
  simp only at h1 h2 h3 h4 h1' h2' h3' h4'
  have e1 := qc_inj (h1.symm.trans h1')
  have e2 := qc_inj (h2.symm.trans h2')
  have e3 := qc_inj (h3.symm.trans h3')
  have e4 := ec_inj (h4.symm.trans h4')
  subst e1 e2 e3 e4
  rfl

theorem rawc_dec {c : Nat} (hc : c < 1024) : rawc (dec c) = c := by
  obtain ⟨hm, l1, l2, l3, l4⟩ := mk_lanes c hc
  unfold rawc dec
  simp only
  rw [qc_qd _ l1, qc_qd _ l2, qc_qd _ l3]
  unfold ec
  rw [toAdd_ofAdd]
  have := ec_ed _ l4
  unfold ec at this
  rw [toAdd_ofAdd] at this
  rw [this, hm]

theorem mul_one_left (q1 q2 q3 : Q8) (h : Model) :
    (⟨(q1, q2, q3), 1⟩ : Model) * h =
      ⟨(q1 * h.left.1, q2 * h.left.2.1, q3 * h.left.2.2), h.right⟩ := by
  apply SemidirectProduct.ext
  · change (q1, q2, q3) * act 1 h.left = _
    rw [map_one, MulAut.one_apply]
    rfl
  · exact one_mul _

theorem mul_swap_left (q1 q2 q3 : Q8) (h : Model) :
    (⟨(q1, q2, q3), Multiplicative.ofAdd 1⟩ : Model) * h =
      ⟨(q1 * h.left.2.1, q2 * h.left.1, q3 * h.left.2.2), Multiplicative.ofAdd 1 * h.right⟩ := by
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hact : act (Multiplicative.ofAdd 1) = swapAut := by simp [act, hne]
  apply SemidirectProduct.ext
  · change (q1, q2, q3) * act (Multiplicative.ofAdd 1) h.left = _
    rw [hact]
    rfl
  · rfl

theorem ec_mul (e f : Multiplicative (ZMod 2)) : ec (e * f) = Nat.xor (ec e) (ec f) := by
  revert e f
  decide

theorem ec_one : ec 1 = 0 := by decide

theorem ec_swap : ec (Multiplicative.ofAdd 1) = 1 := by decide

theorem sw_zero (x y : Nat) : sw 0 x y = x := rfl

theorem sw_one (x y : Nat) : sw 1 x y = y := rfl

theorem mulK_rawc (g h : Model) : mulK (rawc g) (rawc h) = nz (rawc (g * h)) := by
  obtain ⟨-, a1, a2, a3, a4, -⟩ := rawc_lanes g
  obtain ⟨-, b1, b2, b3, b4, -⟩ := rawc_lanes h
  unfold mulK mul5
  rw [a1, a2, a3, a4, b1, b2, b3, b4]
  obtain ⟨⟨q1, q2, q3⟩, e⟩ := g
  rcases zmod2' e with rfl | rfl
  · rw [mul_one_left]
    unfold mul8 rawc
    simp only
    rw [ec_one, sw_zero, sw_zero, qm_qc, qm_qc, qm_qc]
    exact congrArg (fun t => nz (mk _ _ _ t)) (Nat.zero_xor _)
  · rw [mul_swap_left]
    unfold mul8 rawc
    simp only
    rw [ec_mul, ec_swap, sw_one, sw_one, qm_qc, qm_qc, qm_qc]

theorem rawc_zeta (g : Model) : rawc (g * zeta) = Nat.xor (rawc g) 146 := by
  rw [← (rawc_lanes g).2.2.2.2.2]
  obtain ⟨⟨q1, q2, q3⟩, e⟩ := g
  rcases zmod2' e with rfl | rfl
  · rw [mul_one_left]
    unfold rawc
    simp only [zeta]
    rw [qc_mul_a2, qc_mul_a2, qc_mul_a2]
  · rw [mul_swap_left]
    unfold rawc
    simp only [zeta]
    rw [qc_mul_a2, qc_mul_a2, qc_mul_a2]
    simp

theorem code_zeta (g : Model) : code (g * zeta) = code g := by
  unfold code
  rw [rawc_zeta, (nz_facts _ (rawc_lt g)).1]

theorem code_of_keq {g h : Model} (hgh : KEq g h) : code g = code h := by
  rcases hgh with rfl | rfl
  · rfl
  · exact code_zeta h

theorem code_spec (g : Model) : ∃ g' : Model, KEq g' g ∧ code g = rawc g' := by
  rcases (nz_facts _ (rawc_lt g)).2.1 with h | h
  · exact ⟨g, KEq.refl g, h⟩
  · exact ⟨g * zeta, KEq.mul_zeta g, by rw [code, h, rawc_zeta]⟩

theorem code_mul (g h : Model) : code (g * h) = mulK (code g) (code h) := by
  obtain ⟨g', hg, hg'⟩ := code_spec g
  obtain ⟨h', hh, hh'⟩ := code_spec h
  rw [hg', hh', mulK_rawc, ← code, code_of_keq (KEq.mul hg hh)]

theorem code_eq_iff {g h : Model} : code g = code h ↔ KEq g h := by
  constructor
  · intro hgh
    obtain ⟨g', hg, hg'⟩ := code_spec g
    obtain ⟨h', hh, hh'⟩ := code_spec h
    have := rawc_inj (hg'.symm.trans (hgh.trans hh'))
    subst this
    exact hg.symm.trans hh
  · exact code_of_keq

theorem exists_rep (g : Model) : ∃ t < 512, code g = rep t := by
  obtain ⟨-, -, -, h1, h2, -⟩ := nz_facts _ (rawc_lt g)
  exact ⟨_, h1, h2.symm⟩

theorem code_one : code 1 = 0 := by
  decide +kernel

theorem code_dec_of_isC {c : Nat} (hc : isC c = true) : code (dec c) = c := by
  have hlt : c < 1024 := by
    rw [isC, bA_iff] at hc
    simpa using hc.1
  rw [code, rawc_dec hlt, (nz_facts c hlt).2.2.2.2.2 hc]

theorem keq_conj_inv_iff {v w : Model} : KEq (w * v * w⁻¹) v⁻¹ ↔ KEq (v * w * v) w := by
  constructor
  · intro h
    have h' := KEq.mul (KEq.mul (KEq.refl v) h) (KEq.refl w)
    simpa [mul_assoc] using h'
  · intro h
    have h' := KEq.mul (KEq.mul (KEq.refl v⁻¹) h) (KEq.refl w⁻¹)
    simpa [mul_assoc] using h'

theorem commK_code {g h : Model} : commK (code g) (code h) = true ↔ KEq (g * h) (h * g) := by
  rw [commK, beq_iff, ← code_mul, ← code_mul, code_eq_iff]

theorem zList_codes : (zList ()).map code = [2, 16, 18, 512, 537, 530, 523, 564, 573, 550, 559] := by
  decide +kernel

theorem inZK_rep : ∀ t, t < 512 →
    inZK (rep t) = memL (rep t) [2, 16, 18, 512, 537, 530, 523, 564, 573, 550, 559] := by
  decide +kernel

theorem inZK_code (g : Model) : inZK (code g) = true ↔ InZ g := by
  obtain ⟨t, ht, hg⟩ := exists_rep g
  rw [hg, inZK_rep t ht, memL_iff, ← hg, ← zList_codes, List.mem_map, InZ]
  constructor
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, code_eq_iff.mp h.symm⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, (code_eq_iff.mpr h).symm⟩

theorem mulK_code_self_eq_zero {g : Model} : mulK (code g) (code g) = 0 ↔ KEq (g * g) 1 := by
  rw [← code_mul, ← code_one, code_eq_iff]

theorem code_eq_zero {g : Model} : code g = 0 ↔ KEq g 1 := by
  rw [← code_one, code_eq_iff]

theorem f2B_sound {u : Nat} {C S : List Nat} {SV : List (List Nat)} (h : f2B u C S SV = true)
    (g : Model) (hg : code g = u) : ¬ MJ g := by
  subst hg
  rintro ⟨y, v, w, hyu, hvu, hwu, hy1, hy2, hv2, hw2, hwv, hyv, hyw⟩
  unfold f2B at h
  rw [bA_iff, bA_iff, bA_iff] at h
  obtain ⟨hC, hS, hH, hR⟩ := h
  have hC := eqL_iff.mp hC
  have hS := eqL_iff.mp hS
  have hH := eqL_iff.mp hH
  have memC : ∀ x : Model, KEq (x * g) (g * x) → code x ∈ C := fun x hx => by
    rw [← hC, mem_filterR]
    obtain ⟨t, ht, hxt⟩ := exists_rep x
    exact ⟨t, ht, hxt.symm, by rw [← hxt]; exact commK_code.mpr hx⟩
  have memS : ∀ x : Model, KEq (x * g) (g * x) → KEq (x * x) (g * g) → code x ∈ S :=
    fun x hx hxx => by
      rw [← hS, mem_filterL]
      exact ⟨memC x hx, by rw [beq_iff, ← code_mul, ← code_mul, code_eq_iff]; exact hxx⟩
  obtain ⟨Cv, hrow⟩ := mem_heads (hH ▸ memS v hvu hv2 : code v ∈ heads SV)
  have hr := allRows_iff.mp hR _ hrow
  have hr' : f2Row (mulK (code g) (code g)) C S (code v :: Cv) =
      bA (eqL (filterL C (fun y => commK y (code v))) Cv)
        (allL S (f2W (mulK (code g) (code g)) (code v) Cv)) := rfl
  rw [hr', bA_iff, eqL_iff, allL_iff] at hr
  obtain ⟨hCv, hW⟩ := hr
  have hw := hW _ (memS w hwu hw2)
  rw [f2W, bI_iff] at hw
  have hvwv : Nat.beq (mulK (mulK (code v) (code w)) (code v)) (code w) = true := by
    rw [beq_iff, ← code_mul, ← code_mul, code_eq_iff]
    exact keq_conj_inv_iff.mp hwv
  have hy := allL_iff.mp (hw hvwv) (code y) (by
    rw [← hCv, mem_filterL]
    exact ⟨memC y hyu, commK_code.mpr hyv⟩)
  rw [bI_iff] at hy
  have hs := hy (commK_code.mpr hyw)
  rw [sqOK, bO_iff, beq_iff, beq_iff, ← code_mul, ← code_mul, ← code_one, code_eq_iff,
    code_eq_iff] at hs
  rcases hs with hs | hs
  · exact hy1 hs
  · exact hy2 hs

theorem f3B_sound {a : Nat} {L : List Nat} (h : f3B a L = true) (q : Q8)
    (hq : code (mkE 1 1 q) = a) : ∀ v w : Model, IsInvM v → IsInvM w →
      KEq (v * mkE 1 1 q) (mkE 1 1 q * v) → KEq (w * mkE 1 1 q) (mkE 1 1 q * w) →
      ¬ KEq v w → KEq (v * w) (w * v) → InZ v ∨ InZ w ∨ InZ (v * w) := by
  subst hq
  intro v w hv hw hva hwa hvw hc
  unfold f3B at h
  rw [bA_iff, eqL_iff, f3L, allL_iff] at h
  obtain ⟨hL, h3⟩ := h
  have memL' : ∀ x : Model, IsInvM x → KEq (x * mkE 1 1 q) (mkE 1 1 q * x) → code x ∈ L :=
    fun x hx hxa => by
      rw [← hL, mem_filterR]
      obtain ⟨t, ht, hxt⟩ := exists_rep x
      refine ⟨t, ht, hxt.symm, ?_⟩
      rw [← hxt, p3, bA_iff, bA_iff, bN_iff, beq_iff, mulK_code_self_eq_zero, commK_code,
        Bool.eq_false_iff, Ne, beq_iff, code_eq_zero]
      exact ⟨hx.1, hx.2, hxa⟩
  have h4 := allL_iff.mp (h3 _ (memL' v hv hva)) _ (memL' w hw hwa)
  rw [bO_iff, bO_iff, bO_iff, bO_iff, beq_iff, code_eq_iff, bN_iff, ← code_mul, inZK_code,
    inZK_code, inZK_code] at h4
  rcases h4 with h4 | h4 | h4 | h4 | h4
  · exact absurd h4 hvw
  · rw [← Bool.not_eq_true, commK_code] at h4
    exact absurd hc h4
  · exact Or.inl h4
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr h4)

theorem r3c_code : ∀ i, i < 8 → r3c i = code (mkE 1 1 (qd i)) := by
  decide +kernel

theorem r3c_qc (q : Q8) : r3c (qc q) = code (mkE 1 1 q) := by
  revert q
  decide +kernel

theorem zs4_codes : (zs4 ()).map code = zs4K := by
  decide +kernel

theorem code_z3M : code z3M = 18 := by
  decide +kernel

theorem code_shiftRight (g : Model) : Nat.shiftRight (code g) 9 = ec g.right := by
  rw [code, (nz_facts _ (rawc_lt g)).2.2.1, (rawc_lanes g).2.2.2.2.1]

theorem f4B_sound {W : List Nat} (h : f4B W = true) : F4Fact := by
  intro n h1 h2 h3
  unfold f4B at h
  rw [bA_iff, allR_iff, allL_iff] at h
  obtain ⟨hD, hW⟩ := h
  obtain ⟨t, ht, hn⟩ := exists_rep n
  have hdom : domK (code n) = true := by
    rw [domK, bA_iff, bA_iff, bN_iff, bO_iff, beq_iff, ← code_mul, code_of_keq h1, code_z3M]
    refine ⟨rfl, ?_, ?_⟩
    · rw [Bool.eq_false_iff, Ne, anyN_iff]
      rintro ⟨i, hi, hc⟩
      rw [beq_iff, r3c_code i hi, code_eq_iff] at hc
      exact h2 _ hc
    · rcases zmod2' n.right with hr | hr
      · obtain ⟨q, z, hz, hk⟩ := h3 hr
        refine Or.inr (anyN_iff.mpr ⟨qc q, qc_lt q, anyL_iff.mpr ⟨code z, ?_, ?_⟩⟩)
        · rw [← zs4_codes]
          exact List.mem_map_of_mem hz
        · rw [beq_iff, r3c_qc, ← code_mul, code_eq_iff]
          exact hk
      · left
        rw [beq_iff, code_shiftRight, hr]
        rfl
  have hm := hD t ht
  rw [bI_iff, ← hn] at hm
  obtain ⟨x, hx, hxn⟩ := mem_lowL.mp (memL_iff.mp (hm hdom))
  have hwx := hW x hx
  rw [witK, hxn] at hwx
  simp only [bA_iff, bN_iff, invNZ] at hwx
  obtain ⟨-, hvn, hwn, ⟨hvC, hvv, hv0, hvZ⟩, ⟨hwC, hww, hw0, hwZ⟩, hne, hvw, hvwZ⟩ := hwx
  refine ⟨dec (Nat.land (Nat.shiftRight x 10) 1023), dec (Nat.shiftRight x 20), ?_⟩
  have hV := code_dec_of_isC hvC
  have hW' := code_dec_of_isC hwC
  rw [← hV] at hvn hvv hv0 hvZ
  rw [← hW'] at hwn hww hw0 hwZ
  rw [← hV, ← hW'] at hne hvw hvwZ
  rw [commK_code] at hvn hwn hvw
  rw [beq_iff, mulK_code_self_eq_zero] at hvv hww
  rw [Bool.eq_false_iff, Ne, beq_iff, code_eq_zero] at hv0 hw0
  rw [Bool.eq_false_iff, Ne, beq_iff, code_eq_iff] at hne
  rw [Bool.eq_false_iff, Ne, inZK_code] at hvZ hwZ
  rw [← code_mul, Bool.eq_false_iff, Ne, inZK_code] at hvwZ
  exact ⟨hvn, hwn, ⟨hvv, hv0⟩, ⟨hww, hw0⟩, hne, hvw, hvZ, hwZ, hvwZ⟩

end Certificates.FzJt.K
