module

public import CFSG.Certificates.Kernel.Co1Sub.LutSound
public import CFSG.Certificates.Kernel.Co1Sub.OrbitSound
import CFSG.Certificates.Kernel.Co1DceLemmas

public section

namespace CFSG.KC.Co1Sub

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.TabMatGrp

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by
  cases a <;> rfl

@[expose] def lowB (b : Nat) : Nat := b - (b &&& (b - 1))

theorem lowB_spec : ∀ b : Nat, b ≠ 0 → ∃ t, b.testBit t = true ∧ lowB b = 2 ^ t := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb
    rcases Nat.mod_two_eq_zero_or_one b with h | h
    · obtain ⟨t, ht, e⟩ := ih (b / 2) (by omega) (by omega)
      have hxy : b &&& (b - 1) = 2 * (b / 2 &&& (b / 2 - 1)) := by
        apply Nat.eq_of_testBit_eq
        intro j
        cases j with
        | zero =>
          rw [Nat.testBit_and]
          simp [Nat.testBit_zero, h]
        | succ j =>
          have e1 : (b - 1) / 2 = b / 2 - 1 := by omega
          have e2 : 2 * (b / 2 &&& (b / 2 - 1)) / 2 = b / 2 &&& (b / 2 - 1) := by omega
          rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, e1, e2,
            Nat.testBit_and]
      have hle : b / 2 &&& (b / 2 - 1) ≤ b / 2 := Nat.and_le_left
      refine ⟨t + 1, by rw [Nat.testBit_succ]; exact ht, ?_⟩
      unfold lowB at e ⊢
      rw [hxy, Nat.pow_succ]
      omega
    · have hxy : b &&& (b - 1) = b - 1 := by
        apply Nat.eq_of_testBit_eq
        intro j
        cases j with
        | zero =>
          have : (b - 1) % 2 = 0 := by omega
          rw [Nat.testBit_and]
          simp [Nat.testBit_zero, h, this]
        | succ j =>
          have e1 : (b - 1) / 2 = b / 2 := by omega
          rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, e1, Bool.and_self]
      refine ⟨0, by simp [Nat.testBit_zero, h], ?_⟩
      unfold lowB
      rw [hxy, Nat.pow_zero]
      omega

@[expose] def hitB (b v : Nat) : Bool := decide (v &&& lowB b ≠ 0)

theorem land_two_pow (x t : Nat) : decide (x &&& 2 ^ t ≠ 0) = x.testBit t := by
  have e : x &&& 2 ^ t = if x.testBit t then 2 ^ t else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hi : t = i
    · subst hi
      cases x.testBit t <;> simp [Nat.testBit_two_pow]
    · split <;> simp [hi, Nat.testBit_two_pow]
  rw [e]
  cases x.testBit t <;> simp

theorem hitB_spec {b : Nat} (hb : b ≠ 0) : ∃ t, b.testBit t = true ∧ ∀ x, hitB b x = x.testBit t := by
  obtain ⟨t, ht, e⟩ := lowB_spec b hb
  exact ⟨t, ht, fun x => by rw [hitB, e, land_two_pow]⟩

theorem hitB_xor (b v w : Nat) : hitB b (v ^^^ w) = (hitB b v ^^ hitB b w) := by
  by_cases hb : b = 0
  · subst hb
    simp [hitB, lowB]
  · obtain ⟨t, -, e⟩ := hitB_spec hb
    rw [e, e, e, Nat.testBit_xor]

theorem redK_eq (b v : Nat) : redK b v = v ^^^ cond (hitB b v) b 0 := by
  unfold redK
  change Bool.rec (motive := fun _ => Nat) (v ^^^ b) v (Nat.beq (v &&& lowB b) 0) = _
  cases h : Nat.beq (v &&& lowB b) 0
  · have h' : v &&& lowB b ≠ 0 := Nat.ne_of_beq_eq_false h
    simp [hitB, h']
  · have h' : v &&& lowB b = 0 := Nat.eq_of_beq_eq_true h
    simp [hitB, h']

theorem testBit_cond (e : Bool) (x j : Nat) : (cond e x 0).testBit j = (e && x.testBit j) := by
  cases e <;> simp

theorem redK_xor (b v w : Nat) : redK b (v ^^^ w) = redK b v ^^^ redK b w := by
  rw [redK_eq, redK_eq, redK_eq, hitB_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, testBit_cond]
  generalize hitB b v = x
  generalize hitB b w = y
  generalize v.testBit i = p
  generalize w.testBit i = q
  generalize b.testBit i = r
  revert x y p q r
  decide

theorem redK_self (b : Nat) : redK b b = 0 := by
  by_cases hb : b = 0
  · subst hb
    rfl
  · obtain ⟨t, ht, e⟩ := hitB_spec hb
    rw [redK_eq, e, ht]
    exact Nat.xor_self b

theorem redK_zero (b : Nat) : redK b 0 = 0 := by
  rw [redK_eq]
  simp [hitB]

theorem redK_cond (b x : Nat) (e : Bool) : redK b (cond e x 0) = cond e (redK b x) 0 := by
  cases e
  · exact redK_zero b
  · rfl

@[expose] noncomputable def key4R (r0 r1 r2 r3 : Nat) : Nat :=
  Nat.lor (Nat.lor r0 (Nat.shiftLeft (redK r0 r1) 24))
    (Nat.lor (Nat.shiftLeft (redK (redK r0 r1) (redK r0 r2)) 48)
      (Nat.shiftLeft (redK (redK (redK r0 r1) (redK r0 r2)) (redK (redK r0 r1) (redK r0 r3))) 72))

theorem key4_eq_R (Q : Nat) : key4 Q = key4R (fget Q 0 24) (fget Q 1 24) (fget Q 2 24) (fget Q 3 24) := by
  unfold key4
  simp only [strictN_eq]
  try rfl

@[expose] def toZ (b : Bool) : ZMod 2 := if b = true then 1 else 0

theorem toZ_inj {a b : Bool} (h : toZ a = toZ b) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem toZ_xor (a b : Bool) : toZ (a ^^ b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_decide (x : ZMod 2) : toZ (decide (x = 1)) = x := by
  revert x
  decide

theorem testBit_fget24 (X i j : Nat) :
    (fget X i 24).testBit j = (decide (j < 24) && X.testBit (i * 24 + j)) := by
  unfold fget maskN pw2
  change ((X >>> (i * 24)) &&& ((1 <<< 24) - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem low_apply {L : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hL : Low L) {i l : Fin 24}
    (h : i.val ≤ l.val) : L i l = (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) i l := by
  have := hL i l (by omega)
  rw [Matrix.sub_apply, sub_eq_zero] at this
  exact this

theorem mul_apply_low {L : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hL : Low L)
    (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) (i j : Fin 24) :
    (L * M) i j = M i j + ∑ l ∈ Finset.univ.filter (· < i), L i l * M l j := by
  rw [Matrix.mul_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < i), add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem i (by simp)]
  · rw [low_apply hL le_rfl, Matrix.one_apply_eq, one_mul]
  · intro l hl hli
    have hl' : ¬ l < i := (Finset.mem_filter.1 hl).2
    have hil : i.val < l.val := by
      have : l ≠ i := hli
      have := Fin.val_ne_of_ne this
      have := Fin.not_lt.1 hl'
      omega
    rw [low_apply hL hil.le, Matrix.one_apply_ne (Fin.ne_of_lt hil), zero_mul]

theorem fget_low {L : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hL : Low L) {Q Q' : Nat}
    (h : MatP 24 Q' = L * MatP 24 Q) (i : Fin 24) (ls : List (Fin 24))
    (hls : Finset.univ.filter (· < i) = ls.toFinset) (hnd : ls.Nodup) :
    fget Q' i 24 = ls.foldl (fun acc l => acc ^^^ cond (decide (L i l = 1)) (fget Q l 24) 0)
      (fget Q i 24) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have key : ∀ (ls : List (Fin 24)) (acc : Nat),
      toZ ((ls.foldl (fun acc l => acc ^^^ cond (decide (L i l = 1)) (fget Q l 24) 0)
        acc).testBit j) =
      toZ (acc.testBit j) + (ls.map fun l => L i l * toZ ((fget Q l 24).testBit j)).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons l ls ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, Nat.testBit_xor, testBit_cond, toZ_xor, toZ_and, toZ_decide, add_assoc]
  apply toZ_inj
  rw [key]
  by_cases hj : j < 24
  · have e2 : ∀ l : Fin 24, toZ ((fget Q l 24).testBit j) = MatP 24 Q l ⟨j, hj⟩ := fun l => by
      rw [testBit_fget24, decide_eq_true hj, Bool.true_and, MatP_apply]
      rfl
    have e3 : ∀ X : Nat, toZ ((fget X i 24).testBit j) = MatP 24 X i ⟨j, hj⟩ := fun X => by
      rw [testBit_fget24, decide_eq_true hj, Bool.true_and, MatP_apply]
      rfl
    simp only [e2]
    rw [e3 Q', h, mul_apply_low hL, hls, List.sum_toFinset _ hnd]
  · rw [testBit_fget24, testBit_fget24, decide_eq_false hj, Bool.false_and, Bool.false_and]
    have : ∀ l : Fin 24, L i l * toZ ((fget Q l 24).testBit j) = 0 := fun l => by
      rw [testBit_fget24, decide_eq_false hj, Bool.false_and]
      simp [toZ]
    have hz : (ls.map fun l => L i l * toZ ((fget Q l 24).testBit j)) =
        ls.map fun _ => (0 : ZMod 2) := List.map_congr_left fun l _ => this l
    rw [hz]
    simp

theorem key4_mul {L : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hL : Low L) {Q Q' : Nat}
    (h : MatP 24 Q' = L * MatP 24 Q) : key4 Q' = key4 Q := by
  have e0 : fget Q' 0 24 = fget Q 0 24 := fget_low hL h 0 [] (by decide) List.nodup_nil
  have e1 : fget Q' 1 24 = fget Q 1 24 ^^^ cond (decide (L 1 0 = 1)) (fget Q 0 24) 0 :=
    fget_low hL h 1 [0] (by decide) (by decide)
  have e2 : fget Q' 2 24 = fget Q 2 24 ^^^ cond (decide (L 2 0 = 1)) (fget Q 0 24) 0 ^^^
      cond (decide (L 2 1 = 1)) (fget Q 1 24) 0 :=
    fget_low hL h 2 [0, 1] (by decide) (by decide)
  have e3 : fget Q' 3 24 = fget Q 3 24 ^^^ cond (decide (L 3 0 = 1)) (fget Q 0 24) 0 ^^^
      cond (decide (L 3 1 = 1)) (fget Q 1 24) 0 ^^^ cond (decide (L 3 2 = 1)) (fget Q 2 24) 0 :=
    fget_low hL h 3 [0, 1, 2] (by decide) (by decide)
  rw [key4_eq_R, key4_eq_R, e0, e1, e2, e3]
  simp only [key4R, redK_xor, redK_cond, redK_self, Bool.cond_self, Nat.xor_zero]

@[expose] def LowRel (Q Q' : Matrix (Fin 24) (Fin 24) (ZMod 2)) : Prop := ∃ L, Low L ∧ Q = L * Q'

section LowRel

variable {M Q Q' Q'' X : Matrix (Fin 24) (Fin 24) (ZMod 2)}

theorem Low_npow (h : Low M) : ∀ n : Nat, Low (M ^ n)
  | 0 => by rw [pow_zero]; exact Low_one
  | n + 1 => by rw [pow_succ]; exact Low_mul (Low_npow h n) h

theorem Low_inv (h : Low M) : Low M⁻¹ ∧ M⁻¹ * M = 1 := by
  have h32 := Low_pow h
  rw [(by norm_num : (32 : ℕ) = 31 + 1)] at h32
  have e : M * M ^ 31 = 1 := by rw [← pow_succ', h32]
  have hi : M⁻¹ = M ^ 31 := Matrix.inv_eq_right_inv e
  refine ⟨by rw [hi]; exact Low_npow h 31, ?_⟩
  rw [hi, ← pow_succ, h32]

theorem LowRel.refl (Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) : LowRel Q Q :=
  ⟨1, Low_one, (one_mul Q).symm⟩

theorem LowRel.symm (h : LowRel Q Q') : LowRel Q' Q := by
  obtain ⟨L, hL, e⟩ := h
  refine ⟨L⁻¹, (Low_inv hL).1, ?_⟩
  rw [e, ← mul_assoc, (Low_inv hL).2, one_mul]

theorem LowRel.trans (h : LowRel Q Q') (h' : LowRel Q' Q'') : LowRel Q Q'' := by
  obtain ⟨L, hL, e⟩ := h
  obtain ⟨L', hL', e'⟩ := h'
  exact ⟨L * L', Low_mul hL hL', by rw [e, e', mul_assoc]⟩

theorem LowRel.mul_right (h : LowRel Q Q') (X : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    LowRel (Q * X) (Q' * X) := by
  obtain ⟨L, hL, e⟩ := h
  exact ⟨L, hL, by rw [e, mul_assoc]⟩

theorem setOf_lowRel (h : LowRel Q Q') : {X | LowRel X Q} = {X | LowRel X Q'} :=
  Set.ext fun _ => ⟨fun hx => hx.trans h, fun hx => hx.trans h.symm⟩

end LowRel

@[expose] def lowU : Subgroup (GL (Fin 24) (ZMod 2)) where
  carrier := {u | Low (u : Matrix (Fin 24) (Fin 24) (ZMod 2))}
  one_mem' := Low_one
  mul_mem' {a b} ha hb := by
    change Low ((a * b : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2))
    rw [Units.val_mul]
    exact Low_mul ha hb
  inv_mem' {a} ha := by
    change Low ((a⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2))
    rw [Matrix.coe_units_inv]
    exact (Low_inv ha).1

variable {G : Type*} [Group G]

@[expose] def flagStab (φ : G →* GL (Fin 24) (ZMod 2)) (B : GL (Fin 24) (ZMod 2)) : Subgroup G :=
  lowU.comap ((MulAut.conj B).toMonoidHom.comp φ)

variable {φ : G →* GL (Fin 24) (ZMod 2)}

theorem mem_flagStab {B : GL (Fin 24) (ZMod 2)} {g : G} :
    g ∈ flagStab φ B ↔ Low ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ g *
      ((B⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2))) := by
  change Low ((B * φ g * B⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) ↔ _
  rw [Units.val_mul, Units.val_mul]

theorem pow32_of_flagStab (hφ : Function.Injective φ) {B : GL (Fin 24) (ZMod 2)} {g : G}
    (hg : g ∈ flagStab φ B) : g ^ 32 = 1 := by
  have hm : (MulAut.conj B).toMonoidHom.comp φ (g ^ 32) = 1 := by
    rw [map_pow]
    have hl : Low (((MulAut.conj B).toMonoidHom.comp φ g : GL (Fin 24) (ZMod 2)) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) := hg
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Low_pow hl, Units.val_one])
  have hc : B * φ (g ^ 32) * B⁻¹ = 1 := hm
  have hm' : φ (g ^ 32) = 1 := by
    calc φ (g ^ 32) = B⁻¹ * (B * φ (g ^ 32) * B⁻¹) * B := by group
      _ = 1 := by rw [hc, mul_one, inv_mul_cancel]
  exact hφ (by rw [hm', map_one])

theorem flagAt_full {gens : List Nat} {P0 : Nat} {P Pi R : List Nat}
    (h : flagK gens P0 P Pi R = true) {k : Nat} (hk : k < P.length) :
    mulS (P.getD k 0) (Pi.getD k 0) = oneS ∧
    (∀ t < gens.length, imgF (R.getD k 0) t < P.length ∧
      lutK (mulS (mulS (P.getD k 0) (gens.getD t 0)) (Pi.getD (imgF (R.getD k 0) t) 0)) = true) ∧
    (k + 1 < P.length → key4 (P.getD k 0) < key4 (P.getD (k + 1) 0)) ∧
    (depF (R.getD k 0) = 0 → P.getD k 0 = P0) ∧
    (depF (R.getD k 0) ≠ 0 → parF (R.getD k 0) < P.length ∧ genF (R.getD k 0) < gens.length ∧
      depF (R.getD (parF (R.getD k 0)) 0) + 1 = depF (R.getD k 0) ∧
      imgF (R.getD (parF (R.getD k 0)) 0) (genF (R.getD k 0)) = k) := by
  unfold flagK at h
  rw [strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨-, -, h3⟩ := h
  have hN : lenL P ≤ 64 * Nat.succ (Nat.shiftRight (lenL P) 6) := by
    rw [lenL_eq_length, shiftRight_one_eq_six]
    omega
  have hk' := CFSG.Certificates.Co1D.allBelow_spec h3 hN k (by rw [lenL_eq_length]; exact hk)
  unfold flagAt at hk'
  rw [strictB_eq, strictB_eq, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hk'
  obtain ⟨h1, h2, h3, h4⟩ := hk'
  simp only [getL_zero_eq, lenL_eq_length] at h1 h2 h3 h4
  refine ⟨Nat.eq_of_beq_eq_true h1, fun t ht => ?_, fun hk1 => ?_, fun hd => ?_, fun hd => ?_⟩
  · have h2' := (allN_iff' _ _).1 h2 t ht
    rw [strictB_eq, andB_eq, Bool.and_eq_true] at h2'
    exact ⟨Nat.blt_eq.mp h2'.1, h2'.2⟩
  · have hc : Nat.blt (Nat.succ k) P.length = true := Nat.blt_eq.mpr hk1
    rw [hc] at h3
    exact Nat.blt_eq.mp h3
  · have hc : Nat.beq (depF (R.getD k 0)) (nat_lit 0) = true := Nat.beq_eq_true_eq _ _ ▸ hd
    rw [hc] at h4
    exact Nat.eq_of_beq_eq_true h4
  · have hc : Nat.beq (depF (R.getD k 0)) (nat_lit 0) = false := by
      cases h' : Nat.beq (depF (R.getD k 0)) (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') hd
    rw [hc] at h4
    change strictB (parF (R.getD k 0)) _ = true at h4
    rw [strictB_eq, strictB_eq, andB_eq, andB_eq, andB_eq] at h4
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, getL_zero_eq] at h4
    exact ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2⟩

theorem card_le_mul {α : Type*} (H S : Subgroup G) [Finite S] (f : G → α)
    (hf : ∀ h ∈ H, ∀ h' ∈ H, f h = f h' → h * h'⁻¹ ∈ S) {N : ℕ} (p : Fin N → α)
    (hHp : ∀ h ∈ H, ∃ k, f h = p k) (hpH : ∀ k, ∃ h ∈ H, f h = p k) :
    Nat.card H ≤ N * Nat.card S := by
  choose r hrH hr using hpH
  choose κ hκ using fun h : H => hHp h.1 h.2
  let F : H → Fin N × S := fun h =>
    (κ h, ⟨h.1 * (r (κ h))⁻¹, hf _ h.2 _ (hrH _) (by rw [hκ h, hr])⟩)
  have hF : Function.Injective F := by
    intro a b e
    have e1 : κ a = κ b := congrArg Prod.fst e
    have e2 : a.1 * (r (κ a))⁻¹ = b.1 * (r (κ b))⁻¹ := congrArg (fun x : Fin N × S => x.2.1) e
    rw [e1] at e2
    exact Subtype.ext (mul_right_cancel e2)
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at this

section Flag

variable {base : ℕ → G} {gens : List Nat}
  (hg : ∀ i < gens.length, MatP 24 (gens.getD i 0) = matOf φ (base i)) {P0 : Nat}
  {P Pi R : List Nat} (h : flagK gens P0 P Pi R = true) {B : GL (Fin 24) (ZMod 2)}
  (hB : (B : Matrix (Fin 24) (Fin 24) (ZMod 2)) = MatP 24 P0)

include hg h

theorem flag_step {k : Nat} (hk : k < P.length) {t : Nat} (ht : t < gens.length) :
    imgF (R.getD k 0) t < P.length ∧ LowRel (MatP 24 (P.getD k 0) * matOf φ (base t))
      (MatP 24 (P.getD (imgF (R.getD k 0) t) 0)) := by
  obtain ⟨-, hst, -⟩ := flagAt_full h hk
  obtain ⟨hj, hl⟩ := hst t ht
  refine ⟨hj, _, Low_of_lutK hl, ?_⟩
  obtain ⟨hPP, -⟩ := flagAt_full h hj
  have e : MatP 24 (P.getD (imgF (R.getD k 0) t) 0) *
      MatP 24 (Pi.getD (imgF (R.getD k 0) t) 0) = 1 := by
    rw [← MatP_mul, ← mulS_eq, hPP, MatP_oneS]
  have e' := (mul_eq_one_comm (M := Matrix (Fin 24) (Fin 24) (ZMod 2))).mp e
  rw [mulS_eq, MatP_mul, mulS_eq, MatP_mul, ← hg t ht, mul_assoc _ (MatP 24 (Pi.getD _ 0)), e',
    mul_one]

omit hg in
theorem flag_root (hN : 0 < P.length) : ∃ k < P.length, P.getD k 0 = P0 := by
  suffices ∀ d, ∀ k < P.length, depF (R.getD k 0) = d → ∃ k < P.length, P.getD k 0 = P0 from
    this _ 0 hN rfl
  intro d
  induction d with
  | zero => exact fun k hk hd => ⟨k, hk, (flagAt_full h hk).2.2.2.1 hd⟩
  | succ d ih =>
    intro k hk hd
    obtain ⟨hp, -, hdp, -⟩ := (flagAt_full h hk).2.2.2.2 (by omega)
    exact ih _ hp (by omega)

include hB

theorem flag_reach {k : Nat} (hk : k < P.length) :
    ∃ x ∈ Subgroup.closure {g | ∃ i < gens.length, base i = g},
      LowRel (MatP 24 (P.getD k 0)) ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ x) := by
  suffices ∀ d, ∀ k < P.length, depF (R.getD k 0) = d →
      ∃ x ∈ Subgroup.closure {g | ∃ i < gens.length, base i = g},
        LowRel (MatP 24 (P.getD k 0)) ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ x) from
    this _ k hk rfl
  intro d
  induction d with
  | zero =>
    intro k hk hd
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [matOf_one, mul_one, hB, (flagAt_full h hk).2.2.2.1 hd]
    exact LowRel.refl _
  | succ d ih =>
    intro k hk hd
    obtain ⟨hp, ht, hdp, him⟩ := (flagAt_full h hk).2.2.2.2 (by omega)
    obtain ⟨x, hx, hr⟩ := ih _ hp (by omega)
    obtain ⟨-, hs⟩ := flag_step hg h hp ht
    rw [him] at hs
    refine ⟨x * base (genF (R.getD k 0)), Subgroup.mul_mem _ hx
      (Subgroup.subset_closure ⟨_, ht, rfl⟩), ?_⟩
    rw [matOf_mul, ← mul_assoc]
    exact hs.symm.trans (hr.mul_right _)

theorem flag_orbit [Finite G] (hN : 0 < P.length) {x : G}
    (hx : x ∈ Subgroup.closure {g | ∃ i < gens.length, base i = g}) :
    ∃ k < P.length, LowRel ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ x)
      (MatP 24 (P.getD k 0)) := by
  let O : Set G := {y | ∃ k < P.length, LowRel ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
    matOf φ y) (MatP 24 (P.getD k 0))}
  have hstep : ∀ y ∈ O, ∀ t < gens.length, y * base t ∈ O := by
    rintro y ⟨k, hk, hr⟩ t ht
    obtain ⟨hj, hs⟩ := flag_step hg h hk ht
    refine ⟨_, hj, ?_⟩
    rw [matOf_mul, ← mul_assoc]
    exact (hr.mul_right _).trans hs
  have hpow : ∀ y ∈ O, ∀ t < gens.length, ∀ m : ℕ, y * base t ^ m ∈ O := by
    intro y hy t ht m
    induction m with
    | zero => rwa [pow_zero, mul_one]
    | succ m ih =>
      rw [pow_succ, ← mul_assoc]
      exact hstep _ ih t ht
  have hO1 : (1 : G) ∈ O := by
    obtain ⟨k, hk, e⟩ := flag_root h hN
    refine ⟨k, hk, ?_⟩
    rw [matOf_one, mul_one, hB, e]
    exact LowRel.refl _
  change x ∈ O
  induction hx using Subgroup.closure_induction_right with
  | one => exact hO1
  | mul_right y _ z hz hy =>
    obtain ⟨t, ht, rfl⟩ := hz
    exact hstep y hy t ht
  | mul_inv_cancel y _ z hz hy =>
    obtain ⟨t, ht, rfl⟩ := hz
    have hn : 0 < orderOf (base t) := orderOf_pos (base t)
    have e : (base t)⁻¹ = base t ^ (orderOf (base t) - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
    rw [e]
    exact hpow y hy t ht _

omit hg h hB in
theorem lowRel_iff {g : G} : LowRel ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ g)
    (B : Matrix (Fin 24) (Fin 24) (ZMod 2)) ↔ g ∈ flagStab φ B := by
  rw [mem_flagStab]
  constructor
  · rintro ⟨L, hL, e⟩
    rw [e, mul_assoc, Units.mul_inv, mul_one]
    exact hL
  · intro hl
    refine ⟨_, hl, ?_⟩
    rw [mul_assoc _ (((B⁻¹ : GL (Fin 24) (ZMod 2))) : Matrix (Fin 24) (Fin 24) (ZMod 2)),
      Units.inv_mul, mul_one]

theorem card_flag [Finite G] (hN : 0 < P.length) :
    Nat.card (Subgroup.closure {g | ∃ i < gens.length, base i = g}) =
      P.length * Nat.card ↥(Subgroup.closure {g | ∃ i < gens.length, base i = g} ⊓
        flagStab φ B) := by
  set H := Subgroup.closure {g | ∃ i < gens.length, base i = g}
  let f : G → Set (Matrix (Fin 24) (Fin 24) (ZMod 2)) := fun g =>
    {X | LowRel X ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ g)}
  let p : Fin P.length → Set (Matrix (Fin 24) (Fin 24) (ZMod 2)) := fun k =>
    {X | LowRel X (MatP 24 (P.getD k 0))}
  have hpH : ∀ k, ∃ x ∈ H, f x = p k := fun k => by
    obtain ⟨x, hx, hr⟩ := flag_reach hg h hB k.isLt
    exact ⟨x, hx, (setOf_lowRel hr).symm⟩
  apply le_antisymm
  · refine card_le_mul H _ f
      (fun x hx y hy e => Subgroup.mem_inf.2 ⟨H.mul_mem hx (H.inv_mem hy), ?_⟩) p
      (fun x hx => ?_) hpH
    · have hr : LowRel ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ x)
          ((B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ y) := by
        have : (B : Matrix (Fin 24) (Fin 24) (ZMod 2)) * matOf φ x ∈ f x := LowRel.refl _
        rwa [e] at this
      apply lowRel_iff.1
      have := hr.mul_right (matOf φ y⁻¹)
      rwa [mul_assoc, ← matOf_mul, mul_assoc, ← matOf_mul, mul_inv_cancel, matOf_one,
        mul_one] at this
    · obtain ⟨k, hk, hr⟩ := flag_orbit hg h hB hN hx
      exact ⟨⟨k, hk⟩, setOf_lowRel hr⟩
  · refine card_mul_le H _ inf_le_left f (fun s hs x => ?_) p (fun k l e => ?_) hpH
    · apply setOf_lowRel
      have := (lowRel_iff.2 (Subgroup.mem_inf.1 hs).2).mul_right (matOf φ x)
      rwa [mul_assoc, ← matOf_mul] at this
    · have hr : LowRel (MatP 24 (P.getD k 0)) (MatP 24 (P.getD l 0)) := by
        have : MatP 24 (P.getD k 0) ∈ p k := LowRel.refl _
        rwa [e] at this
      obtain ⟨L, hL, hk⟩ := hr
      have ek := key4_mul hL hk
      have hmono : ∀ a b, a < b → b < P.length → key4 (P.getD a 0) < key4 (P.getD b 0) := by
        intro a b hab hb
        obtain ⟨m, rfl⟩ : ∃ m, b = a + 1 + m := ⟨b - (a + 1), by omega⟩
        induction m with
        | zero => exact (flagAt_full h (by omega)).2.2.1 (by omega)
        | succ m ih =>
          exact lt_trans (ih (by omega) (by omega)) ((flagAt_full h (by omega)).2.2.1 (by omega))
      rcases lt_trichotomy k.val l.val with hkl | hkl | hkl
      · exact absurd ek (hmono _ _ hkl l.isLt).ne
      · exact Fin.ext hkl
      · exact absurd ek (hmono _ _ hkl k.isLt).ne'

theorem le_flagStab (h1 : P.length = 1) :
    Subgroup.closure {g | ∃ i < gens.length, base i = g} ≤ flagStab φ B := by
  rw [Subgroup.closure_le]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨k, hk, e⟩ := flag_root h (by omega)
  have hk0 : k = 0 := by omega
  subst hk0
  obtain ⟨hj, hs⟩ := flag_step hg h (k := 0) (by omega) ht
  have hj0 : imgF (R.getD 0 0) t = 0 := by omega
  rw [hj0, e, ← hB] at hs
  exact lowRel_iff.1 hs

end Flag

end CFSG.KC.Co1Sub

end
