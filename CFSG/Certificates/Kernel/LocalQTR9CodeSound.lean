module

public import Certificates.Data.Kernel.LocalQT.R9C
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33DataInputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.LQT.R

open CFSG.QuasithinUnique.Unc25K1 CFSG.KC.Ord

theorem forall_lt_20 {p : ℕ → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3) (h4 : p 4)
    (h5 : p 5) (h6 : p 6) (h7 : p 7) (h8 : p 8) (h9 : p 9) (h10 : p 10) (h11 : p 11) (h12 : p 12)
    (h13 : p 13) (h14 : p 14) (h15 : p 15) (h16 : p 16) (h17 : p 17) (h18 : p 18) (h19 : p 19) :
    ∀ c < 20, p c := by
  intro c hc
  interval_cases c <;> assumption

@[expose] def codeR (x : R9) : ℕ :=
  x.a.val + x.b.val * 4 + x.c.val * 16 + x.d.val * 64 + x.e.val * 256 + x.f.val * 1024 +
    x.g.val * 4096 + x.h.val * 16384 + x.i.val * 65536

theorem mem_rawList (r : R9) : r ∈ rawList ↔ rdet r = 1 := by
  have hv : ∀ x : ZMod 3, x ∈ vals := by decide
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := r
  simp only [rawList, rawAll, List.mem_filter, List.mem_flatMap, List.mem_map, beq_iff_eq]
  exact ⟨fun hm => hm.2, fun hd => ⟨⟨a, hv a, b, hv b, c, hv c, d, hv d, e, hv e, f, hv f, g, hv g,
    h, hv h, i, hv i, rfl⟩, hd⟩⟩

theorem ent_eq (x k : ℕ) : ent x k = x / 4 ^ k % 4 := by
  change (x >>> (2 * k)) &&& (2 ^ 2 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem shl2_eq (v k : ℕ) : Nat.shiftLeft v (Nat.mul 2 k) = v * 4 ^ k := by
  change v <<< (2 * k) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  rfl

theorem mk9_eq (g : ℕ → ℕ) : mk9 g = g 0 + g 1 * 4 + g 2 * 16 + g 3 * 64 + g 4 * 256 +
    g 5 * 1024 + g 6 * 4096 + g 7 * 16384 + g 8 * 65536 := by
  rw [mk9, P.rec_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, shl2_eq]
  ring

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem codeR_eq (x : R9) : codeR x = x.a.val + x.b.val * 4 + x.c.val * 16 + x.d.val * 64 +
    x.e.val * 256 + x.f.val * 1024 + x.g.val * 4096 + x.h.val * 16384 + x.i.val * 65536 := rfl

theorem codeR_digits (x : R9) :
    ent (codeR x) 0 = x.a.val ∧ ent (codeR x) 1 = x.b.val ∧ ent (codeR x) 2 = x.c.val ∧
    ent (codeR x) 3 = x.d.val ∧ ent (codeR x) 4 = x.e.val ∧ ent (codeR x) 5 = x.f.val ∧
    ent (codeR x) 6 = x.g.val ∧ ent (codeR x) 7 = x.h.val ∧ ent (codeR x) 8 = x.i.val := by
  have := ZMod.val_lt x.a
  have := ZMod.val_lt x.b
  have := ZMod.val_lt x.c
  have := ZMod.val_lt x.d
  have := ZMod.val_lt x.e
  have := ZMod.val_lt x.f
  have := ZMod.val_lt x.g
  have := ZMod.val_lt x.h
  have := ZMod.val_lt x.i
  simp only [ent_eq, codeR_eq, Nat.reducePow, Nat.div_one]
  omega

theorem ent0 (x : R9) : ent (codeR x) 0 = x.a.val := (codeR_digits x).1
theorem ent1 (x : R9) : ent (codeR x) 1 = x.b.val := (codeR_digits x).2.1
theorem ent2 (x : R9) : ent (codeR x) 2 = x.c.val := (codeR_digits x).2.2.1
theorem ent3 (x : R9) : ent (codeR x) 3 = x.d.val := (codeR_digits x).2.2.2.1
theorem ent4 (x : R9) : ent (codeR x) 4 = x.e.val := (codeR_digits x).2.2.2.2.1
theorem ent5 (x : R9) : ent (codeR x) 5 = x.f.val := (codeR_digits x).2.2.2.2.2.1
theorem ent6 (x : R9) : ent (codeR x) 6 = x.g.val := (codeR_digits x).2.2.2.2.2.2.1
theorem ent7 (x : R9) : ent (codeR x) 7 = x.h.val := (codeR_digits x).2.2.2.2.2.2.2.1
theorem ent8 (x : R9) : ent (codeR x) 8 = x.i.val := (codeR_digits x).2.2.2.2.2.2.2.2

theorem codeR_inj {x y : R9} (h : codeR x = codeR y) : x = y := by
  have hx := codeR_digits x
  have hy := codeR_digits y
  rw [h] at hx
  obtain ⟨a, b, c, d, e, f, g, h', i⟩ := x
  obtain ⟨a', b', c', d', e', f', g', h'', i'⟩ := y
  simp only at hx hy
  simp only [R9.mk.injEq]
  refine ⟨ZMod.val_injective 3 ?_, ZMod.val_injective 3 ?_, ZMod.val_injective 3 ?_,
    ZMod.val_injective 3 ?_, ZMod.val_injective 3 ?_, ZMod.val_injective 3 ?_,
    ZMod.val_injective 3 ?_, ZMod.val_injective 3 ?_, ZMod.val_injective 3 ?_⟩ <;> omega

theorem codeR_eq_iff {x y : R9} : codeR x = codeR y ↔ x = y :=
  ⟨codeR_inj, fun h => h ▸ rfl⟩

theorem beq_codeR (x y : R9) : Nat.beq (codeR x) (codeR y) = true ↔ x = y := by
  rw [P.beq_iff, codeR_eq_iff]

theorem val_of {a : ZMod 3} {m : ℕ} (h : (m : ZMod 3) = a) : m % 3 = a.val := by
  rw [← h, ZMod.val_natCast]

theorem mulK_eq (x y : ℕ) : mulK x y =
    (ent x 0 * ent y 0 + ent x 1 * ent y 3 + ent x 2 * ent y 6) % 3 +
    (ent x 0 * ent y 1 + ent x 1 * ent y 4 + ent x 2 * ent y 7) % 3 * 4 +
    (ent x 0 * ent y 2 + ent x 1 * ent y 5 + ent x 2 * ent y 8) % 3 * 16 +
    (ent x 3 * ent y 0 + ent x 4 * ent y 3 + ent x 5 * ent y 6) % 3 * 64 +
    (ent x 3 * ent y 1 + ent x 4 * ent y 4 + ent x 5 * ent y 7) % 3 * 256 +
    (ent x 3 * ent y 2 + ent x 4 * ent y 5 + ent x 5 * ent y 8) % 3 * 1024 +
    (ent x 6 * ent y 0 + ent x 7 * ent y 3 + ent x 8 * ent y 6) % 3 * 4096 +
    (ent x 6 * ent y 1 + ent x 7 * ent y 4 + ent x 8 * ent y 7) % 3 * 16384 +
    (ent x 6 * ent y 2 + ent x 7 * ent y 5 + ent x 8 * ent y 8) % 3 * 65536 := by
  rw [mulK, mk9_eq]
  rfl

theorem v3 (a b c d e f : ZMod 3) :
    (a.val * d.val + b.val * e.val + c.val * f.val) % 3 = (a * d + b * e + c * f).val :=
  val_of (by push_cast [ZMod.natCast_zmod_val]; ring)

theorem mulK_codeR (x y : R9) : mulK (codeR x) (codeR y) = codeR (rmul x y) := by
  rw [mulK_eq]
  simp only [ent0, ent1, ent2, ent3, ent4, ent5, ent6, ent7, ent8, v3]
  rfl

theorem minor_eq (x p q r s : ℕ) :
    minor x p q r s = (ent x p * ent x q + 2 * (ent x r * ent x s)) % 3 := rfl

theorem cofK_eq (x : ℕ) : cofK x = minor x 4 8 5 7 + minor x 5 6 3 8 * 4 +
    minor x 3 7 4 6 * 16 + minor x 2 7 1 8 * 64 + minor x 0 8 2 6 * 256 +
    minor x 1 6 0 7 * 1024 + minor x 1 5 2 4 * 4096 + minor x 2 3 0 5 * 16384 +
    minor x 0 4 1 3 * 65536 := by
  rw [cofK, mk9_eq]
  rfl

theorem three_eq : (3 : ZMod 3) = 0 := by decide

theorem m3 (a b c d : ZMod 3) : (a.val * b.val + 2 * (c.val * d.val)) % 3 = (a * b - c * d).val :=
  val_of (by
    push_cast [ZMod.natCast_zmod_val]
    linear_combination (c * d) * three_eq)

theorem cofK_codeR (x : R9) : cofK (codeR x) = codeR (rcof x) := by
  rw [cofK_eq]
  simp only [minor_eq, ent0, ent1, ent2, ent3, ent4, ent5, ent6, ent7, ent8, m3]
  rfl

theorem detK_eq (x : ℕ) : detK x = (ent x 0 * (ent x 4 * ent x 8) + ent x 1 * (ent x 5 * ent x 6) +
    ent x 2 * (ent x 3 * ent x 7) + 2 * (ent x 0 * (ent x 5 * ent x 7) +
    ent x 1 * (ent x 3 * ent x 8) + ent x 2 * (ent x 4 * ent x 6))) % 3 := rfl

theorem detK_codeR (x : R9) : detK (codeR x) = (rdet x).val := by
  rw [detK_eq]
  simp only [ent0, ent1, ent2, ent3, ent4, ent5, ent6, ent7, ent8]
  refine val_of ?_
  push_cast [ZMod.natCast_zmod_val]
  rw [rdet]
  linear_combination (x.a * x.f * x.h + x.b * x.d * x.i + x.c * x.e * x.g) * three_eq

theorem oneK_eq : oneK = codeR rone := by
  rw [codeR_eq]
  rfl

open CFSG.QuasithinUnique.Unc25L33 in
theorem pwK_codeR (x : R9) (n : ℕ) : pwK (codeR x) n = codeR (rpw x n) := by
  induction n with
  | zero => exact oneK_eq
  | succ n ih =>
    change mulK (codeR x) (pwK (codeR x) n) = _
    rw [ih, mulK_codeR]
    rfl

theorem commK_codeR (x y : R9) : commK (codeR x) (codeR y) = true ↔ rmul x y = rmul y x := by
  rw [commK, mulK_codeR, mulK_codeR, beq_codeR]

theorem invoK_codeR (x : R9) : invoK (codeR x) = true ↔ x ≠ rone ∧ rmul x x = rone := by
  rw [invoK, P.andB_iff, P.notB_iff, oneK_eq, beq_codeR, mulK_codeR, beq_codeR]

theorem allLL_iff (l : List (List ℕ)) (f : List ℕ → Bool) :
    allLL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allLL]
  | cons x l ih =>
    change andB (f x) (allLL l f) = true ↔ _
    rw [P.andB_iff, ih]
    simp

theorem anyLL_iff (l : List (List ℕ)) (f : List ℕ → Bool) :
    anyLL l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => simp [anyLL]
  | cons x l ih =>
    change orB (f x) (anyLL l f) = true ↔ _
    rw [P.orB_iff, ih]
    simp

theorem allL_mapR (L : List R9) (f : ℕ → Bool) :
    P.allL (L.map codeR) f = true ↔ ∀ x ∈ L, f (codeR x) = true := by
  rw [P.allL_iff]
  simp

theorem anyL_mapR (L : List R9) (f : ℕ → Bool) :
    P.anyL (L.map codeR) f = true ↔ ∃ x ∈ L, f (codeR x) = true := by
  rw [P.anyL_iff]
  simp

theorem mem_mapR (L : List R9) (x : R9) : codeR x ∈ L.map codeR ↔ x ∈ L := by
  simp only [List.mem_map, codeR_eq_iff, exists_eq_right]

theorem ofIdx_eq (n : ℕ) : ofIdx n = n / 1 % 3 + n / 3 % 3 * 4 + n / 9 % 3 * 16 +
    n / 27 % 3 * 64 + n / 81 % 3 * 256 + n / 243 % 3 * 1024 + n / 729 % 3 * 4096 +
    n / 2187 % 3 * 16384 + n / 6561 % 3 * 65536 := by
  rw [ofIdx, mk9_eq]
  rfl

def idxR (x : R9) : ℕ := x.a.val + x.b.val * 3 + x.c.val * 9 + x.d.val * 27 + x.e.val * 81 +
  x.f.val * 243 + x.g.val * 729 + x.h.val * 2187 + x.i.val * 6561

theorem idxR_spec (x : R9) : idxR x < 19683 ∧ ofIdx (idxR x) = codeR x := by
  have := ZMod.val_lt x.a
  have := ZMod.val_lt x.b
  have := ZMod.val_lt x.c
  have := ZMod.val_lt x.d
  have := ZMod.val_lt x.e
  have := ZMod.val_lt x.f
  have := ZMod.val_lt x.g
  have := ZMod.val_lt x.h
  have := ZMod.val_lt x.i
  refine ⟨by rw [idxR]; omega, ?_⟩
  have e0 : idxR x / 1 % 3 = x.a.val := by rw [idxR]; omega
  have e1 : idxR x / 3 % 3 = x.b.val := by rw [idxR]; omega
  have e2 : idxR x / 9 % 3 = x.c.val := by rw [idxR]; omega
  have e3 : idxR x / 27 % 3 = x.d.val := by rw [idxR]; omega
  have e4 : idxR x / 81 % 3 = x.e.val := by rw [idxR]; omega
  have e5 : idxR x / 243 % 3 = x.f.val := by rw [idxR]; omega
  have e6 : idxR x / 729 % 3 = x.g.val := by rw [idxR]; omega
  have e7 : idxR x / 2187 % 3 = x.h.val := by rw [idxR]; omega
  have e8 : idxR x / 6561 % 3 = x.i.val := by rw [idxR]; omega
  rw [ofIdx_eq, codeR_eq, e0, e1, e2, e3, e4, e5, e6, e7, e8]

theorem allSLc_sound {f : ℕ → Bool} (hs : ∀ c < 20, allSLc c f = true) (x : R9)
    (hx : rdet x = 1) : f (codeR x) = true := by
  obtain ⟨hlt, hof⟩ := idxR_spec x
  have h := hs (idxR x / 1024) (by omega)
  rw [allSLc, P.allN_iff] at h
  have h2 := h (idxR x % 1024) (Nat.mod_lt _ (by norm_num))
  rw [P.letB_eq, P.impB_iff, P.blt_iff] at h2
  have e : Nat.add (Nat.mul 1024 (idxR x / 1024)) (idxR x % 1024) = idxR x := by
    change 1024 * (idxR x / 1024) + idxR x % 1024 = _
    omega
  rw [e] at h2
  have h3 := h2 hlt
  rw [P.letB_eq, P.impB_iff, hof, P.beq_iff, detK_codeR, hx] at h3
  exact h3 rfl

theorem exists_of_slOK {n : ℕ} (h : slOK n = true) : ∃ x : R9, codeR x = n ∧ rdet x = 1 := by
  rw [slOK, P.andB_iff, P.andB_iff, P.blt_iff, P.allN_iff, P.beq_iff] at h
  obtain ⟨hn, he, hd⟩ := h
  have he' : ∀ k < 9, ent n k < 3 := fun k hk => P.blt_iff.1 (he k hk)
  let x : R9 := ⟨(ent n 0 : ZMod 3), (ent n 1 : ZMod 3), (ent n 2 : ZMod 3), (ent n 3 : ZMod 3),
    (ent n 4 : ZMod 3), (ent n 5 : ZMod 3), (ent n 6 : ZMod 3), (ent n 7 : ZMod 3),
    (ent n 8 : ZMod 3)⟩
  have hx : codeR x = n := by
    have h0 := he' 0 (by norm_num)
    have h1 := he' 1 (by norm_num)
    have h2 := he' 2 (by norm_num)
    have h3 := he' 3 (by norm_num)
    have h4 := he' 4 (by norm_num)
    have h5 := he' 5 (by norm_num)
    have h6 := he' 6 (by norm_num)
    have h7 := he' 7 (by norm_num)
    have h8 := he' 8 (by norm_num)
    rw [codeR_eq]
    simp only [x, ZMod.val_natCast, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5, Nat.mod_eq_of_lt h6,
      Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt h8]
    simp only [ent_eq, Nat.reducePow, Nat.div_one] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    omega
  refine ⟨x, hx, ?_⟩
  rw [← hx, detK_codeR] at hd
  exact ZMod.val_injective 3 (hd.trans (by decide))

end CFSG.KC.LQT.R

end
