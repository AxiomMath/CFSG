module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Check
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coh

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def toMat4 (A : Array (Array ℕ)) : Matrix (Fin 6) (Fin 6) (ZMod 4) :=
  Matrix.of fun i j => (m4Get A i j : ZMod 4)

@[expose] def toVec4 (v : Array ℕ) : Fin 6 → ZMod 4 := fun j => (v.getD j 0 : ZMod 4)

theorem m4Get_ofFn (f : Fin 6 → Fin 6 → ℕ) (i j : Fin 6) :
    m4Get (Array.ofFn fun i => Array.ofFn fun j => f i j) i j = f i j := by
  simp [m4Get]

theorem toMat4_mul4 (A B : Array (Array ℕ)) : toMat4 (mul4 A B) = toMat4 A * toMat4 B := by
  ext i j
  simp only [toMat4, mul4, m4Get_ofFn, of_apply, mul_apply, ZMod.natCast_mod, Nat.cast_sum,
    Nat.cast_mul]

theorem toMat4_add4 (A B : Array (Array ℕ)) : toMat4 (add4 A B) = toMat4 A + toMat4 B := by
  ext i j
  simp only [toMat4, add4, m4Get_ofFn, of_apply, Matrix.add_apply, ZMod.natCast_mod, Nat.cast_add]

theorem toMat4_sub4 (A B : Array (Array ℕ)) : toMat4 (sub4 A B) = toMat4 A - toMat4 B := by
  ext i j
  simp only [toMat4, sub4, m4Get_ofFn, of_apply, Matrix.sub_apply, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_mul]
  have : ((3 : ℕ) : ZMod 4) = -1 := by decide
  rw [this, neg_one_mul, ← sub_eq_add_neg]

theorem toMat4_one4 : toMat4 one4 = 1 := by
  ext i j
  simp only [toMat4, one4, m4Get_ofFn, of_apply, one_apply, Fin.val_eq_val]
  split_ifs <;> simp

theorem toVec4_mv4 (A : Array (Array ℕ)) (v : Array ℕ) :
    toVec4 (mv4 A v) = toMat4 A *ᵥ toVec4 v := by
  ext i
  simp [toVec4, mv4, toMat4, mulVec, dotProduct, ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul]

@[expose] def lift4 (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 4) :=
  M.map fun x => (x.val : ZMod 4)

theorem toMat4_lift2 (M : Array ℕ) : toMat4 (lift2 M) = lift4 (toMat 6 6 M) := by
  ext i j
  simp only [toMat4, lift2, m4Get_ofFn, of_apply, lift4, map_apply, toMat_apply]
  cases (M.getD i 0).testBit j <;> rfl

@[expose] def red4 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

theorem red4_val (x : ZMod 2) : red4 (x.val : ZMod 4) = x := by
  revert x; decide

theorem two_mul_red4 (y : ZMod 4) : 2 * y = 2 * ((red4 y).val : ZMod 4) := by
  revert y; decide

theorem map_red4_lift4 (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : (lift4 M).map red4 = M := by
  ext i j
  simp [lift4]

theorem two_smul_eq_lift4 (N : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    (2 : ZMod 4) • N = (2 : ZMod 4) • lift4 (N.map red4) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, lift4, map_apply]
  exact two_mul_red4 _

theorem two_smul_lift4_add (X Y : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (2 : ZMod 4) • lift4 (X + Y) = (2 : ZMod 4) • lift4 X + (2 : ZMod 4) • lift4 Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, lift4, map_apply, Matrix.add_apply]
  generalize X i j = x
  generalize Y i j = y
  revert x y; decide

theorem two_smul_lift4_eq_zero {X : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h : (2 : ZMod 4) • lift4 X = 0) : X = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul, lift4, map_apply, Matrix.zero_apply] at this ⊢
  generalize X i j = x at this ⊢
  revert x; decide

theorem two_smul_two_smul (N : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    (2 : ZMod 4) • ((2 : ZMod 4) • N) = 0 := by
  rw [smul_smul, show (2 : ZMod 4) * 2 = 0 by decide, zero_smul]

@[expose] def liftW (ε : Eps) (C : ℕ → Mat6) (s : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 4) :=
  lift4 (genMat ε s) + (2 : ZMod 4) • lift4 (C s)

@[expose] def prodW (ε : Eps) (C : ℕ → Mat6) (w : List ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 4) :=
  (w.map (liftW ε C)).prod

variable (ε : Eps)

theorem prodW_nil (C : ℕ → Mat6) : prodW ε C [] = 1 := rfl

theorem prodW_cons (C : ℕ → Mat6) (s : ℕ) (w : List ℕ) :
    prodW ε C (s :: w) = liftW ε C s * prodW ε C w := by
  simp [prodW]

theorem map_red4_liftW (C : ℕ → Mat6) (s : ℕ) : (liftW ε C s).map red4 = genMat ε s := by
  ext i j
  simp only [liftW, map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul, lift4]
  rw [red4_val, show red4 2 = 0 by decide, zero_mul, add_zero]

theorem map_red4_prodW (C : ℕ → Mat6) (w : List ℕ) :
    (prodW ε C w).map red4 = (urMat6 ε C w).1 := by
  induction w with
  | nil => simp [prodW_nil, urMat6]
  | cons s w ih => rw [prodW_cons, Matrix.map_mul, map_red4_liftW, ih, urMat6]

theorem expand_two (a b b' P R : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    (a + (2 : ZMod 4) • b) * P - (a + (2 : ZMod 4) • b') * (P - (2 : ZMod 4) • R) =
      (2 : ZMod 4) • (a * R) + (2 : ZMod 4) • ((b - b') * P) := by
  rw [add_mul, add_mul, mul_sub, mul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show (2 : ZMod 4) * 2 = 0 by decide, zero_smul, sub_zero, sub_mul, smul_sub]
  generalize a * P = x
  generalize (2 : ZMod 4) • (a * R) = y
  generalize (2 : ZMod 4) • (b * P) = z
  generalize (2 : ZMod 4) • (b' * P) = z'
  abel

theorem prodW_sub (C C' : ℕ → Mat6) (w : List ℕ) :
    prodW ε C w - prodW ε C' w = (2 : ZMod 4) • lift4 ((urMat6 ε (C - C') w).2) := by
  induction w with
  | nil => simp [prodW_nil, urMat6, lift4]
  | cons s w ih =>
    have hP' : prodW ε C' w = prodW ε C w -
        (2 : ZMod 4) • lift4 ((urMat6 ε (C - C') w).2) := by rw [← ih]; abel
    have e1 : prodW ε C (s :: w) - prodW ε C' (s :: w) =
        (2 : ZMod 4) • (lift4 (genMat ε s) * lift4 ((urMat6 ε (C - C') w).2)) +
          (2 : ZMod 4) • ((lift4 (C s) - lift4 (C' s)) * prodW ε C w) := by
      rw [prodW_cons, prodW_cons, liftW, liftW, hP']
      exact expand_two _ _ _ _ _
    rw [e1, two_smul_eq_lift4 (lift4 (genMat ε s) * _),
      two_smul_eq_lift4 ((lift4 (C s) - lift4 (C' s)) * prodW ε C w), ← two_smul_lift4_add]
    congr 2
    rw [Matrix.map_mul, Matrix.map_mul, map_red4_lift4, map_red4_lift4,
      Matrix.map_sub _ (map_sub red4), map_red4_lift4, map_red4_lift4, map_red4_prodW, urMat6,
      urMat6_fst ε C (C - C') w, Pi.sub_apply]
    rfl

theorem urMat6_fst_eq (C : ℕ → Mat6) (w : List ℕ) :
    (urMat6 ε C w).1 = toMat 6 6 (wordRows ε w) := by
  induction w with
  | nil => exact toMat_id6'.symm
  | cons s w ih => rw [urMat6, ih, wordRows, toMat_bmul, genMat]

@[expose] def c0Mat (s : ℕ) : Mat6 := toMat 6 6 (c0Rows ε s)

theorem toMat4_ptil4 (s : ℕ) : toMat4 (ptil4 ε s) = liftW ε (c0Mat ε) s := by
  rw [ptil4, toMat4_add4, toMat4_add4, toMat4_lift2, toMat4_lift2, liftW, genMat, c0Mat,
    two_smul]

theorem toMat4_prod4 (w : List ℕ) : toMat4 (prod4 ε w) = prodW ε (c0Mat ε) w := by
  induction w with
  | nil => exact toMat4_one4
  | cons s w ih => rw [prod4, toMat4_mul4, toMat4_ptil4, ih, prodW_cons]

@[expose] def kTil : Matrix (Fin 6) (Fin 6) (ZMod 4) := toMat4 kTil4

theorem kTil_eq : kTil = prodW .minus (c0Mat .minus) kWord := toMat4_prod4 .minus kWord

theorem ofFn_mod_eq {f g : Fin 6 → ℕ}
    (h : ∀ j, (f j : ZMod 4) = (g j : ZMod 4)) :
    (Array.ofFn (n := 6) fun j => f j % 4) = Array.ofFn fun j => g j % 4 := by
  congr 1
  funext j
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 (h j)

@[expose] def enc4 (x : Fin 6 → ZMod 4) : ℕ := ∑ j : Fin 6, (x j).val * 4 ^ (j : ℕ)

theorem enc4_lt (x : Fin 6 → ZMod 4) : enc4 x < 4096 := by
  have h : ∀ j, (x j).val < 4 := fun j => ZMod.val_lt _
  simp only [enc4, Fin.sum_univ_six]
  have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at *
  norm_num
  omega

theorem toVec4_dig4_enc4 (x : Fin 6 → ZMod 4) : toVec4 (dig4 (enc4 x)) = x := by
  ext j
  have h : ∀ j, (x j).val < 4 := fun j => ZMod.val_lt _
  have hd : enc4 x / 4 ^ (j : ℕ) % 4 = (x j).val := by
    simp only [enc4, Fin.sum_univ_six]
    have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5
    fin_cases j <;> simp <;> omega
  simp [toVec4, dig4, hd]

theorem toVec4_ofFn_mod (f : Fin 6 → ℕ) (j : Fin 6) :
    toVec4 (Array.ofFn (n := 6) fun j => f j % 4) j = (f j : ZMod 4) := by
  simp [toVec4, ZMod.natCast_mod]

theorem eq_of_toVec4_eq {f g : Fin 6 → ℕ}
    (h : toVec4 (Array.ofFn (n := 6) fun j => f j % 4) =
      toVec4 (Array.ofFn (n := 6) fun j => g j % 4)) :
    (Array.ofFn (n := 6) fun j => f j % 4) = Array.ofFn fun j => g j % 4 :=
  ofFn_mod_eq fun j => by
    have := congrFun h j
    rwa [toVec4_ofFn_mod, toVec4_ofFn_mod] at this

theorem prodW_c0_rel {w : List ℕ} (hw : w ∈ extRels ε) : prodW ε (c0Mat ε) w = 1 := by
  have h := relCheck4_spec ε
  simp only [relCheck4, List.all_eq_true, beq_iff_eq] at h
  rw [← toMat4_prod4, h w hw, toMat4_one4]

theorem wordRows_kWord : wordRows .minus kWord = kRows := by
  have h := kCheck_spec
  simp only [kCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem kRows_sq :
    toMat 6 6 kRows * toMat 6 6 kRows = toMat 6 6 (s0Get .minus (zIdx .minus)) := by
  have h := kCheck_spec
  simp only [kCheck, Bool.and_eq_true, beq_iff_eq] at h
  rw [← toMat_bmul, h.2]

theorem exists_sqrt (x : Fin 6 → ZMod 4) (hx : (1 + kTil * kTil) *ᵥ x = 0) :
    ∃ v, (1 + kTil) *ᵥ v = x ∨ (1 - kTil) *ᵥ v = x := by
  have h := sqCheck_spec
  simp only [sqCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at h
  obtain ⟨hwit, hcov⟩ := h
  have hK3 : toMat4 (add4 one4 (mul4 kTil4 kTil4)) = 1 + kTil * kTil := by
    rw [toMat4_add4, toMat4_one4, toMat4_mul4]; rfl
  have hx' : mv4 (add4 one4 (mul4 kTil4 kTil4)) (dig4 (enc4 x)) = dig4 0 := by
    refine eq_of_toVec4_eq ?_
    change toVec4 (mv4 _ _) = toVec4 (dig4 0)
    rw [toVec4_mv4, hK3, toVec4_dig4_enc4, hx]
    ext j
    simp [toVec4, dig4]
  rcases hcov (enc4 x) (enc4_lt x) with h0 | ⟨e, he, hen⟩
  · exact absurd hx' (by simpa using h0)
  · refine ⟨toVec4 (dig4 e.2.1), ?_⟩
    have hw := hwit e he
    have hv := congrArg toVec4 hw
    rw [toVec4_mv4, hen, toVec4_dig4_enc4] at hv
    cases hb : e.2.2
    · right
      rw [hb, ite_eq_right (by simp), toMat4_sub4, toMat4_one4] at hv
      exact hv
    · left
      rw [hb, ite_eq_left rfl, toMat4_add4, toMat4_one4] at hv
      exact hv

end CFSG.EvenSmallLie.OmegaEight.Chain
