module

public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.Universal.Spin QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank

abbrev ι8 : Type := Fin 4 ⊕ Fin 4

abbrev V8 : Type := ι8 → ZMod 2

@[expose] def nb (f : Fin 4 → ZMod 2) : ℕ := ∑ i : Fin 4, (f i).val * 2 ^ (i : ℕ)

@[expose] def bvN (c : ℕ) : Fin 4 → ZMod 2 := fun i => if c.testBit (i : ℕ) then 1 else 0

@[expose] def bc (v : V8) : ℕ := nb (fun i => v (Sum.inl i)) + 16 * nb (fun i => v (Sum.inr i))

@[expose] def bv (c : ℕ) : V8 := Sum.elim (bvN (c % 16)) (bvN (c / 16 % 16))

theorem nb_lt : ∀ f : Fin 4 → ZMod 2, nb f < 16 := by decide +kernel

theorem bvN_nb : ∀ f : Fin 4 → ZMod 2, bvN (nb f) = f := by decide +kernel

theorem nb_bvN : ∀ c < 16, nb (bvN c) = c := by decide +kernel

theorem bc_lt (v : V8) : bc v < 256 := by
  have h1 := nb_lt (fun i => v (Sum.inl i))
  have h2 := nb_lt (fun i => v (Sum.inr i))
  unfold bc
  omega

theorem bv_bc (v : V8) : bv (bc v) = v := by
  have h1 := nb_lt (fun i => v (Sum.inl i))
  have h2 := nb_lt (fun i => v (Sum.inr i))
  have e1 : bc v % 16 = nb (fun i => v (Sum.inl i)) := by unfold bc; omega
  have e2 : bc v / 16 % 16 = nb (fun i => v (Sum.inr i)) := by unfold bc; omega
  unfold bv
  rw [e1, e2, bvN_nb, bvN_nb]
  funext x
  rcases x with x | x <;> rfl

theorem bc_bv {c : ℕ} (hc : c < 256) : bc (bv c) = c := by
  have h1 : nb (bvN (c % 16)) = c % 16 := nb_bvN _ (Nat.mod_lt _ (by norm_num))
  have h2 : nb (bvN (c / 16 % 16)) = c / 16 % 16 := nb_bvN _ (Nat.mod_lt _ (by norm_num))
  have : bc (bv c) = nb (bvN (c % 16)) + 16 * nb (bvN (c / 16 % 16)) := rfl
  rw [this, h1, h2]
  omega

theorem bc_injective {v w : V8} (h : bc v = bc w) : v = w := by
  rw [← bv_bc v, h, bv_bc w]

@[expose] def addB (a b : ℕ) : ℕ := ((a % 16) ^^^ (b % 16)) + 16 * ((a / 16 % 16) ^^^ (b / 16 % 16))

theorem nb_add : ∀ f g : Fin 4 → ZMod 2, nb (f + g) = nb f ^^^ nb g := by decide +kernel

theorem bc_add (v w : V8) : bc (v + w) = addB (bc v) (bc w) := by
  have h1 := nb_lt (fun i => v (Sum.inl i))
  have h2 := nb_lt (fun i => v (Sum.inr i))
  have h3 := nb_lt (fun i => w (Sum.inl i))
  have h4 := nb_lt (fun i => w (Sum.inr i))
  have e1 : bc v % 16 = nb (fun i => v (Sum.inl i)) := by unfold bc; omega
  have e2 : bc v / 16 % 16 = nb (fun i => v (Sum.inr i)) := by unfold bc; omega
  have e3 : bc w % 16 = nb (fun i => w (Sum.inl i)) := by unfold bc; omega
  have e4 : bc w / 16 % 16 = nb (fun i => w (Sum.inr i)) := by unfold bc; omega
  unfold addB
  rw [e1, e2, e3, e4]
  unfold bc
  rw [← nb_add, ← nb_add]
  rfl

theorem bc_zero : bc (0 : V8) = 0 := by
  have : (0 : V8) = bv 0 := by
    funext x
    rcases x with x | x <;> simp [bv, bvN]
  rw [this]
  exact bc_bv (by norm_num)

theorem addB_lt (a b : ℕ) : addB a b < 256 := by
  unfold addB
  have h1 : (a % 16) ^^^ (b % 16) < 16 := Nat.xor_lt_two_pow (n := 4) (by omega) (by omega)
  have h2 : (a / 16 % 16) ^^^ (b / 16 % 16) < 16 :=
    Nat.xor_lt_two_pow (n := 4) (by omega) (by omega)
  omega

@[expose] def dotN (a b : ℕ) : ℕ :=
  let x := a &&& b
  let y := x ^^^ (x >>> 2)
  (y ^^^ (y >>> 1)) &&& 1

@[expose] def Qb (c : ℕ) : ℕ := dotN (c % 16) (c / 16 % 16)

@[expose] def Bb (a b : ℕ) : ℕ :=
  (dotN (a % 16) (b / 16 % 16) + dotN (b % 16) (a / 16 % 16)) % 2

theorem dot_nb : ∀ f g : Fin 4 → ZMod 2, ∑ i, f i * g i = (dotN (nb f) (nb g) : ZMod 2) := by
  decide +kernel

theorem quad_bc (v : V8) : StatedQuadPlus 4 (ZMod 2) v = (Qb (bc v) : ZMod 2) := by
  have h1 := nb_lt (fun i => v (Sum.inl i))
  have h2 := nb_lt (fun i => v (Sum.inr i))
  have e1 : bc v % 16 = nb (fun i => v (Sum.inl i)) := by unfold bc; omega
  have e2 : bc v / 16 % 16 = nb (fun i => v (Sum.inr i)) := by unfold bc; omega
  unfold Qb
  rw [e1, e2, ← dot_nb]
  rfl

section Polar

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem polar_bc (v w : V8) :
    polar (quadPlus 4 (ZMod 2)) v w = (Bb (bc v) (bc w) : ZMod 2) := by
  have h1 := nb_lt (fun i => v (Sum.inl i))
  have h2 := nb_lt (fun i => v (Sum.inr i))
  have h3 := nb_lt (fun i => w (Sum.inl i))
  have h4 := nb_lt (fun i => w (Sum.inr i))
  have e1 : bc v % 16 = nb (fun i => v (Sum.inl i)) := by unfold bc; omega
  have e2 : bc v / 16 % 16 = nb (fun i => v (Sum.inr i)) := by unfold bc; omega
  have e3 : bc w % 16 = nb (fun i => w (Sum.inl i)) := by unfold bc; omega
  have e4 : bc w / 16 % 16 = nb (fun i => w (Sum.inr i)) := by unfold bc; omega
  rw [polar_quadPlus]
  unfold Bb
  rw [e1, e2, e3, e4, ZMod.natCast_mod, Nat.cast_add, ← dot_nb, ← dot_nb, Finset.sum_add_distrib]

end Polar

theorem dotN_lt (a b : ℕ) : dotN a b < 2 := by
  unfold dotN
  have : ∀ z : ℕ, z &&& 1 < 2 := fun z => by
    rw [Nat.and_one_is_mod]
    omega
  exact this _

theorem Qb_lt (c : ℕ) : Qb c < 2 := dotN_lt _ _

theorem Bb_lt (a b : ℕ) : Bb a b < 2 := by
  unfold Bb
  omega

theorem cast2_eq_zero_iff (n : ℕ) : (n : ZMod 2) = 0 ↔ n % 2 = 0 := by
  rw [← ZMod.natCast_mod n 2]
  constructor
  · intro h
    have h2 : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases hn : n % 2
    · rfl
    · exact absurd h (by decide)
  · intro h
    rw [h]
    rfl

theorem bc_smul (a : ZMod 2) (w : V8) : bc (a • w) = if a = 0 then 0 else bc w := by
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · simp [bc_zero]
  · simp

theorem sub_eq_add_V8 (a b : V8) : a - b = a + b := by
  funext i
  exact CharTwo.sub_eq_add _ _

@[expose] def eAct (u w c : ℕ) : ℕ :=
  if Qb u = 0 ∧ Bb u w = 0 then
    addB (addB c (if Bb c u = 1 then w else 0))
      (if (Bb c w + Qb w * Bb c u) % 2 = 1 then u else 0)
  else c

section Eichler

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem quad_quadPlus (v : V8) : quadPlus 4 (ZMod 2) v = (Qb (bc v) : ZMod 2) := by
  rw [quadPlus_apply]
  exact quad_bc v

theorem ite_cast (n t : ℕ) :
    (if (n : ZMod 2) = 0 then 0 else t) = if n % 2 = 1 then t else 0 := by
  by_cases h : n % 2 = 0
  · have : ¬ n % 2 = 1 := by omega
    simp [(cast2_eq_zero_iff n).2 h, this]
  · have : n % 2 = 1 := by omega
    have h2 : ¬ (n : ZMod 2) = 0 := fun h' => h ((cast2_eq_zero_iff n).1 h')
    simp [h2, this]

theorem bc_eichler (u w x : V8) :
    bc (eichler (quadPlus 4 (ZMod 2)) u w x) = eAct (bc u) (bc w) (bc x) := by
  have hQ := quad_quadPlus u
  have hP := polar_bc u w
  by_cases h : quadPlus 4 (ZMod 2) u = 0 ∧ polar (quadPlus 4 (ZMod 2)) u w = 0
  · have h1 : Qb (bc u) = 0 ∧ Bb (bc u) (bc w) = 0 := by
      rw [hQ, hP, cast2_eq_zero_iff, cast2_eq_zero_iff] at h
      have := Qb_lt (bc u)
      have := Bb_lt (bc u) (bc w)
      omega
    rw [eichler_apply h.1 h.2 x, sub_eq_add_V8, bc_add, bc_add, bc_smul, bc_smul, polar_bc x u,
      polar_bc x w, quad_quadPlus w]
    unfold eAct
    simp only [h1.1, h1.2, and_self, ↓reduceIte]
    have ha := Bb_lt (bc x) (bc u)
    have e1 : ((if Bb (bc x) (bc u) = 1 then bc w else 0) : ℕ) =
        if Bb (bc x) (bc u) % 2 = 1 then bc w else 0 := by
      rw [Nat.mod_eq_of_lt ha]
    have e2 : (((Bb (bc x) (bc w) : ℕ) : ZMod 2) + (Qb (bc w) : ZMod 2) *
        (Bb (bc x) (bc u) : ZMod 2)) =
        ((Bb (bc x) (bc w) + Qb (bc w) * Bb (bc x) (bc u) : ℕ) : ZMod 2) := by
      push_cast
      rfl
    rw [e1, e2, ite_cast, ite_cast]
  · have h1 : ¬(Qb (bc u) = 0 ∧ Bb (bc u) (bc w) = 0) := by
      intro h1
      apply h
      rw [hQ, hP, cast2_eq_zero_iff, cast2_eq_zero_iff]
      have := Qb_lt (bc u)
      have := Bb_lt (bc u) (bc w)
      omega
    rw [eichler_of_not h]
    unfold eAct
    simp only [h1, ↓reduceIte]
    rfl

@[expose] def actG (g : GL ι8 (ZMod 2)) (c : ℕ) : ℕ := bc ((g : Matrix ι8 ι8 (ZMod 2)) *ᵥ bv c)

theorem actG_lt (g : GL ι8 (ZMod 2)) (c : ℕ) : actG g c < 256 := bc_lt _

theorem actG_mul (g h : GL ι8 (ZMod 2)) (c : ℕ) : actG (g * h) c = actG g (actG h c) := by
  unfold actG
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, bv_bc]

theorem actG_one {c : ℕ} (hc : c < 256) : actG 1 c = c := by
  unfold actG
  rw [Units.val_one, Matrix.one_mulVec, bc_bv hc]

theorem gl_ext_act {g h : GL ι8 (ZMod 2)} (H : ∀ c < 256, actG g c = actG h c) : g = h := by
  have key : ∀ v : V8, (g : Matrix ι8 ι8 (ZMod 2)) *ᵥ v = (h : Matrix ι8 ι8 (ZMod 2)) *ᵥ v := by
    intro v
    have := H (bc v) (bc_lt v)
    unfold actG at this
    rw [bv_bc] at this
    exact bc_injective this
  apply Units.ext
  exact Matrix.ext_of_mulVec_single fun i => key _

@[expose] noncomputable def eichGL (u w : V8) : GL ι8 (ZMod 2) :=
  (toLinEquiv ι8 (ZMod 2)).symm (eichler (quadPlus 4 (ZMod 2)) u w)

theorem eichGL_mulVec (u w x : V8) :
    (eichGL u w : Matrix ι8 ι8 (ZMod 2)) *ᵥ x = eichler (quadPlus 4 (ZMod 2)) u w x := by
  rw [← toLinEquiv_apply]
  unfold eichGL
  rw [MulEquiv.apply_symm_apply]

theorem actG_eichGL (u w : V8) {c : ℕ} (hc : c < 256) :
    actG (eichGL u w) c = eAct (bc u) (bc w) c := by
  unfold actG
  rw [eichGL_mulVec, bc_eichler, bc_bv hc]

theorem bv_zero : bv 0 = (0 : V8) := by
  funext x
  rcases x with x | x <;> simp [bv, bvN]

theorem actG_zero (g : GL ι8 (ZMod 2)) : actG g 0 = 0 := by
  unfold actG
  rw [bv_zero, Matrix.mulVec_zero, bc_zero]

theorem bv_addB {a b : ℕ} (ha : a < 256) (hb : b < 256) : bv (addB a b) = bv a + bv b := by
  apply bc_injective
  rw [bc_bv (addB_lt a b), bc_add, bc_bv ha, bc_bv hb]

theorem actG_addB (g : GL ι8 (ZMod 2)) {a b : ℕ} (ha : a < 256) (hb : b < 256) :
    actG g (addB a b) = addB (actG g a) (actG g b) := by
  unfold actG
  rw [bv_addB ha hb, Matrix.mulVec_add, bc_add]

theorem addB_two_pow : ∀ m < 8, ∀ a < 2 ^ m, addB a (2 ^ m) = a + 2 ^ m := by decide +kernel

@[expose] def colsB (g : GL ι8 (ZMod 2)) : List ℕ := (List.range 8).map fun j => actG g (2 ^ j)

@[expose] def applyB (cols : List ℕ) (c : ℕ) : ℕ :=
  (List.range 8).foldl (fun acc j => if c.testBit j then addB acc (cols.getD j 0) else acc) 0

theorem foldl_applyB (g : GL ι8 (ZMod 2)) (c : ℕ) :
    ∀ m ≤ 8, (List.range m).foldl (fun acc j =>
      if c.testBit j then addB acc ((colsB g).getD j 0) else acc) 0 = actG g (c % 2 ^ m)
  | 0, _ => by
    rw [List.range_zero, List.foldl_nil, pow_zero, Nat.mod_one]
    exact (actG_zero g).symm
  | m + 1, hm => by
    have hm' : m < 8 := hm
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_applyB g c m hm'.le]
    have hcol : (colsB g).getD m 0 = actG g (2 ^ m) := by
      simp [colsB, List.getD_eq_getElem?_getD, hm']
    have hlt : c % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
    have hp8 : 2 ^ m < 256 := by
      calc 2 ^ m < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hm'
        _ = 256 := by norm_num
    have hlt256 : c % 2 ^ m < 256 := by omega
    rw [Nat.mod_pow_succ]
    by_cases hb : c.testBit m = true
    · have hdiv : c / 2 ^ m % 2 = 1 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at hb
        simpa using hb
      rw [hdiv, mul_one]
      simp only [hb, ↓reduceIte]
      rw [hcol, ← addB_two_pow m hm' _ hlt, actG_addB g hlt256 hp8]
    · have hdiv : c / 2 ^ m % 2 = 0 := by
        rw [Bool.not_eq_true] at hb
        rw [Nat.testBit_eq_decide_div_mod_eq] at hb
        simp only [decide_eq_false_iff_not] at hb
        omega
      rw [hdiv, mul_zero, add_zero]
      simp only [hb, Bool.false_eq_true, ↓reduceIte]

theorem actG_eq_applyB (g : GL ι8 (ZMod 2)) {c : ℕ} (hc : c < 256) :
    actG g c = applyB (colsB g) c := by
  unfold applyB
  rw [foldl_applyB g c 8 le_rfl]
  congr 1
  rw [show (2 : ℕ) ^ 8 = 256 by norm_num, Nat.mod_eq_of_lt hc]

end Eichler

end CFSG.AGLEmbedding
