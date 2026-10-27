module

public import CFSG.ClassicalInvolution.ModelFacts.D4RigidLinear
public import CFSG.LieType.Universal.Spin.Chevalley.Plus

public section

namespace CFSG.ClassicalInvolution.ModelFacts.D4Rigid

open CFSG.LieType.Universal.Spin QuadraticMap

variable {F : Type} [Field F]

noncomputable abbrev fr (F : Type) [Field F] : HypFrame (quadPlus 4 F) 4 :=
  plusFrame 4 F (by norm_num)

@[expose] def idx (i : Fin 4) (s : Bool) : Idx := if s then .inl i else .inr i

theorem vec_eq (i : Fin 4) (s : Bool) : (fr F).vec i s = Pi.single (idx i s) 1 := by
  cases s <;> rfl

theorem polar_vec (v : Idx → F) (j : Fin 4) (t : Bool) :
    polar (quadPlus 4 F) v ((fr F).vec j t) = v (idx j (!t)) := by
  cases t
  · exact polar_quadPlus_single_inr 4 F v j
  · exact polar_quadPlus_single_inl 4 F v j

theorem spinAction_longRoot_apply {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : F) (v : Idx → F)
    (μ : Idx) :
    spinAction (quadPlus 4 F) ((fr F).longRoot hij s t (.ofAdd c)) v μ =
      v μ + c * v (idx j (!t)) * (if μ = idx i s then 1 else 0) -
        c * v (idx i (!s)) * (if μ = idx j t then 1 else 0) := by
  rw [HypFrame.spinAction_longRoot, polar_vec, polar_vec]
  simp [vec_eq, Pi.single_apply]

@[expose] def lamT (i j : Fin 4) (s t : Bool) (τ τi : F) (μ : Idx) : F :=
  1 + (if μ = idx i s then τ - 1 else 0) + (if μ = idx j t then τ - 1 else 0) +
    (if μ = idx i (!s) then τi - 1 else 0) + (if μ = idx j (!t) then τi - 1 else 0)

theorem spinAction_longTorus_apply {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (τ : Fˣ)
    (v : Idx → F) (μ : Idx) :
    spinAction (quadPlus 4 F) ((fr F).longTorus hij s t τ) v μ =
      lamT i j s t (τ : F) ((τ⁻¹ : Fˣ) : F) μ * v μ := by
  rw [HypFrame.spinAction_longTorus, polar_vec, polar_vec, polar_vec, polar_vec]
  simp only [lamT, vec_eq]
  simp [Pi.single_apply]
  split_ifs <;> subst_vars <;> simp_all <;> ring

theorem ne01 : (0 : Fin 4) ≠ 1 := by decide
theorem ne10 : (1 : Fin 4) ≠ 0 := by decide
theorem ne12 : (1 : Fin 4) ≠ 2 := by decide
theorem ne21 : (2 : Fin 4) ≠ 1 := by decide
theorem ne23 : (2 : Fin 4) ≠ 3 := by decide
theorem ne32 : (3 : Fin 4) ≠ 2 := by decide

@[expose] noncomputable def xr (F : Type) [Field F] (a : F) : spinGroup (quadPlus 4 F) :=
  (fr F).longRoot ne12 true false (.ofAdd a)

@[expose] noncomputable def xn (F : Type) [Field F] (a : F) : spinGroup (quadPlus 4 F) :=
  (fr F).longRoot ne12 false true (.ofAdd a)

@[expose] noncomputable def u0 (F : Type) [Field F] (c : F) : spinGroup (quadPlus 4 F) :=
  (fr F).longRoot ne10 true false (.ofAdd c)

@[expose] noncomputable def u1 (F : Type) [Field F] (c : F) : spinGroup (quadPlus 4 F) :=
  (fr F).longRoot ne01 true true (.ofAdd c)

@[expose] noncomputable def u2 (F : Type) [Field F] (c : F) : spinGroup (quadPlus 4 F) :=
  (fr F).longRoot ne32 true false (.ofAdd c)

@[expose] noncomputable def u3 (F : Type) [Field F] (c : F) : spinGroup (quadPlus 4 F) :=
  (fr F).longRoot ne32 false false (.ofAdd c)

theorem commute_xr_u0 (a c : F) : Commute (xr F a) (u0 F c) :=
  (fr F).commute_longRoot_longRoot_left ne12 ne10 true false false a c

theorem commute_xr_u1 (a c : F) : Commute (xr F a) (u1 F c) := by
  have h : xr F a = (fr F).longRoot ne21 false true (.ofAdd (-a)) := by
    unfold xr
    rw [HypFrame.longRoot_swap]
  rw [h]
  exact ((fr F).commute_longRoot_longRoot_right ne01 ne21 true true false c (-a)).symm

theorem commute_xr_u2 (a c : F) : Commute (xr F a) (u2 F c) :=
  ((fr F).commute_longRoot_longRoot_right ne32 ne12 true false true c a).symm

theorem commute_xr_u3 (a c : F) : Commute (xr F a) (u3 F c) :=
  ((fr F).commute_longRoot_longRoot_right ne32 ne12 false false true c a).symm

theorem xr_add (a b : F) : xr F (a + b) = xr F a * xr F b := by
  unfold xr
  rw [← map_mul, ← ofAdd_add]

theorem xr_zero : xr F 0 = 1 := by
  unfold xr
  rw [ofAdd_zero, map_one]

theorem xr_pow (a : F) (n : ℕ) : xr F a ^ n = xr F (n • a) := by
  unfold xr
  rw [← map_pow, ← ofAdd_nsmul]

theorem xr_pow_char {p : ℕ} [CharP F p] (a : F) : xr F a ^ p = 1 := by
  rw [xr_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, xr_zero]

theorem xn_pow_char {p : ℕ} [CharP F p] (a : F) : xn F a ^ p = 1 := by
  unfold xn
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero, map_one]

theorem coe_spinAction_u0 :
    ⇑(spinAction (quadPlus 4 F) (u0 F 1)) = tvm (.inl 0) (.inl 1) (.inr 1) (.inr 0) := by
  funext v μ
  unfold u0
  rw [spinAction_longRoot_apply]
  simp [tvm, idx]

theorem coe_spinAction_u1 :
    ⇑(spinAction (quadPlus 4 F) (u1 F 1)) = tvm (.inr 1) (.inl 0) (.inr 0) (.inl 1) := by
  funext v μ
  unfold u1
  rw [spinAction_longRoot_apply]
  simp [tvm, idx]

theorem coe_spinAction_u2 :
    ⇑(spinAction (quadPlus 4 F) (u2 F 1)) = tvm (.inl 2) (.inl 3) (.inr 3) (.inr 2) := by
  funext v μ
  unfold u2
  rw [spinAction_longRoot_apply]
  simp [tvm, idx]

theorem coe_spinAction_u3 :
    ⇑(spinAction (quadPlus 4 F) (u3 F 1)) = tvm (.inl 2) (.inr 3) (.inl 3) (.inr 2) := by
  funext v μ
  unfold u3
  rw [spinAction_longRoot_apply]
  simp [tvm, idx]

theorem coe_spinAction_xr (b : F) : ⇑(spinAction (quadPlus 4 F) (xr F b)) = xrm b := by
  funext v μ
  unfold xr
  rw [spinAction_longRoot_apply]
  simp [xrm, idx]

@[expose] noncomputable def Ta (F : Type) [Field F] (c : Fˣ) : spinGroup (quadPlus 4 F) :=
  (fr F).longTorus ne01 true false c * (fr F).longTorus ne01 true true c

@[expose] noncomputable def Tb (F : Type) [Field F] (c : Fˣ) : spinGroup (quadPlus 4 F) :=
  (fr F).longTorus ne23 true false c * (fr F).longTorus ne23 true true c⁻¹

theorem coe_spinAction_Ta (c : Fˣ) :
    ⇑(spinAction (quadPlus 4 F) (Ta F c)) = dg (lamA (c : F)) := by
  funext v μ
  unfold Ta
  rw [map_mul, LinearEquiv.mul_apply, spinAction_longTorus_apply, spinAction_longTorus_apply]
  simp only [dg, lamA]
  rcases μ with i | i <;> fin_cases i <;> simp [lamT, idx] <;> field_simp

theorem coe_spinAction_Tb (c : Fˣ) :
    ⇑(spinAction (quadPlus 4 F) (Tb F c)) = dg (lamB (c : F)) := by
  funext v μ
  unfold Tb
  rw [map_mul, LinearEquiv.mul_apply, spinAction_longTorus_apply, spinAction_longTorus_apply]
  simp only [dg, lamB]
  rcases μ with i | i <;> fin_cases i <;> simp [lamT, idx] <;> field_simp

theorem torus_conj_xr {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (τ : Fˣ) (a : F) :
    (fr F).longTorus hij s t τ * xr F a * ((fr F).longTorus hij s t τ)⁻¹ =
      xr F (((τ ^ (longCoroot i j s t 1 true + longCoroot i j s t 2 false) : Fˣ) : F) * a) :=
  (fr F).longTorus_conj_longRoot hij s t τ ne12 true false a

theorem Ta_conj_xr (c : Fˣ) (a : F) : Ta F c * xr F a * (Ta F c)⁻¹ = xr F a := by
  have e1 : longCoroot (n := 4) 0 1 true false 1 true +
      longCoroot (n := 4) 0 1 true false 2 false = -1 := by
    decide
  have e2 : longCoroot (n := 4) 0 1 true true 1 true +
      longCoroot (n := 4) 0 1 true true 2 false = 1 := by
    decide
  unfold Ta
  calc (fr F).longTorus ne01 true false c * (fr F).longTorus ne01 true true c * xr F a *
        ((fr F).longTorus ne01 true false c * (fr F).longTorus ne01 true true c)⁻¹ =
      (fr F).longTorus ne01 true false c * ((fr F).longTorus ne01 true true c * xr F a *
        ((fr F).longTorus ne01 true true c)⁻¹) * ((fr F).longTorus ne01 true false c)⁻¹ := by
        group
    _ = xr F a := by
      rw [torus_conj_xr, e2, torus_conj_xr, e1]
      simp

theorem Tb_conj_xr (c : Fˣ) (a : F) : Tb F c * xr F a * (Tb F c)⁻¹ = xr F a := by
  have e1 : longCoroot (n := 4) 2 3 true false 1 true +
      longCoroot (n := 4) 2 3 true false 2 false = -1 := by
    decide
  have e2 : longCoroot (n := 4) 2 3 true true 1 true +
      longCoroot (n := 4) 2 3 true true 2 false = -1 := by
    decide
  unfold Tb
  calc (fr F).longTorus ne23 true false c * (fr F).longTorus ne23 true true c⁻¹ * xr F a *
        ((fr F).longTorus ne23 true false c * (fr F).longTorus ne23 true true c⁻¹)⁻¹ =
      (fr F).longTorus ne23 true false c * ((fr F).longTorus ne23 true true c⁻¹ * xr F a *
        ((fr F).longTorus ne23 true true c⁻¹)⁻¹) * ((fr F).longTorus ne23 true false c)⁻¹ := by
        group
    _ = xr F a := by
      rw [torus_conj_xr, e2, torus_conj_xr, e1]
      simp

theorem eq_of_spinAction_eq_of_pow {n p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h2 : (2 : F) ≠ 0)
    {g₁ g₂ : spinGroup (quadPlus n F)}
    (h : spinAction (quadPlus n F) g₁ = spinAction (quadPlus n F) g₂) (h₁ : g₁ ^ p = 1)
    (h₂ : g₂ ^ p = 1) : g₁ = g₂ := by
  have hz : spinAction (quadPlus n F) (g₁ * g₂⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rcases eq_one_or_eq_neg_one_of_spinAction_eq_one n F _ hz with h1 | h1
  · have : g₁ * g₂⁻¹ = 1 := Subtype.ext h1
    exact mul_inv_eq_one.mp this
  · exfalso
    have e : (g₁ : CliffordAlgebra (quadPlus n F)) = -(g₂ : CliffordAlgebra (quadPlus n F)) := by
      calc (g₁ : CliffordAlgebra (quadPlus n F)) = ((g₁ * g₂⁻¹ * g₂ : spinGroup (quadPlus n F)) :
            CliffordAlgebra (quadPlus n F)) := by rw [inv_mul_cancel_right]
        _ = -(g₂ : CliffordAlgebra (quadPlus n F)) := by
          rw [Submonoid.coe_mul, h1, neg_one_mul]
    have hodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
    have h3 : ((g₁ ^ p : spinGroup (quadPlus n F)) : CliffordAlgebra (quadPlus n F)) =
        -((g₂ ^ p : spinGroup (quadPlus n F)) : CliffordAlgebra (quadPlus n F)) := by
      rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, e, hodd.neg_pow]
    rw [h₁, h₂] at h3
    have h4 : (2 : CliffordAlgebra (quadPlus n F)) = 0 := by
      have : (1 : CliffordAlgebra (quadPlus n F)) + 1 = 0 := by
        have := congrArg (· + (1 : CliffordAlgebra (quadPlus n F))) h3
        simpa using this
      simpa [one_add_one_eq_two] using this
    apply h2
    apply algebraMap_injective' (quadPlus n F)
    rw [map_ofNat, h4, map_zero]

structure FixesFrame (β : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F)) : Prop where
  h0 : ∀ M, β ((fr F).longSL2 ne01 true false M) = (fr F).longSL2 ne01 true false M
  h1 : ∀ M, β ((fr F).longSL2 ne01 true true M) = (fr F).longSL2 ne01 true true M
  h2 : ∀ M, β ((fr F).longSL2 ne23 true false M) = (fr F).longSL2 ne23 true false M
  h3 : ∀ M, β ((fr F).longSL2 ne23 true true M) = (fr F).longSL2 ne23 true true M

section Fixes

variable {β : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F)}

theorem FixesFrame.map_u0 (h : FixesFrame β) (c : F) : β (u0 F c) = u0 F c := by
  have e : u0 F c = (fr F).longSL2 ne01 true false (lowerSL2 c) := by
    rw [HypFrame.longSL2_lowerSL2]
    rfl
  rw [e]
  exact h.h0 _

theorem FixesFrame.map_u1 (h : FixesFrame β) (c : F) : β (u1 F c) = u1 F c := by
  have e : u1 F c = (fr F).longSL2 ne01 true true (upperSL2 c) := by
    rw [HypFrame.longSL2_upperSL2]
    rfl
  rw [e]
  exact h.h1 _

theorem FixesFrame.map_u2 (h : FixesFrame β) (c : F) : β (u2 F c) = u2 F c := by
  have e : u2 F c = (fr F).longSL2 ne23 true false (lowerSL2 c) := by
    rw [HypFrame.longSL2_lowerSL2]
    rfl
  rw [e]
  exact h.h2 _

theorem FixesFrame.map_u3 (h : FixesFrame β) (c : F) : β (u3 F c) = u3 F c := by
  have e : u3 F c = (fr F).longSL2 ne23 true true (lowerSL2 c) := by
    rw [HypFrame.longSL2_lowerSL2]
    rfl
  rw [e]
  exact h.h3 _

theorem FixesFrame.map_Ta (h : FixesFrame β) (c : Fˣ) : β (Ta F c) = Ta F c := by
  unfold Ta
  rw [map_mul, (fr F).longTorus_apply, (fr F).longTorus_apply, h.h0, h.h1]

theorem FixesFrame.map_Tb (h : FixesFrame β) (c : Fˣ) : β (Tb F c) = Tb F c := by
  unfold Tb
  rw [map_mul, (fr F).longTorus_apply, (fr F).longTorus_apply, h.h2, h.h3]

theorem FixesFrame.comm_Ta (h : FixesFrame β) (c : Fˣ) (a : F) :
    Commute (β (xr F a)) (Ta F c) := by
  have h1 := congrArg β (Ta_conj_xr c a)
  rw [map_mul, map_mul, map_inv, h.map_Ta] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem FixesFrame.comm_Tb (h : FixesFrame β) (c : Fˣ) (a : F) :
    Commute (β (xr F a)) (Tb F c) := by
  have h1 := congrArg β (Tb_conj_xr c a)
  rw [map_mul, map_mul, map_inv, h.map_Tb] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem FixesFrame.comm_u0 (h : FixesFrame β) (a c : F) : Commute (β (xr F a)) (u0 F c) := by
  have := (commute_xr_u0 a c).map β
  rwa [h.map_u0] at this

theorem FixesFrame.comm_u1 (h : FixesFrame β) (a c : F) : Commute (β (xr F a)) (u1 F c) := by
  have := (commute_xr_u1 a c).map β
  rwa [h.map_u1] at this

theorem FixesFrame.comm_u2 (h : FixesFrame β) (a c : F) : Commute (β (xr F a)) (u2 F c) := by
  have := (commute_xr_u2 a c).map β
  rwa [h.map_u2] at this

theorem FixesFrame.comm_u3 (h : FixesFrame β) (a c : F) : Commute (β (xr F a)) (u3 F c) := by
  have := (commute_xr_u3 a c).map β
  rwa [h.map_u3] at this

theorem spinAction_comm {g u : spinGroup (quadPlus 4 F)} (h : Commute g u) (v : Idx → F) :
    spinAction (quadPlus 4 F) g (spinAction (quadPlus 4 F) u v) =
      spinAction (quadPlus 4 F) u (spinAction (quadPlus 4 F) g v) := by
  rw [← LinearEquiv.mul_apply, ← map_mul, h.eq, map_mul, LinearEquiv.mul_apply]

theorem two_ne_zero_of_charP {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((CharP.cast_eq_zero_iff F p 2).mp h'))

theorem exists_xr_of_fixesFrame {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {c : Fˣ}
    (hc2 : (c : F) ^ 2 ≠ 1) (h : FixesFrame β) (a : F) : ∃ b : F, β (xr F a) = xr F b := by
  have hNp : β (xr F a) ^ p = 1 := by rw [← map_pow, xr_pow_char, map_one]
  obtain ⟨b, hb⟩ := linear_part hp2 hc2 (spinAction (quadPlus 4 F) (β (xr F a)))
    (fun v => map_spinAction _ _ v) (fun v w => polar_spinAction _ _ v w)
    (fun v => by
      have := spinAction_comm (h.comm_u0 a 1) v
      rwa [coe_spinAction_u0] at this)
    (fun v => by
      have := spinAction_comm (h.comm_u1 a 1) v
      rwa [coe_spinAction_u1] at this)
    (fun v => by
      have := spinAction_comm (h.comm_u2 a 1) v
      rwa [coe_spinAction_u2] at this)
    (fun v => by
      have := spinAction_comm (h.comm_u3 a 1) v
      rwa [coe_spinAction_u3] at this)
    (fun v => by
      have := spinAction_comm (h.comm_Ta c a) v
      rwa [coe_spinAction_Ta] at this)
    (fun v => by
      have := spinAction_comm (h.comm_Tb c a) v
      rwa [coe_spinAction_Tb] at this)
    (by rw [← map_pow, hNp, map_one])
  refine ⟨b, eq_of_spinAction_eq_of_pow hp2 (two_ne_zero_of_charP hp2) ?_ hNp (xr_pow_char b)⟩
  refine LinearEquiv.ext fun v => ?_
  rw [hb v, ← coe_spinAction_xr b]

@[expose] noncomputable def W (F : Type) [Field F] : spinGroup (quadPlus 4 F) :=
  (fr F).longWeyl ne01 true false * (fr F).longWeyl ne01 true true *
    (fr F).longWeyl ne23 true false * (fr F).longWeyl ne23 true true

theorem FixesFrame.map_W (h : FixesFrame β) : β (W F) = W F := by
  unfold W
  rw [map_mul, map_mul, map_mul]
  unfold HypFrame.longWeyl
  rw [h.h0, h.h1, h.h2, h.h3]

theorem spinAction_W_e1 :
    spinAction (quadPlus 4 F) (W F) ((fr F).vec 1 true) = (-1 : F) • (fr F).vec 1 false := by
  unfold W
  rw [map_mul, map_mul, map_mul]
  simp only [LinearEquiv.mul_apply]
  rw [(fr F).spinAction_longWeyl_vec_of_ne ne23 true true (k := 1) (by decide) (by decide) true,
    (fr F).spinAction_longWeyl_vec_of_ne ne23 true false (k := 1) (by decide) (by decide) true,
    (fr F).spinAction_longWeyl_vec_right ne01 true true,
    (fr F).spinAction_longWeyl_vec_left_not ne01 true false]
  simp

theorem spinAction_W_f2 :
    spinAction (quadPlus 4 F) (W F) ((fr F).vec 2 false) = (-1 : F) • (fr F).vec 2 true := by
  have d : spinAction (quadPlus 4 F) ((fr F).longWeyl ne23 true true) ((fr F).vec 2 false) =
      -(fr F).vec 3 true := (fr F).spinAction_longWeyl_vec_left_not ne23 true true
  have c : spinAction (quadPlus 4 F) ((fr F).longWeyl ne23 true false) ((fr F).vec 3 true) =
      (fr F).vec 2 true := (fr F).spinAction_longWeyl_vec_right_not ne23 true false
  unfold W
  rw [map_mul, map_mul, map_mul]
  simp only [LinearEquiv.mul_apply]
  rw [d, map_neg, c, map_neg,
    (fr F).spinAction_longWeyl_vec_of_ne ne01 true true (k := 2) (by decide) (by decide) true,
    map_neg,
    (fr F).spinAction_longWeyl_vec_of_ne ne01 true false (k := 2) (by decide) (by decide) true]
  simp

theorem conj_W_xr (a : F) : W F * xr F a * (W F)⁻¹ = xn F a := by
  have := (fr F).conj_longRoot (W F) ne12 true false (i' := 1) (j' := 2) ne12 false true
    (l := (-1 : F)) (m := (-1 : F)) spinAction_W_e1 spinAction_W_f2 a
  unfold xr xn
  rw [this]
  norm_num

theorem exists_xn_of_fixesFrame {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {c : Fˣ}
    (hc2 : (c : F) ^ 2 ≠ 1) (h : FixesFrame β) (a : F) : ∃ b : F, β (xn F a) = xn F b := by
  obtain ⟨b, hb⟩ := exists_xr_of_fixesFrame hp2 hc2 h a
  refine ⟨b, ?_⟩
  rw [← conj_W_xr a, map_mul, map_mul, map_inv, h.map_W, hb, conj_W_xr]

theorem FixesFrame.symm (h : FixesFrame β) : FixesFrame β.symm :=
  ⟨fun M => (MulEquiv.symm_apply_eq β).mpr (h.h0 M).symm,
    fun M => (MulEquiv.symm_apply_eq β).mpr (h.h1 M).symm,
    fun M => (MulEquiv.symm_apply_eq β).mpr (h.h2 M).symm,
    fun M => (MulEquiv.symm_apply_eq β).mpr (h.h3 M).symm⟩

theorem longSL2_lowerSL2_ne12 (c : F) :
    (fr F).longSL2 ne12 true false (lowerSL2 c) = xn F (-c) := by
  rw [HypFrame.longSL2_lowerSL2]
  unfold xn
  rw [(fr F).longRoot_swap ne12 false true (-c), neg_neg]
  rfl

theorem longSL2_upperSL2_ne12 (c : F) :
    (fr F).longSL2 ne12 true false (upperSL2 c) = xr F c := by
  rw [HypFrame.longSL2_upperSL2]
  rfl

theorem map_longSL2_mem {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {c : Fˣ}
    (hc2 : (c : F) ^ 2 ≠ 1) (h : FixesFrame β) (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    β ((fr F).longSL2 ne12 true false M) ∈ ((fr F).longSL2 ne12 true false).range := by
  have key := mem_closure_upperSL2_lowerSL2
    (β.toMonoidHom.comp ((fr F).longSL2 ne12 true false)) M
  refine (Subgroup.closure_le _).mpr ?_ key
  rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  · obtain ⟨b, hb⟩ := exists_xr_of_fixesFrame hp2 hc2 h d
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, longSL2_upperSL2_ne12, hb]
    exact ⟨upperSL2 b, longSL2_upperSL2_ne12 b⟩
  · obtain ⟨b, hb⟩ := exists_xn_of_fixesFrame hp2 hc2 h (-d)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, longSL2_lowerSL2_ne12, hb]
    exact ⟨lowerSL2 (-b), by rw [longSL2_lowerSL2_ne12, neg_neg]⟩

theorem map_range_longSL2_eq {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {c : Fˣ}
    (hc2 : (c : F) ^ 2 ≠ 1) (h : FixesFrame β) :
    ((fr F).longSL2 ne12 true false).range.map β.toMonoidHom =
      ((fr F).longSL2 ne12 true false).range := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨M, rfl⟩, rfl⟩
    exact map_longSL2_mem hp2 hc2 h M
  · rintro _ ⟨M, rfl⟩
    obtain ⟨M', hM'⟩ := map_longSL2_mem (β := β.symm) hp2 hc2 h.symm M
    exact ⟨_, ⟨M', rfl⟩, by simp [hM']⟩

end Fixes
end CFSG.ClassicalInvolution.ModelFacts.D4Rigid
