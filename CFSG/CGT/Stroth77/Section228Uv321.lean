module

public import CFSG.CGT.Stroth77.Section228Uv

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G}

theorem t321_u_a :
    (StrothTypeIndex.t321).action.φu (Torus.a (k := (StrothTypeIndex.t321).k)) =
      Torus.b (k := (StrothTypeIndex.t321).k) := by
  show Type321.action.φu (gen Type321.k 1) = gen Type321.k 2
  dsimp only [Type321.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu]
  rw [matAct_gen_eq]
  funext i
  fin_cases i <;> simp [Type321.uM, uMat, ofCols_apply, gen, Pi.single_apply]

theorem t321_u_b :
    (StrothTypeIndex.t321).action.φu (Torus.b (k := (StrothTypeIndex.t321).k)) =
      Torus.a (k := (StrothTypeIndex.t321).k) := by
  show Type321.action.φu (gen Type321.k 2) = gen Type321.k 1
  dsimp only [Type321.action, SigmaFourAction.ofMatEq, SigmaFourAction.φu]
  rw [matAct_gen_eq]
  funext i
  fin_cases i <;> simp [Type321.uM, uMat, ofCols_apply, gen, Pi.single_apply]

theorem t321_uv_a :
    (StrothTypeIndex.t321).action.φuv (Torus.a (k := (StrothTypeIndex.t321).k)) =
      Torus.ofInt Type321.k ![4, 1, 6] := by
  show Type321.action.φuv (gen Type321.k 1) = Torus.ofInt Type321.k ![4, 1, 6]
  dsimp only [Type321.action, SigmaFourAction.ofMatEq, SigmaFourAction.φuv]
  rw [matAct_gen_eq]
  rw [Torus.ofInt_eq_zsmul_gens]
  funext i
  fin_cases i <;> simp [Type321.uvM, Type321.uvA, ofCols_apply, gen, Pi.single_apply]

theorem t321_uv_b :
    (StrothTypeIndex.t321).action.φuv (Torus.b (k := (StrothTypeIndex.t321).k)) =
      Torus.ofInt Type321.k ![84, 22, -7] := by
  show Type321.action.φuv (gen Type321.k 2) = Torus.ofInt Type321.k ![84, 22, -7]
  dsimp only [Type321.action, SigmaFourAction.ofMatEq, SigmaFourAction.φuv]
  rw [matAct_gen_eq]
  rw [Torus.ofInt_eq_zsmul_gens]
  funext i
  fin_cases i <;> simp [Type321.uvM, Type321.uvA, Type321.tM, Type321.ρM, ofCols_apply]
  all_goals decide

theorem t321_u_a_half :
    (StrothTypeIndex.t321).action.φu
        ((2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
          Torus.a (k := (StrothTypeIndex.t321).k)) =
      (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.b (k := (StrothTypeIndex.t321).k) := by
  have h4 : (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) = 4 := by decide
  rw [h4, map_nsmul, t321_u_a]

theorem t321_uv_fixes_a_half :
    (StrothTypeIndex.t321).action.φuv
        ((2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
          Torus.a (k := (StrothTypeIndex.t321).k)) =
      (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.a (k := (StrothTypeIndex.t321).k) := by
  have h4 : (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) = 4 := by decide
  rw [h4, map_nsmul, t321_uv_a]
  funext i
  fin_cases i <;>
    simp [Torus.ofInt, Torus.a, gen, Pi.single_apply, nsmul_eq_mul]
  all_goals decide

theorem t321_uv_fixes_b_half :
    (StrothTypeIndex.t321).action.φuv
        ((2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
          Torus.b (k := (StrothTypeIndex.t321).k)) =
      (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.b (k := (StrothTypeIndex.t321).k) := by
  have h4 : (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) = 4 := by decide
  rw [h4, map_nsmul, t321_uv_b]
  funext i
  fin_cases i <;>
    simp [Torus.ofInt, Torus.b, gen, Pi.single_apply, nsmul_eq_mul]
  all_goals decide

theorem t321_φuv_a_add_b :
    (StrothTypeIndex.t321).action.φuv
        (Torus.a (k := (StrothTypeIndex.t321).k) +
          Torus.b (k := (StrothTypeIndex.t321).k)) =
      Torus.ofInt (StrothTypeIndex.t321).k ![88, 23, -1] := by
  rw [map_add, t321_uv_a, t321_uv_b]
  funext i
  fin_cases i <;> simp [Torus.ofInt, Torus.a, Torus.b, gen, Pi.single_apply]
  all_goals decide

theorem t321_φuv_ab_half :
    (StrothTypeIndex.t321).action.φuv
        ((2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) •
          (Torus.a (k := (StrothTypeIndex.t321).k) +
            Torus.b (k := (StrothTypeIndex.t321).k))) =
      -((2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) •
        (Torus.a (k := (StrothTypeIndex.t321).k) +
          Torus.b (k := (StrothTypeIndex.t321).k))) := by
  have h2 : (2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) = 2 := by decide
  rw [h2, map_nsmul, t321_φuv_a_add_b]
  funext i
  fin_cases i <;>
    simp [Torus.ofInt, Torus.a, Torus.b, gen, Pi.single_apply, nsmul_eq_mul]
  all_goals decide

theorem t321_u_fixes_ab_half :
    (StrothTypeIndex.t321).action.φu
        ((2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) •
          (Torus.a (k := (StrothTypeIndex.t321).k) +
            Torus.b (k := (StrothTypeIndex.t321).k))) =
      (2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) •
        (Torus.a (k := (StrothTypeIndex.t321).k) +
          Torus.b (k := (StrothTypeIndex.t321).k)) := by
  have h2 : (2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) = 2 := by decide
  rw [h2, map_nsmul, map_add, t321_u_a, t321_u_b, add_comm]

theorem t321_uv_preimage :
    ∃ v : Torus (StrothTypeIndex.t321).k,
      (StrothTypeIndex.t321).action.φuv v - v =
        (2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) •
          (Torus.a (k := (StrothTypeIndex.t321).k) +
            Torus.b (k := (StrothTypeIndex.t321).k)) := by
  refine ⟨(3 : ℤ) • (Torus.a (k := (StrothTypeIndex.t321).k) +
    Torus.b (k := (StrothTypeIndex.t321).k)), ?_⟩
  have h2 : (2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) = 2 := by decide
  rw [h2, map_zsmul, map_add, t321_uv_a, t321_uv_b]
  funext i
  fin_cases i <;>
    simp [Torus.ofInt, Torus.a, Torus.b, gen, Pi.single_apply, zsmul_eq_mul, nsmul_eq_mul]
  all_goals decide

theorem t321_u_swaps_a_half {dD : StrothWeakTypeData D (StrothTypeIndex.t321)} :
    dD.u⁻¹ * ((dD.a : G) ^ 2 ^ ((StrothTypeIndex.t321).n - 1)) * dD.u =
      (dD.b : G) ^ 2 ^ ((StrothTypeIndex.t321).n - 1) := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj
    ((2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
      Torus.a (k := (StrothTypeIndex.t321).k))
  rw [t321_u_a_half] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.a_eq] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.b_eq] at h
  exact h

theorem t321_d2_sq_eq {dD : StrothWeakTypeData D (StrothTypeIndex.t321)}
    (h : F.IsD D dD) :
    (((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2)) *
        (((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2)) =
      ((F.dA.a : G)⁻¹) ^ 2 * ((F.dA.b : G)⁻¹) ^ 2 := by
  have h2 : (2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) = 2 := by decide
  have h4 : (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) = 4 := by decide
  rw [h2]
  set x : G := (F.dA.a : G)⁻¹ with hx
  set y : G := (F.dA.b : G)⁻¹ with hy
  set ah : G := (dD.a : G) ^ 4 with hah
  set bh : G := (dD.b : G) ^ 4 with hbh
  set ab : G := (dD.a : G) * (dD.b : G) with hab
  change ab ^ 2 * ab ^ 2 = x ^ 2 * y ^ 2
  haveI : IsMulCommutative D := dD.isMulCommutative
  haveI : IsMulCommutative F.A := F.dA.isMulCommutative
  have haord : orderOf (dD.a : G) = 8 := by
    rw [Subgroup.orderOf_coe, StrothWeakTypeData.orderOf_a]
    decide
  have hbord : orderOf (dD.b : G) = 8 := by
    rw [Subgroup.orderOf_coe, StrothWeakTypeData.orderOf_b]
    decide
  have hah2 : ah * ah = 1 := by
    rw [show ah * ah = (dD.a : G) ^ (4 + 4) by rw [hah, ← pow_add]]
    rw [show 4 + 4 = 8 by norm_num, ← haord, pow_orderOf_eq_one]
  have hbh2 : bh * bh = 1 := by
    rw [show bh * bh = (dD.b : G) ^ (4 + 4) by rw [hbh, ← pow_add]]
    rw [show 4 + 4 = 8 by norm_num, ← hbord, pow_orderOf_eq_one]
  have hah_mem_D : ah ∈ D := by
    rw [hah]
    exact D.pow_mem dD.a.2 _
  have hbh_mem_D : bh ∈ D := by
    rw [hbh]
    exact D.pow_mem dD.b.2 _
  have hahΩ : ah ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hah_mem_D hah2
  have hbhΩ : bh ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hbh_mem_D hbh2
  have hah_ofT : ah = dD.ofTorus
      ((2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.a (k := (StrothTypeIndex.t321).k)) := by
    have h4' : ah = (dD.a : G) ^ 2 ^ ((StrothTypeIndex.t321).n - 1) := by
      rw [hah, h4]
    rw [h4', show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t321).k)) from dD.a_eq, ← dD.ofTorus_nsmul]
  have hbh_ofT : bh = dD.ofTorus
      ((2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.b (k := (StrothTypeIndex.t321).k)) := by
    have h4' : bh = (dD.b : G) ^ 2 ^ ((StrothTypeIndex.t321).n - 1) := by
      rw [hbh, h4]
    rw [h4', show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t321).k)) from dD.b_eq, ← dD.ofTorus_nsmul]
  have huv_ah : dD.uv⁻¹ * ah * dD.uv = ah := by
    rw [hah_ofT]
    have hfix := dD.conj_ofTorus dD.uv_mem dD.uv_conj
      ((2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.a (k := (StrothTypeIndex.t321).k))
    rwa [t321_uv_fixes_a_half] at hfix
  have huv_bh : dD.uv⁻¹ * bh * dD.uv = bh := by
    rw [hbh_ofT]
    have hfix := dD.conj_ofTorus dD.uv_mem dD.uv_conj
      ((2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.b (k := (StrothTypeIndex.t321).k))
    rwa [t321_uv_fixes_b_half] at hfix
  have hahK : ah ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G) := by
    have hfix : ah ∈ {g : G | g ∈ omegaIn 1 D ∧ dD.uv⁻¹ * g * dD.uv = g} :=
      ⟨hahΩ, huv_ah⟩
    rw [IsD.omegaIn_one_uv_fixed_eq h] at hfix
    simpa [hx, hy] using hfix
  have hbhK : bh ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G) := by
    have hfix : bh ∈ {g : G | g ∈ omegaIn 1 D ∧ dD.uv⁻¹ * g * dD.uv = g} :=
      ⟨hbhΩ, huv_bh⟩
    rw [IsD.omegaIn_one_uv_fixed_eq h] at hfix
    simpa [hx, hy] using hfix
  have hx4 : x ^ 4 = 1 := by
    rw [hx]
    exact F.dA.pow_four_a_inv
  have hy4 : y ^ 4 = 1 := by
    rw [hy]
    exact F.dA.pow_four_b_inv
  have hx2sq : x ^ 2 * x ^ 2 = 1 := by
    rw [← pow_two, ← pow_mul, show 2 * 2 = 4 by norm_num]
    exact hx4
  have hy2sq : y ^ 2 * y ^ 2 = 1 := by
    rw [← pow_two, ← pow_mul, show 2 * 2 = 4 by norm_num]
    exact hy4
  have hcomm_xy : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
    have hx2A : x ^ 2 ∈ F.A := by
      rw [hx]
      exact F.A.pow_mem (F.A.inv_mem F.dA.a.2) 2
    have hy2A : y ^ 2 ∈ F.A := by
      rw [hy]
      exact F.A.pow_mem (F.A.inv_mem F.dA.b.2) 2
    exact mul_comm_mem_of_isMulCommutative (D := F.A) hx2A hy2A
  have hXXY : x ^ 2 * (x ^ 2 * y ^ 2) = y ^ 2 := by
    rw [← mul_assoc, hx2sq, one_mul]
  have hYXY : y ^ 2 * (x ^ 2 * y ^ 2) = x ^ 2 := by
    rw [← mul_assoc, hcomm_xy.symm, mul_assoc, hy2sq, mul_one]
  have hXYXY : (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2) = 1 := by
    calc (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2)
        = x ^ 2 * (y ^ 2 * x ^ 2) * y ^ 2 := by group
      _ = x ^ 2 * (x ^ 2 * y ^ 2) * y ^ 2 := by rw [hcomm_xy.symm]
      _ = (x ^ 2 * x ^ 2) * (y ^ 2 * y ^ 2) := by group
      _ = 1 := by rw [hx2sq, hy2sq, mul_one]
  have hXinv : (x ^ 2)⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right hx2sq
  have hYinv : (y ^ 2)⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right hy2sq
  have hXYinv : (x ^ 2 * y ^ 2)⁻¹ = x ^ 2 * y ^ 2 :=
    inv_eq_of_mul_eq_one_right hXYXY
  have hKsub : ∀ z ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G),
      z = 1 ∨ z = x ^ 2 ∨ z = y ^ 2 ∨ z = x ^ 2 * y ^ 2 := by
    intro z hz
    refine Subgroup.closure_induction (p := fun z _ =>
      z = 1 ∨ z = x ^ 2 ∨ z = y ^ 2 ∨ z = x ^ 2 * y ^ 2) ?_ ?_ ?_ ?_ hz
    · intro u hu
      rcases hu with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro a b _ _ iha ihb
      rcases iha with rfl | rfl | rfl | rfl <;>
        rcases ihb with rfl | rfl | rfl | rfl <;>
        simp [hx2sq, hy2sq, hcomm_xy.symm, hXXY, hYXY, hXYXY, mul_assoc]
    · intro a _ iha
      rcases iha with rfl | rfl | rfl | rfl <;>
        simp [hXinv, hYinv, hXYinv]
  have hux : F.dA.u⁻¹ * x * F.dA.u = y := by
    rw [hx, hy]
    exact StrothWeakTypeData.u_conj_a_inv F.dA
  have huy : F.dA.u⁻¹ * y * F.dA.u = x := by
    have hu : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
    calc F.dA.u⁻¹ * y * F.dA.u
        = F.dA.u⁻¹ * (F.dA.u⁻¹ * x * F.dA.u) * F.dA.u := by rw [hux]
      _ = (F.dA.u⁻¹ * F.dA.u⁻¹) * x * (F.dA.u * F.dA.u) := by group
      _ = x := by rw [hu, F.dA.u_sq, one_mul, mul_one]
  have hux2 : F.dA.u⁻¹ * x ^ 2 * F.dA.u = y ^ 2 := by
    calc F.dA.u⁻¹ * x ^ 2 * F.dA.u
        = (F.dA.u⁻¹ * x * F.dA.u) ^ 2 := by
            simpa [inv_inv] using
              (conj_pow (a := F.dA.u⁻¹) (b := x) (i := 2)).symm
      _ = y ^ 2 := by rw [hux]
  have huy2 : F.dA.u⁻¹ * y ^ 2 * F.dA.u = x ^ 2 := by
    calc F.dA.u⁻¹ * y ^ 2 * F.dA.u
        = (F.dA.u⁻¹ * y * F.dA.u) ^ 2 := by
            simpa [inv_inv] using
              (conj_pow (a := F.dA.u⁻¹) (b := y) (i := 2)).symm
      _ = x ^ 2 := by rw [huy]
  have hufix : F.dA.u⁻¹ * (x ^ 2 * y ^ 2) * F.dA.u = x ^ 2 * y ^ 2 := by
    calc F.dA.u⁻¹ * (x ^ 2 * y ^ 2) * F.dA.u
        = (F.dA.u⁻¹ * x ^ 2 * F.dA.u) * (F.dA.u⁻¹ * y ^ 2 * F.dA.u) := by group
      _ = y ^ 2 * x ^ 2 := by rw [hux2, huy2]
      _ = x ^ 2 * y ^ 2 := hcomm_xy.symm
  have hswap_d : dD.u⁻¹ * ah * dD.u = bh := by
    simpa [hah, hbh, h4] using t321_u_swaps_a_half (dD := dD)
  have hswap : F.dA.u⁻¹ * ah * F.dA.u = bh := by
    rw [← h.u_eq]
    exact hswap_d
  have hu_bh : F.dA.u⁻¹ * bh * F.dA.u = ah := by
    have hu : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
    calc F.dA.u⁻¹ * bh * F.dA.u
        = F.dA.u⁻¹ * (F.dA.u⁻¹ * ah * F.dA.u) * F.dA.u := by rw [hswap]
      _ = (F.dA.u⁻¹ * F.dA.u⁻¹) * ah * (F.dA.u * F.dA.u) := by group
      _ = ah := by rw [hu, F.dA.u_sq, one_mul, mul_one]
  have hah_ne_one : ah ≠ 1 := by
    have hlt : 4 < orderOf (dD.a : G) := by rw [haord]; norm_num
    have h := pow_ne_one_of_lt_orderOf (x := (dD.a : G)) (n := 4)
      (by norm_num : (4 : ℕ) ≠ 0) hlt
    simpa [hah] using h
  have hbh_ne_one : bh ≠ 1 := by
    have hlt : 4 < orderOf (dD.b : G) := by rw [hbord]; norm_num
    have h := pow_ne_one_of_lt_orderOf (x := (dD.b : G)) (n := 4)
      (by norm_num : (4 : ℕ) ≠ 0) hlt
    simpa [hbh] using h
  have hua_ne : (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
      Torus.a (k := (StrothTypeIndex.t321).k) ≠
      (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.b (k := (StrothTypeIndex.t321).k) := by
    rw [h4]
    intro htor
    have h2 := congrFun htor 1
    simp [Torus.a, Torus.b, gen, Pi.single_apply, nsmul_eq_mul] at h2
    exact (by decide : ¬ ((4 : ZMod 8) = 0)) h2
  have hahb_ne : ah ≠ bh := by
    intro heq
    have htor : (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
        Torus.a (k := (StrothTypeIndex.t321).k) =
        (2 ^ ((StrothTypeIndex.t321).n - 1) : ℕ) •
          Torus.b (k := (StrothTypeIndex.t321).k) := by
      apply dD.ofTorus_inj
      rw [← hah_ofT, ← hbh_ofT]
      exact heq
    exact hua_ne htor
  have hah_ne_xy : ah ≠ x ^ 2 * y ^ 2 := by
    intro hxy
    have hbh_eq : bh = x ^ 2 * y ^ 2 := by
      rw [← hswap, hxy, hufix]
    exact hahb_ne (hxy.trans hbh_eq.symm)
  have hbh_ne_xy : bh ≠ x ^ 2 * y ^ 2 := by
    intro hxy
    have hah_eq : ah = x ^ 2 * y ^ 2 := by
      rw [← hu_bh, hxy, hufix]
    exact hahb_ne (hah_eq.trans hxy.symm)
  have hcomm_ab : Commute (dD.a : G) (dD.b : G) :=
    mul_comm_mem_of_isMulCommutative (D := D) dD.a.2 dD.b.2
  have hLHS : ab ^ 2 * ab ^ 2 = ah * bh := by
    calc ab ^ 2 * ab ^ 2 = ab ^ (2 + 2) := (pow_add ab 2 2).symm
      _ = ab ^ 4 := by norm_num
      _ = (dD.a : G) ^ 4 * (dD.b : G) ^ 4 := by
            rw [hab]
            exact hcomm_ab.mul_pow 4
      _ = ah * bh := by rw [← hah, ← hbh]
  have hmain : ah * bh = x ^ 2 * y ^ 2 := by
    rcases hKsub ah hahK with hah1 | hahx | hahy | hahxy
    · exact absurd hah1 hah_ne_one
    · rcases hKsub bh hbhK with hbh1 | hbhx | hbhy | hbhxy
      · exact absurd hbh1 hbh_ne_one
      · exact absurd (hahx.trans hbhx.symm) hahb_ne
      · rw [hahx, hbhy]
      · exact absurd hbhxy hbh_ne_xy
    · rcases hKsub bh hbhK with hbh1 | hbhx | hbhy | hbhxy
      · exact absurd hbh1 hbh_ne_one
      · rw [hahy, hbhx, hcomm_xy.symm]
      · exact absurd (hahy.trans hbhy.symm) hahb_ne
      · exact absurd hbhxy hbh_ne_xy
    · exact absurd hahxy hah_ne_xy
  exact hLHS.trans hmain

theorem t321_d2_ofTorus {dD : StrothWeakTypeData D (StrothTypeIndex.t321)} :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2) =
      dD.ofTorus ((2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) •
        (Torus.a (k := (StrothTypeIndex.t321).k) +
          Torus.b (k := (StrothTypeIndex.t321).k))) := by
  rw [show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t321).k)) from dD.a_eq,
    show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t321).k)) from dD.b_eq,
    ← dD.ofTorus_add, ← dD.ofTorus_nsmul]

theorem t321_d2_mem_A {dD : StrothWeakTypeData D (StrothTypeIndex.t321)}
    (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2) ∈ F.A := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2)
  let x : G := (F.dA.a : G)⁻¹
  let y : G := (F.dA.b : G)⁻¹
  change d2 ∈ F.A
  haveI : IsMulCommutative D := dD.isMulCommutative
  haveI : IsMulCommutative F.A := F.dA.isMulCommutative
  have hd2D : d2 ∈ D := by
    dsimp only [d2]
    exact D.pow_mem (D.mul_mem dD.a.2 dD.b.2) _
  have hxA : x ∈ F.A := by dsimp only [x]; exact F.A.inv_mem F.dA.a.2
  have hyA : y ∈ F.A := by dsimp only [y]; exact F.A.inv_mem F.dA.b.2
  have hxyA : x * y ∈ F.A := F.A.mul_mem hxA hyA
  have hxyD : x * y ∈ D := h.A_le hxyA
  have hxy_sq : (x * y) * (x * y) = x ^ 2 * y ^ 2 := by
    have hxy_comm : x * y = y * x :=
      mul_comm_mem_of_isMulCommutative (D := F.A) hxA hyA
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy_comm]
      _ = (x * x) * (y * y) := by group
      _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]
  have hd2sq : d2 * d2 = x ^ 2 * y ^ 2 := by
    simpa [d2, x, y] using t321_d2_sq_eq (dD := dD) h
  have hcomm : Commute d2 (x * y) :=
    mul_comm_mem_of_isMulCommutative (D := D) hd2D hxyD
  have hcomm_inv : Commute d2 (x * y)⁻¹ := hcomm.inv_right
  have hz2 : (d2 * (x * y)⁻¹) * (d2 * (x * y)⁻¹) = 1 := by
    calc (d2 * (x * y)⁻¹) * (d2 * (x * y)⁻¹)
        = d2 * ((x * y)⁻¹ * d2) * (x * y)⁻¹ := by group
      _ = d2 * (d2 * (x * y)⁻¹) * (x * y)⁻¹ := by rw [hcomm_inv.eq.symm]
      _ = (d2 * d2) * ((x * y)⁻¹ * (x * y)⁻¹) := by group
      _ = (x ^ 2 * y ^ 2) * (((x * y) * (x * y))⁻¹) := by
            rw [hd2sq, ← _root_.mul_inv_rev]
      _ = (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2)⁻¹ := by rw [hxy_sq]
      _ = 1 := mul_inv_cancel _
  have hzA : d2 * (x * y)⁻¹ ∈ F.A :=
    h.mem_A_of_mul_self (D.mul_mem hd2D (D.inv_mem hxyD)) hz2
  have hd2_eq : d2 = (d2 * (x * y)⁻¹) * (x * y) := by group
  rw [hd2_eq]
  exact F.A.mul_mem hzA hxyA

theorem t321_d2_eq_xy {dD : StrothWeakTypeData D (StrothTypeIndex.t321)}
    (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2) =
        F.dA.toConfig.x * F.dA.toConfig.y ∨
      ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2) =
        (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2)
  let w : Torus (StrothTypeIndex.t321).k :=
    (2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) • (Torus.a + Torus.b)
  change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
    d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹
  have hd2A : d2 ∈ F.A := by
    simpa [d2] using t321_d2_mem_A (dD := dD) h
  have hd2D : d2 ∈ D := by
    dsimp only [d2]
    exact D.pow_mem (D.mul_mem dD.a.2 dD.b.2) _
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t321_d2_ofTorus (dD := dD)
  have hφu : (StrothTypeIndex.t321).action.φu w = w := by
    dsimp only [w]
    exact t321_u_fixes_ab_half
  have hφuv : (StrothTypeIndex.t321).action.φuv w = -w := by
    dsimp only [w]
    exact t321_φuv_ab_half
  have hdu : dD.u⁻¹ * d2 * dD.u = d2 := by
    rw [hd2_ofT]
    have hconj := dD.conj_ofTorus dD.u_mem dD.u_conj w
    rwa [hφu] at hconj
  have hduv : dD.uv⁻¹ * d2 * dD.uv = d2⁻¹ := by
    rw [hd2_ofT]
    have hconj := dD.conj_ofTorus dD.uv_mem dD.uv_conj w
    rw [hφuv, dD.ofTorus_neg] at hconj
    exact hconj
  have hduA : F.dA.u⁻¹ * d2 * F.dA.u = d2 := by
    rw [← h.u_eq]
    exact hdu
  have hduvA : F.dA.uv⁻¹ * d2 * F.dA.uv = d2⁻¹ := by
    rw [← h.uv_eq]
    exact hduv
  obtain ⟨δ, hδ⟩ := F.dA.exists_ofTorus hd2A
  have hδ2 : δ + δ = (2 : ℕ) • Torus.a + (2 : ℕ) • Torus.b := by
    apply F.dA.ofTorus_inj
    rw [F.dA.ofTorus_add, F.dA.ofTorus_add, F.dA.ofTorus_nsmul, F.dA.ofTorus_nsmul]
    rw [← hδ]
    have hd2sq : d2 * d2 =
        ((F.dA.a : G)⁻¹) ^ 2 * ((F.dA.b : G)⁻¹) ^ 2 := by
      simpa [d2] using t321_d2_sq_eq (dD := dD) h
    rw [hd2sq, F.a_inv_sq, F.b_inv_sq]
    rfl
  have hδu : (StrothTypeIndex.t100 1).action.φu δ = δ := by
    apply F.dA.ofTorus_inj
    have hconj := F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj δ
    rw [← hconj, ← hδ]
    exact hduA
  have hδuv : (StrothTypeIndex.t100 1).action.φuv δ = -δ := by
    apply F.dA.ofTorus_inj
    rw [F.dA.ofTorus_neg]
    have hconj := F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj δ
    rw [← hconj, ← hδ]
    exact hduvA
  have hxy : F.dA.toConfig.x * F.dA.toConfig.y =
      F.dA.ofTorus (-(Torus.a + Torus.b)) := by
    rw [StrothWeakTypeData.toConfig_x, StrothWeakTypeData.toConfig_y,
      neg_add, F.dA.ofTorus_add, F.dA.ofTorus_neg, F.dA.ofTorus_neg,
      ← F.dA.a_eq, ← F.dA.b_eq]
  rcases Stroth43Fus.t100_one_xy δ hδ2 hδu hδuv with hδab | hδab
  · right
    rw [hδ, hδab, hxy, ← F.dA.ofTorus_neg, neg_neg]
  · left
    rw [hδ, hδab, hxy]

theorem t321_isConj_uv_xyuv {dD : StrothWeakTypeData D (StrothTypeIndex.t321)}
    (h : F.IsD D dD) :
    IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv) := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t321).n - 2)
  let w : Torus (StrothTypeIndex.t321).k :=
    (2 ^ ((StrothTypeIndex.t321).n - 2) : ℕ) • (Torus.a + Torus.b)
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t321_d2_ofTorus (dD := dD)
  have hd2 : d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
    have h := t321_d2_eq_xy (dD := dD) h
    change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ at h
    exact h
  obtain ⟨v, hv⟩ := t321_uv_preimage
  have hφ : dD.ofTorus ((StrothTypeIndex.t321).action.φuv v - v) = d2 := by
    rw [hv, hd2_ofT]
  exact isConj_uv_xyuv_of_d2 (τ := StrothTypeIndex.t321) h hd2 hφ

end StrothFrame.IsD

end CFSG.CGT.Stroth77
