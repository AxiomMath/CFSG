module

public import CFSG.CGT.Stroth77.Section224A
public import CFSG.CGT.Stroth77.Stroth31NeAFrame
public import CFSG.CGT.Stroth77.Section43Fus

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem isConj_uv_xyuv_of_d2 (h : F.IsD D dD) {d2 : G}
    (hd2 : d2 = (F.dA.toConfig.x * F.dA.toConfig.y) ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹)
    {v : Torus τ.k} (hφ : dD.ofTorus (τ.action.φuv v - v) = d2) :
    IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv) := by
  have huv : dD.uv = F.dA.uv := h.uv_eq
  have hconj : (dD.ofTorus v)⁻¹ * dD.uv * dD.ofTorus v = d2 * dD.uv := by
    rw [Stroth43Fus.ofTorus_inv_mul_uv_mul, hφ]
  rcases hd2 with hd2 | hd2
  · rw [hd2] at hconj
    refine isConj_iff.2 ⟨(dD.ofTorus v)⁻¹, ?_⟩
    simpa [huv] using hconj
  · have hφ' : dD.ofTorus (τ.action.φuv (-v) - -v) =
        (F.dA.toConfig.x * F.dA.toConfig.y) := by
      rw [show τ.action.φuv (-v) - -v = -(τ.action.φuv v - v) by
            rw [map_neg]; abel,
        dD.ofTorus_neg, hφ, hd2, inv_inv]
    have hconj' : (dD.ofTorus (-v))⁻¹ * dD.uv * dD.ofTorus (-v) =
        (F.dA.toConfig.x * F.dA.toConfig.y) * dD.uv := by
      rw [Stroth43Fus.ofTorus_inv_mul_uv_mul, hφ']
    refine isConj_iff.2 ⟨(dD.ofTorus (-v))⁻¹, ?_⟩
    simpa [huv] using hconj'

theorem IsD.omegaIn_one_eq_closure_w_a_sq_b_sq (h : F.IsD D dD) :
    omegaIn 1 D = Subgroup.closure ({(F.dA.c : G), ((F.dA.a : G) ^ 2),
      ((F.dA.b : G) ^ 2)} : Set G) := by
  rw [h.omegaIn_one_eq, omegaIn_one_t100 F.dA]
  simp

theorem t100_uv_not_fixes_w (F : StrothFrame G) :
    F.dA.uv⁻¹ * (F.dA.c : G) * F.dA.uv ≠ (F.dA.c : G) := by
  intro hw
  have hφ : (StrothTypeIndex.t100 1).action.φuv
      (Torus.c (k := (StrothTypeIndex.t100 1).k)) =
        Torus.c + (2 : ℕ) • Torus.a + (2 : ℕ) • Torus.b := by
    show (Type100.action 1).φuv (Torus.c (k := Type100.k 1)) =
      Torus.c + (2 : ℕ) • Torus.a + (2 : ℕ) • Torus.b
    rw [Type100.uv_c 1]
    funext i
    fin_cases i <;> simp [Torus.c, Torus.a, Torus.b, gen, Pi.single_apply, zsmul_eq_mul]
    all_goals decide
  have h := F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj
    (Torus.c (k := (StrothTypeIndex.t100 1).k))
  rw [hφ, show F.dA.ofTorus (Torus.c (k := (StrothTypeIndex.t100 1).k)) =
    ((F.dA.c : F.A) : G) from rfl] at h
  rw [hw] at h
  have hc : (Torus.c : Torus (StrothTypeIndex.t100 1).k) +
      (2 : ℕ) • Torus.a + (2 : ℕ) • Torus.b = Torus.c := by
    exact F.dA.ofTorus_inj (by
      simpa [show F.dA.ofTorus (Torus.c (k := (StrothTypeIndex.t100 1).k)) =
        ((F.dA.c : F.A) : G) from rfl] using h.symm)
  have hcoord := congrFun hc 1
  simp [Torus.c, Torus.a, Torus.b, gen, Pi.single_apply] at hcoord
  change (2 : ZMod 4) = 0 at hcoord
  exact (by decide : ¬ ((2 : ZMod 4) = 0)) hcoord

theorem t100_uv_fixed_torus :
    {v : Torus (StrothTypeIndex.t100 1).k |
        v + v = 0 ∧ (StrothTypeIndex.t100 1).action.φuv v = v} =
      ({0, (2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k),
        (2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k),
        (2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k) +
          (2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k)} :
        Set (Torus (StrothTypeIndex.t100 1).k)) := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert v
  decide

theorem t100_uv_fixes_a_sq (F : StrothFrame G) :
    F.dA.uv⁻¹ * ((F.dA.a : G) ^ 2) * F.dA.uv = (F.dA.a : G) ^ 2 := by
  have hφ : (StrothTypeIndex.t100 1).action.φuv
      ((2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k)) =
        (2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k) := by
    show (Type100.action 1).φuv ((2 : ℕ) • Torus.a (k := Type100.k 1)) =
      (2 : ℕ) • Torus.a (k := Type100.k 1)
    rw [map_nsmul, Type100.uv_a 1]
    funext i
    fin_cases i <;> simp [Torus.c, Torus.a, Torus.b, gen, Pi.single_apply, nsmul_eq_mul]
    all_goals decide
  have h := F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj
    ((2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k))
  rw [hφ, StrothWeakTypeData.ofTorus_nsmul,
    show F.dA.ofTorus (Torus.a (k := (StrothTypeIndex.t100 1).k)) = ((F.dA.a : F.A) : G)
      from rfl] at h
  simpa using h

theorem t100_uv_fixes_b_sq (F : StrothFrame G) :
    F.dA.uv⁻¹ * ((F.dA.b : G) ^ 2) * F.dA.uv = (F.dA.b : G) ^ 2 := by
  have hcomm : ∀ v : Torus (StrothTypeIndex.t100 1).k,
      (StrothTypeIndex.t100 1).action.φu ((StrothTypeIndex.t100 1).action.φuv v) =
        (StrothTypeIndex.t100 1).action.φuv
          ((StrothTypeIndex.t100 1).action.φu v) :=
    fun v => DFunLike.congr_fun (StrothTypeIndex.t100 1).action.rels.uv_comm_u v
  have hua : (StrothTypeIndex.t100 1).action.φu
      ((2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k)) =
        (2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k) := by
    show (Type100.action 1).φu ((2 : ℕ) • Torus.a (k := Type100.k 1)) =
      (2 : ℕ) • Torus.b (k := Type100.k 1)
    rw [map_nsmul, Type100.u_a 1]
    simp
  have huv_a : (StrothTypeIndex.t100 1).action.φuv
      ((2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k)) =
        (2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k) := by
    show (Type100.action 1).φuv ((2 : ℕ) • Torus.a (k := Type100.k 1)) =
      (2 : ℕ) • Torus.a (k := Type100.k 1)
    rw [map_nsmul, Type100.uv_a 1]
    funext i
    fin_cases i <;> simp [Torus.c, Torus.a, Torus.b, gen, Pi.single_apply, nsmul_eq_mul]
    all_goals decide
  have hφ : (StrothTypeIndex.t100 1).action.φuv
      ((2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k)) =
        (2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k) := by
    calc (StrothTypeIndex.t100 1).action.φuv
          ((2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k))
        = (StrothTypeIndex.t100 1).action.φuv
            ((StrothTypeIndex.t100 1).action.φu
              ((2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k))) := by rw [hua]
      _ = (StrothTypeIndex.t100 1).action.φu
            ((StrothTypeIndex.t100 1).action.φuv
              ((2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k))) :=
            (hcomm _).symm
      _ = (StrothTypeIndex.t100 1).action.φu
            ((2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k)) := by rw [huv_a]
      _ = (2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k) := hua
  have h := F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj
    ((2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k))
  rw [hφ, StrothWeakTypeData.ofTorus_nsmul,
    show F.dA.ofTorus (Torus.b (k := (StrothTypeIndex.t100 1).k)) = ((F.dA.b : F.A) : G)
      from rfl] at h
  simpa using h

theorem t100_uv_fixed_group (F : StrothFrame G) :
    (omegaIn 1 F.A) ⊓ Subgroup.centralizer ({(F.dA.uv : G)} : Set G) =
      Subgroup.closure ({(F.dA.a : G) ^ 2, (F.dA.b : G) ^ 2} : Set G) := by
  haveI : IsMulCommutative F.A := F.dA.isMulCommutative
  have hcomm : ∀ x ∈ F.A, ∀ y ∈ F.A, x * y = y * x :=
    fun x hx y hy => mul_comm_mem_of_isMulCommutative hx hy
  let K : Subgroup G := Subgroup.closure ({(F.dA.a : G) ^ 2, (F.dA.b : G) ^ 2} : Set G)
  let Fix : Subgroup G := (omegaIn 1 F.A) ⊓ Subgroup.centralizer ({(F.dA.uv : G)} : Set G)
  change Fix = K
  have ha4 : (F.dA.a : G) ^ 4 = 1 := by
    have hord : orderOf (F.dA.a : G) = 4 := by
      have h := StrothWeakTypeData.orderOf_a F.dA
      rw [show (StrothTypeIndex.t100 1).n = 2 from rfl] at h
      simpa using h
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  have hb4 : (F.dA.b : G) ^ 4 = 1 := by
    have hord : orderOf (F.dA.b : G) = 4 := by
      have h := StrothWeakTypeData.orderOf_b F.dA
      rw [show (StrothTypeIndex.t100 1).n = 2 from rfl] at h
      simpa using h
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hg
    obtain ⟨hgΩ, hgc⟩ := hg
    obtain ⟨v, hv⟩ := F.dA.exists_ofTorus (omegaIn_le 1 F.A hgΩ)
    have hg2 : g * g = 1 := mul_self_eq_one_of_mem_omegaIn_one hcomm hgΩ
    have hv2 : v + v = 0 := by
      apply F.dA.ofTorus_inj
      rw [F.dA.ofTorus_add, F.dA.ofTorus_zero, ← hv]
      exact hg2
    have hφ : (StrothTypeIndex.t100 1).action.φuv v = v := by
      apply F.dA.ofTorus_inj
      have hconj := F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj v
      rw [← hconj, ← hv]
      calc F.dA.uv⁻¹ * g * F.dA.uv = F.dA.uv⁻¹ * (g * F.dA.uv) := by group
        _ = F.dA.uv⁻¹ * (F.dA.uv * g) := by rw [hgc]
        _ = g := by group
    have hvset : v ∈ ({0, (2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k),
        (2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k),
        (2 : ℕ) • Torus.a (k := (StrothTypeIndex.t100 1).k) +
          (2 : ℕ) • Torus.b (k := (StrothTypeIndex.t100 1).k)} :
        Set (Torus (StrothTypeIndex.t100 1).k)) := by
      rw [← t100_uv_fixed_torus]
      exact ⟨hv2, hφ⟩
    rw [hv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvset
    rcases hvset with rfl | rfl | rfl | rfl
    · simp [F.dA.ofTorus_zero]
    · rw [F.dA.ofTorus_nsmul]
      rw [show F.dA.ofTorus (Torus.a (k := (StrothTypeIndex.t100 1).k)) =
        (F.dA.a : G) from F.dA.a_eq.symm]
      exact Subgroup.subset_closure (by simp)
    · rw [F.dA.ofTorus_nsmul]
      rw [show F.dA.ofTorus (Torus.b (k := (StrothTypeIndex.t100 1).k)) =
        (F.dA.b : G) from F.dA.b_eq.symm]
      exact Subgroup.subset_closure (by simp)
    · rw [F.dA.ofTorus_add, F.dA.ofTorus_nsmul, F.dA.ofTorus_nsmul]
      rw [show F.dA.ofTorus (Torus.a (k := (StrothTypeIndex.t100 1).k)) =
        (F.dA.a : G) from F.dA.a_eq.symm]
      rw [show F.dA.ofTorus (Torus.b (k := (StrothTypeIndex.t100 1).k)) =
        (F.dA.b : G) from F.dA.b_eq.symm]
      exact K.mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · change Subgroup.closure ({(F.dA.a : G) ^ 2, (F.dA.b : G) ^ 2} : Set G) ≤ Fix
    apply (Subgroup.closure_le Fix).2
    intro x hx
    dsimp only [Fix]
    change x ∈ (omegaIn 1 F.A) ⊓ Subgroup.centralizer ({(F.dA.uv : G)} : Set G)
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl
    · refine ⟨mem_omegaIn_one_of_mul_self (Subgroup.pow_mem F.A (F.dA.a : F.A).2 2) ?_, ?_⟩
      · rw [← pow_add]; norm_num [ha4]
      · have h := congrArg (fun x => F.dA.uv * x) (t100_uv_fixes_a_sq F)
        simpa [mul_assoc, F.dA.uv_sq] using h
    · refine ⟨mem_omegaIn_one_of_mul_self (Subgroup.pow_mem F.A (F.dA.b : F.A).2 2) ?_, ?_⟩
      · rw [← pow_add]; norm_num [hb4]
      · have h := congrArg (fun x => F.dA.uv * x) (t100_uv_fixes_b_sq F)
        simpa [mul_assoc, F.dA.uv_sq] using h

theorem t100_uv_fixed_set (F : StrothFrame G) :
    {g : G | g ∈ omegaIn 1 F.A ∧ F.dA.uv⁻¹ * g * F.dA.uv = g} =
      Subgroup.closure ({(F.dA.a : G) ^ 2, (F.dA.b : G) ^ 2} : Set G) := by
  ext g
  rw [Set.mem_setOf_eq, ← t100_uv_fixed_group F]
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, ?_⟩
    change g ∈ Subgroup.centralizer ({(F.dA.uv : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun x => F.dA.uv * x) hfix
    simpa [mul_assoc, F.dA.uv_sq] using h
  · rintro ⟨hg, hgc⟩
    refine ⟨hg, ?_⟩
    change g ∈ Subgroup.centralizer ({(F.dA.uv : G)} : Set G) at hgc
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    calc F.dA.uv⁻¹ * g * F.dA.uv = F.dA.uv⁻¹ * (g * F.dA.uv) := by group
      _ = F.dA.uv⁻¹ * (F.dA.uv * g) := by rw [hgc]
      _ = g := by group

theorem IsD.omegaIn_one_uv_fixed_eq (h : F.IsD D dD) :
    {g : G | g ∈ omegaIn 1 D ∧ dD.uv⁻¹ * g * dD.uv = g} =
      Subgroup.closure ({((F.dA.a : G)⁻¹) ^ 2, ((F.dA.b : G)⁻¹) ^ 2} : Set G) := by
  have ha4 : (F.dA.a : G) ^ 4 = 1 := by
    have hord : orderOf (F.dA.a : G) = 4 := by
      have h := StrothWeakTypeData.orderOf_a F.dA
      rw [show (StrothTypeIndex.t100 1).n = 2 from rfl] at h
      simpa using h
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  have hb4 : (F.dA.b : G) ^ 4 = 1 := by
    have hord : orderOf (F.dA.b : G) = 4 := by
      have h := StrothWeakTypeData.orderOf_b F.dA
      rw [show (StrothTypeIndex.t100 1).n = 2 from rfl] at h
      simpa using h
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  have ha : ((F.dA.a : G)⁻¹) ^ 2 = (F.dA.a : G) ^ 2 := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right (by
      rw [show (F.dA.a : G) ^ 2 * (F.dA.a : G) ^ 2 = (F.dA.a : G) ^ 4 by
        rw [← pow_add]]
      exact ha4)
  have hb : ((F.dA.b : G)⁻¹) ^ 2 = (F.dA.b : G) ^ 2 := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right (by
      rw [show (F.dA.b : G) ^ 2 * (F.dA.b : G) ^ 2 = (F.dA.b : G) ^ 4 by
        rw [← pow_add]]
      exact hb4)
  have hset : ({((F.dA.a : G)⁻¹) ^ 2, ((F.dA.b : G)⁻¹) ^ 2} : Set G) =
      ({(F.dA.a : G) ^ 2, (F.dA.b : G) ^ 2} : Set G) := by
    rw [ha, hb]
  calc {g : G | g ∈ omegaIn 1 D ∧ dD.uv⁻¹ * g * dD.uv = g}
      = {g : G | g ∈ omegaIn 1 F.A ∧ F.dA.uv⁻¹ * g * F.dA.uv = g} := by
          rw [h.omegaIn_one_eq, h.uv_eq]
    _ = Subgroup.closure ({(F.dA.a : G) ^ 2, (F.dA.b : G) ^ 2} : Set G) :=
          t100_uv_fixed_set F
    _ = Subgroup.closure ({((F.dA.a : G)⁻¹) ^ 2, ((F.dA.b : G)⁻¹) ^ 2} : Set G) := by
          rw [hset]

theorem t310_u_a_half (m : ℕ) (hm : 2 ≤ m) :
    (StrothTypeIndex.t310 m hm).action.φu
        ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k)) =
      (2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k) := by
  show (Type310.action m hm).φu ((2 ^ (m - 1) : ℕ) • Torus.a (k := Type310.k m)) =
    (2 ^ (m - 1) : ℕ) • Torus.b (k := Type310.k m)
  rw [map_nsmul, Type310.u_a m hm]
  simp

theorem t310_u_swaps_a_half {D : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (dD : StrothWeakTypeData D (StrothTypeIndex.t310 m hm)) :
    dD.u⁻¹ * ((dD.a : G) ^ 2 ^ (m - 1)) * dD.u = (dD.b : G) ^ 2 ^ (m - 1) := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj
    ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k))
  rw [t310_u_a_half m hm] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.a_eq] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.b_eq] at h
  exact h

theorem t310_uv_fixes_a (m : ℕ) (hm : 2 ≤ m) :
    (StrothTypeIndex.t310 m hm).action.φuv
        ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k)) =
      (2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k) := by
  show (Type310.action m hm).φuv ((2 ^ (m - 1) : ℕ) • Torus.a (k := Type310.k m)) =
    (2 ^ (m - 1) : ℕ) • Torus.a (k := Type310.k m)
  dsimp only [Type310.action, SigmaFourAction.ofMatEq, SigmaFourAction.φuv, Torus.a]
  rw [map_nsmul, matAct_gen_eq]
  simp [Type310.uvM, Type310.uvA, Type310.ρM, Type310.tM, uMat, ofCols, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  funext i
  fin_cases i <;> simp [gen, Pi.single_apply, zsmul_eq_mul]
  · have hzero : ((2 : ZMod (2 ^ m)) ^ m) = 0 := by
      rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) from by norm_num]
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have h1 : (2 : ZMod (2 ^ m)) ^ (m - 1) * 4 = 0 := by
      rw [show (4 : ZMod (2 ^ m)) = 2 ^ 2 by norm_num, ← pow_add,
        show m - 1 + 2 = m + 1 by omega, pow_succ, hzero, zero_mul]
    change (2 : ZMod (2 ^ m)) ^ (m - 1) * 4 = 0
    exact h1
  · have hzero : ((2 : ZMod (2 ^ m)) ^ m) = 0 := by
      rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) from by norm_num]
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := by
      rw [← pow_succ, show m - 1 + 1 = m by omega, hzero]
    change (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0
    exact h2

theorem t310_uv_fixes_b (m : ℕ) (hm : 2 ≤ m) :
    (StrothTypeIndex.t310 m hm).action.φuv
        ((2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k)) =
      (2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k) := by
  have hcomm : ∀ v : Torus (StrothTypeIndex.t310 m hm).k,
      (StrothTypeIndex.t310 m hm).action.φu ((StrothTypeIndex.t310 m hm).action.φuv v) =
        (StrothTypeIndex.t310 m hm).action.φuv
          ((StrothTypeIndex.t310 m hm).action.φu v) :=
    fun v => DFunLike.congr_fun (StrothTypeIndex.t310 m hm).action.rels.uv_comm_u v
  calc (StrothTypeIndex.t310 m hm).action.φuv
        ((2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k))
      = (StrothTypeIndex.t310 m hm).action.φuv
          ((StrothTypeIndex.t310 m hm).action.φu
            ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k))) := by
          rw [t310_u_a_half m hm]
    _ = (StrothTypeIndex.t310 m hm).action.φu
          ((StrothTypeIndex.t310 m hm).action.φuv
            ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k))) :=
          (hcomm _).symm
    _ = (StrothTypeIndex.t310 m hm).action.φu
          ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k)) := by
          rw [t310_uv_fixes_a m hm]
    _ = (2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k) :=
          t310_u_a_half m hm

theorem t310_φuv_a_add_b (m : ℕ) (hm : 2 ≤ m) :
    (Type310.action m hm).φuv
        (Torus.a (k := Type310.k m) + Torus.b (k := Type310.k m)) =
      Torus.ofInt (Type310.k m) ![-(32 : ℤ) * 2 ^ (m - 2) + 8,
        -(8 : ℤ) * 2 ^ (m - 2) + 3, -(8 : ℤ) * 2 ^ (m - 2) + 3] := by
  rw [map_add, Type310.uv_a m hm, Type310.uv_b m hm]
  funext i
  fin_cases i <;>
    simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply, Torus.ofInt, zsmul_eq_mul]
  all_goals ring

theorem t310_uv_preimage {m : ℕ} (hm : 2 ≤ m) :
    ∃ v : Torus (StrothTypeIndex.t310 m hm).k,
      (StrothTypeIndex.t310 m hm).action.φuv v - v =
        (2 ^ (m - 2) : ℕ) • (Torus.a + Torus.b) := by
  obtain h2 | h2 : m = 2 ∨ 2 < m := by omega
  · subst h2
    obtain rfl : hm = (le_rfl : 2 ≤ 2) := Subsingleton.elim hm _
    refine ⟨Torus.c + Torus.a, ?_⟩
    decide
  · let N : ℤ := (2 : ℤ) ^ (m - 3)
    let v : Torus (Type310.k m) := Torus.ofInt (Type310.k m) ![0, N, N]
    refine ⟨v, ?_⟩
    change (Type310.action m hm).φuv v - v =
      (2 ^ (m - 2) : ℕ) • (Torus.a (k := Type310.k m) +
        Torus.b (k := Type310.k m))
    have hN2 : (2 : ℤ) ^ (m - 2) = 2 * N := by
      dsimp only [N]
      rw [show m - 2 = (m - 3) + 1 by omega, pow_succ]
      ring
    have h8N : (8 : ℤ) * N = (2 : ℤ) ^ m := by
      dsimp only [N]
      rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add,
        show 3 + (m - 3) = m by omega]
    have hzsmul : ∀ {k : Fin 3 → ℕ} (z : ℤ) (f : Torus k) (i : Fin 3),
        (z • f) i = z • f i := fun _ _ _ => rfl
    have hv : v = N • (Torus.a (k := Type310.k m) + Torus.b (k := Type310.k m)) := by
      dsimp only [v]
      rw [Torus.ofInt_eq_zsmul_gens, smul_add]
      simp [Torus.a, Torus.b, gen]
    have hφv : (Type310.action m hm).φuv v =
        Torus.ofInt (Type310.k m) ![
          N * (-(32 : ℤ) * 2 ^ (m - 2) + 8),
          N * (-(8 : ℤ) * 2 ^ (m - 2) + 3),
          N * (-(8 : ℤ) * 2 ^ (m - 2) + 3)] := by
      rw [hv, map_zsmul, t310_φuv_a_add_b (m := m) hm, ← Torus.ofInt_zsmul]
      congr 1
      funext i
      fin_cases i <;> simp [Pi.smul_apply]
    have hw : (2 ^ (m - 2) : ℕ) •
        (Torus.a (k := Type310.k m) + Torus.b (k := Type310.k m)) =
        Torus.ofInt (Type310.k m)
          ![0, (2 : ℤ) ^ (m - 2), (2 : ℤ) ^ (m - 2)] := by
      rw [← natCast_zsmul, smul_add,
        show Torus.a (k := Type310.k m) = gen (Type310.k m) 1 from rfl,
        show Torus.b (k := Type310.k m) = gen (Type310.k m) 2 from rfl]
      simpa using (Torus.ofInt_eq_zsmul_gens (k := Type310.k m)
        (v := ![0, (2 : ℤ) ^ (m - 2), (2 : ℤ) ^ (m - 2)])).symm
    rw [hφv, hw]
    dsimp only [v]
    rw [← Torus.ofInt_sub, Torus.ofInt_eq_ofInt_iff]
    intro i
    fin_cases i
    · rw [Int.modEq_iff_dvd]
      refine ⟨8 * N - 1, ?_⟩
      simp only [Type310.k, Pi.sub_apply, hN2, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [← h8N]
      ring_nf
    · rw [Int.modEq_iff_dvd]
      refine ⟨2 * N, ?_⟩
      simp only [Type310.k, Pi.sub_apply, hN2, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [← h8N]
      ring_nf
    · rw [Int.modEq_iff_dvd]
      refine ⟨2 * N, ?_⟩
      simp only [Type310.k, Pi.sub_apply, hN2, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [← h8N]
      ring_nf

theorem t310_φuv_ab_half {m : ℕ} (hm : 2 ≤ m) :
    (StrothTypeIndex.t310 m hm).action.φuv
        ((2 ^ (m - 2) : ℕ) • (Torus.a + Torus.b)) =
      -((2 ^ (m - 2) : ℕ) • (Torus.a + Torus.b)) := by
  obtain ⟨v, hv⟩ := t310_uv_preimage (m := m) hm
  have hsq := (StrothTypeIndex.t310 m hm).action.rels.uv_sq
  have hvv : (StrothTypeIndex.t310 m hm).action.φuv
      ((StrothTypeIndex.t310 m hm).action.φuv v) = v := by
    have := DFunLike.congr_fun hsq v
    simpa using this
  have h2 : (StrothTypeIndex.t310 m hm).action.φuv
      ((StrothTypeIndex.t310 m hm).action.φuv v - v) =
      -((StrothTypeIndex.t310 m hm).action.φuv v - v) := by
    rw [map_sub, hvv]
    abel
  rwa [hv] at h2

theorem t310_d2_sq_eq {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t310 m hm)} (h : F.IsD D dD) :
    (((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2)) *
        (((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2)) =
      ((F.dA.a : G)⁻¹) ^ 2 * ((F.dA.b : G)⁻¹) ^ 2 := by
  set x : G := (F.dA.a : G)⁻¹ with hx
  set y : G := (F.dA.b : G)⁻¹ with hy
  set ah : G := (dD.a : G) ^ 2 ^ (m - 1) with hah
  set bh : G := (dD.b : G) ^ 2 ^ (m - 1) with hbh
  set ab : G := (dD.a : G) * (dD.b : G) with hab
  change ab ^ 2 ^ (m - 2) * ab ^ 2 ^ (m - 2) = x ^ 2 * y ^ 2
  haveI : IsMulCommutative D := dD.isMulCommutative
  haveI : IsMulCommutative F.A := F.dA.isMulCommutative
  have haord : orderOf (dD.a : G) = 2 ^ m := by
    rw [Subgroup.orderOf_coe, StrothWeakTypeData.orderOf_a]
    rfl
  have hbord : orderOf (dD.b : G) = 2 ^ m := by
    rw [Subgroup.orderOf_coe, StrothWeakTypeData.orderOf_b]
    rfl
  have hah2 : ah * ah = 1 := by
    rw [show ah * ah = (dD.a : G) ^ (2 ^ (m - 1) + 2 ^ (m - 1)) by
      rw [hah, ← pow_add]]
    rw [show 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m by
      rw [← two_mul, ← pow_succ', show m - 1 + 1 = m by omega]]
    rw [← haord, pow_orderOf_eq_one]
  have hbh2 : bh * bh = 1 := by
    rw [show bh * bh = (dD.b : G) ^ (2 ^ (m - 1) + 2 ^ (m - 1)) by
      rw [hbh, ← pow_add]]
    rw [show 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m by
      rw [← two_mul, ← pow_succ', show m - 1 + 1 = m by omega]]
    rw [← hbord, pow_orderOf_eq_one]
  have hah_mem_D : ah ∈ D := by
    rw [hah]
    exact D.pow_mem dD.a.2 _
  have hbh_mem_D : bh ∈ D := by
    rw [hbh]
    exact D.pow_mem dD.b.2 _
  have hahΩ : ah ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hah_mem_D hah2
  have hbhΩ : bh ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hbh_mem_D hbh2
  have hah_ofT : ah = dD.ofTorus
      ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k)) := by
    rw [hah, show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t310 m hm).k)) from dD.a_eq, ← dD.ofTorus_nsmul]
  have hbh_ofT : bh = dD.ofTorus
      ((2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k)) := by
    rw [hbh, show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t310 m hm).k)) from dD.b_eq, ← dD.ofTorus_nsmul]
  have huv_ah : dD.uv⁻¹ * ah * dD.uv = ah := by
    rw [hah_ofT]
    have hfix := dD.conj_ofTorus dD.uv_mem dD.uv_conj
      ((2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k))
    rwa [t310_uv_fixes_a m hm] at hfix
  have huv_bh : dD.uv⁻¹ * bh * dD.uv = bh := by
    rw [hbh_ofT]
    have hfix := dD.conj_ofTorus dD.uv_mem dD.uv_conj
      ((2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k))
    rwa [t310_uv_fixes_b m hm] at hfix
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
    simpa [hah, hbh] using t310_u_swaps_a_half hm dD
  have hswap : F.dA.u⁻¹ * ah * F.dA.u = bh := by
    rw [← h.u_eq]
    exact hswap_d
  have hu_bh : F.dA.u⁻¹ * bh * F.dA.u = ah := by
    have hu : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
    calc F.dA.u⁻¹ * bh * F.dA.u
        = F.dA.u⁻¹ * (F.dA.u⁻¹ * ah * F.dA.u) * F.dA.u := by rw [hswap]
      _ = (F.dA.u⁻¹ * F.dA.u⁻¹) * ah * (F.dA.u * F.dA.u) := by group
      _ = ah := by rw [hu, F.dA.u_sq, one_mul, mul_one]
  have hltpow : 2 ^ (m - 1) < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hah_ne_one : ah ≠ 1 := by
    have hlt : 2 ^ (m - 1) < orderOf (dD.a : G) := by
      simpa [haord] using hltpow
    have h := pow_ne_one_of_lt_orderOf (x := (dD.a : G)) (n := 2 ^ (m - 1))
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hlt
    simpa [hah] using h
  have hbh_ne_one : bh ≠ 1 := by
    have hlt : 2 ^ (m - 1) < orderOf (dD.b : G) := by
      simpa [hbord] using hltpow
    have h := pow_ne_one_of_lt_orderOf (x := (dD.b : G)) (n := 2 ^ (m - 1))
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hlt
    simpa [hbh] using h
  have hua_ne : (2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k) ≠
      (2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k) := by
    intro htor
    have h1 := congrFun htor 1
    simp [Torus.a, Torus.b, gen, Pi.single_apply, nsmul_eq_mul] at h1
    exact two_pow_pred_ne_zero (n := m) (by omega) h1
  have hahb_ne : ah ≠ bh := by
    intro heq
    have htor : (2 ^ (m - 1) : ℕ) • Torus.a (k := (StrothTypeIndex.t310 m hm).k) =
        (2 ^ (m - 1) : ℕ) • Torus.b (k := (StrothTypeIndex.t310 m hm).k) := by
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
  have hLHS : ab ^ 2 ^ (m - 2) * ab ^ 2 ^ (m - 2) = ah * bh := by
    have hpow : 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1) := by
      rw [← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega]
    calc ab ^ 2 ^ (m - 2) * ab ^ 2 ^ (m - 2)
        = ab ^ (2 ^ (m - 2) + 2 ^ (m - 2)) := (pow_add ab _ _).symm
      _ = ab ^ 2 ^ (m - 1) := by rw [hpow]
      _ = (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) := by
            rw [hab]
            exact hcomm_ab.mul_pow _
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

theorem t310_d2_ofTorus {D : Subgroup G} {m : ℕ} {hm : 2 ≤ m}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t310 m hm)} :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2) =
      dD.ofTorus ((2 ^ (m - 2) : ℕ) •
        (Torus.a (k := (StrothTypeIndex.t310 m hm).k) +
          Torus.b (k := (StrothTypeIndex.t310 m hm).k))) := by
  rw [show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t310 m hm).k)) from dD.a_eq,
    show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t310 m hm).k)) from dD.b_eq,
    ← dD.ofTorus_add, ← dD.ofTorus_nsmul]

theorem t310_d2_mem_A {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t310 m hm)} (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2) ∈ F.A := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2)
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
    have hxy_comm : x * y = y * x := mul_comm_mem_of_isMulCommutative (D := F.A) hxA hyA
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy_comm]
      _ = (x * x) * (y * y) := by group
      _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]
  have hd2sq : d2 * d2 = x ^ 2 * y ^ 2 := by
    simpa [d2, x, y] using t310_d2_sq_eq (m := m) (dD := dD) hm h
  have hcomm : Commute d2 (x * y) :=
    mul_comm_mem_of_isMulCommutative (D := D) hd2D hxyD
  have hcomm_inv : Commute d2 (x * y)⁻¹ := hcomm.inv_right
  have hz2 : (d2 * (x * y)⁻¹) * (d2 * (x * y)⁻¹) = 1 := by
    calc (d2 * (x * y)⁻¹) * (d2 * (x * y)⁻¹)
        = d2 * ((x * y)⁻¹ * d2) * (x * y)⁻¹ := by group
      _ = d2 * (d2 * (x * y)⁻¹) * (x * y)⁻¹ := by rw [hcomm_inv.eq.symm]
      _ = (d2 * d2) * ((x * y)⁻¹ * (x * y)⁻¹) := by group
      _ = (x ^ 2 * y ^ 2) * (((x * y) * (x * y))⁻¹) := by
            rw [hd2sq, ← mul_inv_rev]
      _ = (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2)⁻¹ := by rw [hxy_sq]
      _ = 1 := mul_inv_cancel _
  have hzA : d2 * (x * y)⁻¹ ∈ F.A :=
    h.mem_A_of_mul_self (D.mul_mem hd2D (D.inv_mem hxyD)) hz2
  have hd2_eq : d2 = (d2 * (x * y)⁻¹) * (x * y) := by group
  rw [hd2_eq]
  exact F.A.mul_mem hzA hxyA

theorem t310_d2_eq_xy {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t310 m hm)} (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2) =
        F.dA.toConfig.x * F.dA.toConfig.y ∨
      ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2) =
        (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2)
  let w : Torus (StrothTypeIndex.t310 m hm).k :=
    (2 ^ (m - 2) : ℕ) • (Torus.a + Torus.b)
  change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
    d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹
  have hd2A : d2 ∈ F.A := by
    simpa [d2] using t310_d2_mem_A (m := m) (dD := dD) hm h
  have hd2D : d2 ∈ D := by
    dsimp only [d2]
    exact D.pow_mem (D.mul_mem dD.a.2 dD.b.2) _
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t310_d2_ofTorus (m := m) (dD := dD)
  have hφu : (StrothTypeIndex.t310 m hm).action.φu w = w := by
    dsimp only [w]
    change (Type310.action m hm).φu
        ((2 ^ (m - 2) : ℕ) • (Torus.a (k := Type310.k m) +
          Torus.b (k := Type310.k m))) =
      (2 ^ (m - 2) : ℕ) • (Torus.a (k := Type310.k m) +
        Torus.b (k := Type310.k m))
    rw [map_nsmul, map_add, Type310.u_a m hm, Type310.u_b m hm, add_comm]
    simp
  have hφuv : (StrothTypeIndex.t310 m hm).action.φuv w = -w := by
    dsimp only [w]
    exact t310_φuv_ab_half (m := m) hm
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
      simpa [d2] using t310_d2_sq_eq (m := m) (dD := dD) hm h
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

theorem t310_isConj_uv_xyuv {F : StrothFrame G} {D : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    {dD : StrothWeakTypeData D (StrothTypeIndex.t310 m hm)} (h : F.IsD D dD) :
    IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv) := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ (m - 2)
  let w : Torus (StrothTypeIndex.t310 m hm).k :=
    (2 ^ (m - 2) : ℕ) • (Torus.a + Torus.b)
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t310_d2_ofTorus (m := m) (dD := dD)
  have hd2 : d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
    have h := t310_d2_eq_xy (m := m) (dD := dD) hm h
    change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ at h
    exact h
  obtain ⟨v, hv⟩ := t310_uv_preimage (m := m) hm
  have hφ : dD.ofTorus ((StrothTypeIndex.t310 m hm).action.φuv v - v) = d2 := by
    rw [hv]
    rw [hd2_ofT]
  exact isConj_uv_xyuv_of_d2 (τ := StrothTypeIndex.t310 m hm) h hd2 hφ

end StrothFrame.IsD

end CFSG.CGT.Stroth77
