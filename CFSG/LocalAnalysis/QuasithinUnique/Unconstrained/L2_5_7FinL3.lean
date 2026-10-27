module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverRoots
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aAut
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.QuasithinUnique.Fin257

namespace L3

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover

open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem xP_zero : xP (0 : F) = 1 := (xP_eq_one_iff 0).2 rfl

omit [CharP F 2] in
theorem yP_zero : yP (0 : F) = 1 := (yP_eq_one_iff 0).2 rfl

omit [CharP F 2] in
theorem wP_zero : wP (0 : F) = 1 := (wP_eq_one_iff 0).2 rfl

theorem xP_mul_self (a : F) : xP a * xP a = 1 := by
  rw [← xP_add, CharTwo.add_self_eq_zero, xP_zero]

theorem yP_mul_self (a : F) : yP a * yP a = 1 := by
  rw [← yP_add, CharTwo.add_self_eq_zero, yP_zero]

theorem wP_mul_self (a : F) : wP a * wP a = 1 := by
  rw [← wP_add, CharTwo.add_self_eq_zero, wP_zero]

@[expose] def V1 : Subgroup (projectiveSL 3 F) where
  carrier := {g | ∃ a c : F, g = xP a * wP c}
  one_mem' := ⟨0, 0, by rw [xP_zero, wP_zero, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
    refine ⟨a + a', c + c', ?_⟩
    rw [xP_add, wP_add]
    calc xP a * wP c * (xP a' * wP c') = xP a * (wP c * xP a') * wP c' := by group
      _ = xP a * (xP a' * wP c) * wP c' := by rw [wP_mul_xP]
      _ = xP a * xP a' * (wP c * wP c') := by group
  inv_mem' := by
    rintro _ ⟨a, c, rfl⟩
    refine ⟨a, c, ?_⟩
    rw [inv_eq_iff_mul_eq_one]
    calc xP a * wP c * (xP a * wP c) = xP a * (wP c * xP a) * wP c := by group
      _ = xP a * (xP a * wP c) * wP c := by rw [wP_mul_xP]
      _ = (xP a * xP a) * (wP c * wP c) := by group
      _ = 1 := by rw [xP_mul_self, wP_mul_self, one_mul]

@[expose] def V2 : Subgroup (projectiveSL 3 F) where
  carrier := {g | ∃ b c : F, g = yP b * wP c}
  one_mem' := ⟨0, 0, by rw [yP_zero, wP_zero, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
    refine ⟨a + a', c + c', ?_⟩
    rw [yP_add, wP_add]
    calc yP a * wP c * (yP a' * wP c') = yP a * (wP c * yP a') * wP c' := by group
      _ = yP a * (yP a' * wP c) * wP c' := by rw [wP_mul_yP]
      _ = yP a * yP a' * (wP c * wP c') := by group
  inv_mem' := by
    rintro _ ⟨a, c, rfl⟩
    refine ⟨a, c, ?_⟩
    rw [inv_eq_iff_mul_eq_one]
    calc yP a * wP c * (yP a * wP c) = yP a * (wP c * yP a) * wP c := by group
      _ = yP a * (yP a * wP c) * wP c := by rw [wP_mul_yP]
      _ = (yP a * yP a) * (wP c * wP c) := by group
      _ = 1 := by rw [yP_mul_self, wP_mul_self, one_mul]

@[expose] def Wg : Subgroup (projectiveSL 3 F) where
  carrier := {g | ∃ c : F, g = wP c}
  one_mem' := ⟨0, wP_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', by rw [wP_add]⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [inv_eq_iff_mul_eq_one, wP_mul_self]

theorem mem_V1 {g : projectiveSL 3 F} : g ∈ V1 ↔ ∃ a c : F, g = xP a * wP c := Iff.rfl

theorem mem_V2 {g : projectiveSL 3 F} : g ∈ V2 ↔ ∃ b c : F, g = yP b * wP c := Iff.rfl

theorem mem_Wg {g : projectiveSL 3 F} : g ∈ Wg ↔ ∃ c : F, g = wP c := Iff.rfl

theorem mem_Ubar {g : projectiveSL 3 F} :
    g ∈ projUnitriangular 3 F ↔ ∃ c a b : F, g = wP c * xP a * yP b := by
  constructor
  · intro hg
    obtain ⟨a, b, c, h⟩ := (projRoots (K := F)).mem_S g hg
    exact ⟨c, a, b, h⟩
  · rintro ⟨c, a, b, rfl⟩
    exact mul_mem (mul_mem ((projRoots (K := F)).w_mem c) ((projRoots (K := F)).x_mem a))
      ((projRoots (K := F)).y_mem b)

omit [CharP F 2] in
theorem V1_mul (a c a' c' : F) : (xP a * wP c) * (xP a' * wP c') = xP (a + a') * wP (c + c') := by
  rw [xP_add, wP_add]
  calc xP a * wP c * (xP a' * wP c') = xP a * (wP c * xP a') * wP c' := by group
    _ = xP a * (xP a' * wP c) * wP c' := by rw [wP_mul_xP]
    _ = xP a * xP a' * (wP c * wP c') := by group

omit [CharP F 2] in
theorem V2_mul (b c b' c' : F) : (yP b * wP c) * (yP b' * wP c') = yP (b + b') * wP (c + c') := by
  rw [yP_add, wP_add]
  calc yP b * wP c * (yP b' * wP c') = yP b * (wP c * yP b') * wP c' := by group
    _ = yP b * (yP b' * wP c) * wP c' := by rw [wP_mul_yP]
    _ = yP b * yP b' * (wP c * wP c') := by group

theorem V1_le_U : (V1 : Subgroup (projectiveSL 3 F)) ≤ projUnitriangular 3 F := by
  rintro _ ⟨a, c, rfl⟩
  exact mul_mem ((projRoots (K := F)).x_mem a) ((projRoots (K := F)).w_mem c)

theorem V2_le_U : (V2 : Subgroup (projectiveSL 3 F)) ≤ projUnitriangular 3 F := by
  rintro _ ⟨b, c, rfl⟩
  exact mul_mem ((projRoots (K := F)).y_mem b) ((projRoots (K := F)).w_mem c)

theorem Wg_le_V1 : (Wg : Subgroup (projectiveSL 3 F)) ≤ V1 := by
  rintro _ ⟨c, rfl⟩
  exact ⟨0, c, by rw [xP_zero, one_mul]⟩

theorem Wg_le_V2 : (Wg : Subgroup (projectiveSL 3 F)) ≤ V2 := by
  rintro _ ⟨c, rfl⟩
  exact ⟨0, c, by rw [yP_zero, one_mul]⟩

theorem U_eq_sup : (V1 : Subgroup (projectiveSL 3 F)) ⊔ V2 = projUnitriangular 3 F := by
  apply le_antisymm (sup_le V1_le_U V2_le_U)
  intro g hg
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hg
  have h1 : wP c * xP a ∈ (V1 : Subgroup (projectiveSL 3 F)) := ⟨a, c, by rw [wP_mul_xP]⟩
  have h2 : yP b ∈ (V2 : Subgroup (projectiveSL 3 F)) := ⟨b, 0, by rw [wP_zero, mul_one]⟩
  exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

theorem isElemAbelian_V1 : IsElemAbelian 2 (V1 : Subgroup (projectiveSL 3 F)) := by
  refine ⟨isMulCommutative_iff_of_setLike.mpr ?_, ?_⟩
  · rintro _ ⟨a, c, rfl⟩ _ ⟨a', c', rfl⟩
    rw [V1_mul, V1_mul, add_comm a, add_comm c]
  · rintro _ ⟨a, c, rfl⟩
    rw [pow_two, V1_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, xP_zero, wP_zero,
      one_mul]

theorem isElemAbelian_V2 : IsElemAbelian 2 (V2 : Subgroup (projectiveSL 3 F)) := by
  refine ⟨isMulCommutative_iff_of_setLike.mpr ?_, ?_⟩
  · rintro _ ⟨b, c, rfl⟩ _ ⟨b', c', rfl⟩
    rw [V2_mul, V2_mul, add_comm b, add_comm c]
  · rintro _ ⟨b, c, rfl⟩
    rw [pow_two, V2_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, yP_zero, wP_zero,
      one_mul]

omit [CharP F 2] in
theorem xP_wP_ne (a c c' : F) (ha : a ≠ 0) : xP a * wP c ≠ wP c' := by
  intro h
  have hU1 : xMat a * wMat c ∈ unitriangular 3 F :=
    mul_mem (xMat_mem_unitriangular a) (wMat_mem_unitriangular c)
  have hU2 : wMat c' ∈ unitriangular 3 F := wMat_mem_unitriangular c'
  have h' := LinearFlag.proj_injOn_unitriangular 3 hU1 hU2 h
  have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F) 0 1) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  change (xM a * wM c) 0 1 = (wM c') 0 1 at this
  simp [xM, wM, Matrix.mul_apply, Fin.sum_univ_three] at this
  exact ha this

omit [CharP F 2] in
theorem xP_wP_eq_yP_wP {a b c c' : F} (h : xP a * wP c = yP b * wP c') :
    a = 0 ∧ b = 0 ∧ c = c' := by
  have hU1 : xMat a * wMat c ∈ unitriangular 3 F :=
    mul_mem (xMat_mem_unitriangular a) (wMat_mem_unitriangular c)
  have hU2 : yMat b * wMat c' ∈ unitriangular 3 F :=
    mul_mem (yMat_mem_unitriangular b) (wMat_mem_unitriangular c')
  have hh : proj 3 F (xMat a * wMat c) = proj 3 F (yMat b * wMat c') := by
    rw [map_mul, map_mul]
    exact h
  have h' := LinearFlag.proj_injOn_unitriangular 3 hU1 hU2 hh
  have hm : (xM a * wM c) = (yM b * wM c') := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) F =>
      (X : Matrix (Fin 3) (Fin 3) F)) h'
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have e01 := congrFun (congrFun hm 0) 1
  have e12 := congrFun (congrFun hm 1) 2
  have e02 := congrFun (congrFun hm 0) 2
  simp [xM, wM, yM, Matrix.mul_apply, Fin.sum_univ_three] at e01 e12 e02
  exact ⟨e01, e12.symm, e02⟩

theorem V1_inf_V2 : (V1 : Subgroup (projectiveSL 3 F)) ⊓ V2 = Wg := by
  apply le_antisymm
  · rintro g ⟨⟨a, c, rfl⟩, ⟨b, c', hb⟩⟩
    obtain ⟨ha, -, -⟩ := xP_wP_eq_yP_wP hb
    exact ⟨c, by rw [ha, xP_zero, one_mul]⟩
  · exact le_inf Wg_le_V1 Wg_le_V2

theorem V1_ne_V2 : (V1 : Subgroup (projectiveSL 3 F)) ≠ V2 := by
  intro h
  have h1 : xP (1 : F) ∈ (V1 : Subgroup (projectiveSL 3 F)) := ⟨1, 0, by rw [wP_zero, mul_one]⟩
  rw [h] at h1
  obtain ⟨b, c, hb⟩ := h1
  have := xP_wP_eq_yP_wP (a := (1 : F)) (c := 0) (b := b) (c' := c) (by rw [wP_zero, mul_one, hb])
  exact one_ne_zero this.1

theorem V2_not_le_centralizer_V1 :
    ¬ (V2 : Subgroup (projectiveSL 3 F)) ≤ Subgroup.centralizer ((V1 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
  intro h
  have hy : yP (1 : F) ∈ (V2 : Subgroup (projectiveSL 3 F)) := ⟨1, 0, by rw [wP_zero, mul_one]⟩
  have hx : xP (1 : F) ∈ (V1 : Subgroup (projectiveSL 3 F)) := ⟨1, 0, by rw [wP_zero, mul_one]⟩
  have hc := Subgroup.mem_centralizer_iff.mp (h hy) (xP 1) hx
  have : ⁅xP (1 : F), yP (1 : F)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
  rw [commutatorElement_xP_yP, one_mul, wP_eq_one_iff] at this
  exact one_ne_zero this

theorem Wg_le_commutator :
    (V1 : Subgroup (projectiveSL 3 F)) ⊓ V2 ≤ ⁅(V1 : Subgroup (projectiveSL 3 F)), V2⁆ := by
  rw [V1_inf_V2]
  rintro _ ⟨c, rfl⟩
  have h1 : xP c ∈ (V1 : Subgroup (projectiveSL 3 F)) := ⟨c, 0, by rw [wP_zero (F := F), mul_one]⟩
  have h2 : yP (1 : F) ∈ (V2 : Subgroup (projectiveSL 3 F)) :=
    ⟨1, 0, by rw [wP_zero (F := F), mul_one]⟩
  have := Subgroup.commutator_mem_commutator h1 h2
  rwa [commutatorElement_xP_yP, mul_one] at this

omit [CharP F 2] in
theorem comm_of_proj_comm_of_sq {A B : Matrix.SpecialLinearGroup (Fin 3) F} (hB : B * B = 1)
    (h : proj 3 F A * proj 3 F B = proj 3 F B * proj 3 F A) : A * B = B * A := by
  have hp : proj 3 F (A * B) = proj 3 F (B * A) := by rw [map_mul, map_mul]; exact h
  have hs : (A * B)⁻¹ * (B * A) ∈ scalars 3 F := proj_eq_proj_iff.mp hp
  set s := (A * B)⁻¹ * (B * A) with hsdef
  have hcen : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, g * s = s * g := fun g =>
    Subgroup.mem_center_iff.mp (scalars_le_center 3 F hs) g
  have h1 : A⁻¹ * B * A = B * s := by rw [hsdef]; group
  have h2 : (A⁻¹ * B * A) * (A⁻¹ * B * A) = 1 := by
    calc (A⁻¹ * B * A) * (A⁻¹ * B * A) = A⁻¹ * (B * B) * A := by group
      _ = 1 := by rw [hB]; group
  have h3 : s * s = 1 := by
    have : (B * s) * (B * s) = s * s := by
      calc (B * s) * (B * s) = B * (s * B) * s := by group
        _ = B * (B * s) * s := by rw [← hcen B]
        _ = (B * B) * (s * s) := by group
        _ = s * s := by rw [hB, one_mul]
    rw [← this, ← h1]
    exact h2
  obtain ⟨c, hc3, hc⟩ := mem_scalars.mp hs
  have hcc : c * c = 1 := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) F =>
      (X : Matrix (Fin 3) (Fin 3) F) 0 0) h3
    simp only [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.scalar_apply,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at this
    exact Units.ext this
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, hcc]; simp
  have hs1 : s = 1 := by
    apply Subtype.ext
    rw [hc, hc1]
    simp
  rw [hsdef] at hs1
  exact (inv_mul_eq_one.mp hs1)

omit [CharP F 2] in
theorem xMat_zero : xMat (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xMat, xM]

omit [CharP F 2] in
theorem yMat_zero : yMat (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [yMat, yM]

omit [CharP F 2] in
theorem wMat_zero : wMat (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, wM]

theorem xMat_one_mul_self : (xMat (1 : F)) * xMat 1 = 1 := by
  rw [← xMat_add, CharTwo.add_self_eq_zero, xMat_zero]

theorem yMat_one_mul_self : (yMat (1 : F)) * yMat 1 = 1 := by
  rw [← yMat_add, CharTwo.add_self_eq_zero, yMat_zero]

theorem wMat_one_mul_self : (wMat (1 : F)) * wMat 1 = 1 := by
  rw [← wMat_add, CharTwo.add_self_eq_zero, wMat_zero]

omit [CharP F 2] in
theorem entries_comm_x {A : Matrix.SpecialLinearGroup (Fin 3) F} (h : A * xMat 1 = xMat 1 * A) :
    (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
  have hm : (A : Matrix (Fin 3) (Fin 3) F) * xM (1 : F) =
      xM (1 : F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) F =>
      (X : Matrix (Fin 3) (Fin 3) F)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have e00 := congrFun (congrFun hm 0) 0
  have e21 := congrFun (congrFun hm 2) 1
  have e01 := congrFun (congrFun hm 0) 1
  have e02 := congrFun (congrFun hm 0) 2
  simp [xM, Matrix.mul_apply, Fin.sum_univ_three] at e00 e21 e01 e02
  exact ⟨e00, e21, e02, by linear_combination (-1 : F) * e01⟩

omit [CharP F 2] in
theorem entries_comm_w {A : Matrix.SpecialLinearGroup (Fin 3) F} (h : A * wMat 1 = wMat 1 * A) :
    (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
  have hm : (A : Matrix (Fin 3) (Fin 3) F) * wM (1 : F) =
      wM (1 : F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) F =>
      (X : Matrix (Fin 3) (Fin 3) F)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e02 := congrFun (congrFun hm 0) 2
  have e12 := congrFun (congrFun hm 1) 2
  simp [wM, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e12
  exact ⟨e00, e01, e12, by linear_combination (-1 : F) * e02⟩

omit [CharP F 2] in
theorem entries_comm_y {A : Matrix.SpecialLinearGroup (Fin 3) F} (h : A * yMat 1 = yMat 1 * A) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 1 1 := by
  have hm : (A : Matrix (Fin 3) (Fin 3) F) * yM (1 : F) =
      yM (1 : F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) F =>
      (X : Matrix (Fin 3) (Fin 3) F)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have e02 := congrFun (congrFun hm 0) 2
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  have e12 := congrFun (congrFun hm 1) 2
  simp [yM, Matrix.mul_apply, Fin.sum_univ_three] at e02 e10 e11 e12
  exact ⟨e02, e10, e11, by linear_combination (-1 : F) * e12⟩

omit [CharP F 2] in
theorem det_eq_cube {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h12 : (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h11 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 3 = 1 := by
  have := A.2
  rw [Matrix.det_fin_three] at this
  rw [h10, h20, h21, h12, h11, h22] at this
  linear_combination this

omit [CharP F 2] in
theorem exists_scalar_mul {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (hl : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 3 = 1) :
    ∃ c : Fˣ, c ^ 3 = 1 ∧ (c : F) = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
  have h0 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
    intro h
    rw [h] at hl
    simp at hl
  refine ⟨Units.mk0 _ h0, ?_, rfl⟩
  apply Units.ext
  simpa using hl

theorem proj_mem_V1_of_entries {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h12 : (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h11 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0) :
    proj 3 F A ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨c, hc, hcA⟩ := exists_scalar_mul (det_eq_cube h10 h20 h21 h12 h11 h22)
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hA00 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := hcA ▸ hc0
  refine ⟨(A : Matrix (Fin 3) (Fin 3) F) 0 1 / c, (A : Matrix (Fin 3) (Fin 3) F) 0 2 / c, ?_⟩
  have hA : A = scalarElement c hc * (xMat ((A : Matrix (Fin 3) (Fin 3) F) 0 1 / c) *
      wMat ((A : Matrix (Fin 3) (Fin 3) F) 0 2 / c)) := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement]
    change (A : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (c : F) *
      (xM ((A : Matrix (Fin 3) (Fin 3) F) 0 1 / c) * wM ((A : Matrix (Fin 3) (Fin 3) F) 0 2 / c))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [xM, wM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, hcA, h10, h20,
        h21, h12, h11, h22] <;> field_simp
  have : proj 3 F A = proj 3 F (xMat ((A : Matrix (Fin 3) (Fin 3) F) 0 1 / c) *
      wMat ((A : Matrix (Fin 3) (Fin 3) F) 0 2 / c)) := by
    conv_lhs => rw [hA]
    rw [map_mul, (proj_eq_one_iff).mpr (scalarElement_mem_scalars c hc), one_mul]
  rw [this, map_mul]
  rfl

omit [CharP F 2] in
theorem det_eq_cube₂ {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (h11 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 3 = 1 := by
  have := A.2
  rw [Matrix.det_fin_three] at this
  rw [h10, h20, h21, h01, h11, h22] at this
  linear_combination this

theorem proj_mem_V2_of_entries {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (h11 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0) :
    proj 3 F A ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨c, hc, hcA⟩ := exists_scalar_mul (det_eq_cube₂ h10 h20 h21 h01 h11 h22)
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hA00 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := hcA ▸ hc0
  refine ⟨(A : Matrix (Fin 3) (Fin 3) F) 1 2 / c, (A : Matrix (Fin 3) (Fin 3) F) 0 2 / c, ?_⟩
  have hA : A = scalarElement c hc * (yMat ((A : Matrix (Fin 3) (Fin 3) F) 1 2 / c) *
      wMat ((A : Matrix (Fin 3) (Fin 3) F) 0 2 / c)) := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement]
    change (A : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (c : F) *
      (yM ((A : Matrix (Fin 3) (Fin 3) F) 1 2 / c) * wM ((A : Matrix (Fin 3) (Fin 3) F) 0 2 / c))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [yM, wM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, hcA, h10, h20,
        h21, h01, h11, h22] <;> field_simp
  have : proj 3 F A = proj 3 F (yMat ((A : Matrix (Fin 3) (Fin 3) F) 1 2 / c) *
      wMat ((A : Matrix (Fin 3) (Fin 3) F) 0 2 / c)) := by
    conv_lhs => rw [hA]
    rw [map_mul, (proj_eq_one_iff).mpr (scalarElement_mem_scalars c hc), one_mul]
  rw [this, map_mul]
  rfl

theorem cent_V1 (g : projectiveSL 3 F)
    (hg : ∀ r ∈ (V1 : Subgroup (projectiveSL 3 F)), g * r = r * g) :
    g ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨A, rfl⟩ := proj_surjective 3 F g
  have hx : proj 3 F A * proj 3 F (xMat 1) = proj 3 F (xMat 1) * proj 3 F A :=
    hg (xP 1) ⟨1, 0, by rw [wP_zero (F := F), mul_one]⟩
  have hw : proj 3 F A * proj 3 F (wMat 1) = proj 3 F (wMat 1) * proj 3 F A :=
    hg (wP 1) ⟨0, 1, by rw [xP_zero (F := F), one_mul]⟩
  have hAx := comm_of_proj_comm_of_sq xMat_one_mul_self hx
  have hAw := comm_of_proj_comm_of_sq wMat_one_mul_self hw
  obtain ⟨h10, h20, h12, h11⟩ := entries_comm_x hAx
  obtain ⟨-, h21, -, h22⟩ := entries_comm_w hAw
  exact proj_mem_V1_of_entries h10 h20 h21 h12 h11 h22

theorem cent_V2 (g : projectiveSL 3 F)
    (hg : ∀ r ∈ (V2 : Subgroup (projectiveSL 3 F)), g * r = r * g) :
    g ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨A, rfl⟩ := proj_surjective 3 F g
  have hy : proj 3 F A * proj 3 F (yMat 1) = proj 3 F (yMat 1) * proj 3 F A :=
    hg (yP 1) ⟨1, 0, by rw [wP_zero (F := F), mul_one]⟩
  have hw : proj 3 F A * proj 3 F (wMat 1) = proj 3 F (wMat 1) * proj 3 F A :=
    hg (wP 1) ⟨0, 1, by rw [yP_zero (F := F), one_mul]⟩
  have hAy := comm_of_proj_comm_of_sq yMat_one_mul_self hy
  have hAw := comm_of_proj_comm_of_sq wMat_one_mul_self hw
  obtain ⟨h01, h20, h21, h22⟩ := entries_comm_y hAy
  obtain ⟨-, -, h10, h22'⟩ := entries_comm_w hAw
  exact proj_mem_V2_of_entries h10 h20 h21 h01 (by rw [← h22', h22]) h22'

theorem mem_normalizer_of_conj {G : Type*} [Group G] (H : Subgroup G) {g : G}
    (h : ∀ v ∈ H, g * v * g⁻¹ ∈ H) (h' : ∀ v ∈ H, g⁻¹ * v * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨h v, fun hv => ?_⟩
  have := h' _ hv
  simpa [mul_assoc] using this

theorem yP_mul_xP (a b : F) : yP b * xP a = wP (a * b) * xP a * yP b := by
  have h : xP a * yP b = wP (a * b) * yP b * xP a := (projRoots (K := F)).x_mul_y a b
  have hw : wP (a * b) * wP (a * b) = 1 := wP_mul_self _
  calc yP b * xP a = (wP (a * b) * wP (a * b)) * (yP b * xP a) := by rw [hw, one_mul]
    _ = wP (a * b) * (wP (a * b) * yP b * xP a) := by group
    _ = wP (a * b) * (xP a * yP b) := by rw [← h]
    _ = wP (a * b) * xP a * yP b := by group

theorem yP_conj_xP (a b : F) : yP b * xP a * (yP b)⁻¹ = xP a * wP (a * b) := by
  rw [yP_mul_xP]
  calc wP (a * b) * xP a * yP b * (yP b)⁻¹ = wP (a * b) * xP a := by group
    _ = xP a * wP (a * b) := by rw [wP_mul_xP]

theorem xP_conj_yP (a b : F) : xP a * yP b * (xP a)⁻¹ = wP (a * b) * yP b := by
  have h : xP a * yP b = wP (a * b) * yP b * xP a := (projRoots (K := F)).x_mul_y a b
  rw [h]
  group

theorem yP_inv (b : F) : (yP b)⁻¹ = yP b := inv_eq_of_mul_eq_one_right (yP_mul_self b)
theorem xP_inv (a : F) : (xP a)⁻¹ = xP a := inv_eq_of_mul_eq_one_right (xP_mul_self a)
theorem wP_inv (c : F) : (wP c)⁻¹ = wP c := inv_eq_of_mul_eq_one_right (wP_mul_self c)

theorem yP_mem_normalizer_V1 (b : F) :
    yP b ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ v ∈ (V1 : Subgroup (projectiveSL 3 F)), yP b * v * (yP b)⁻¹ ∈ V1 := by
    rintro _ ⟨a, c, rfl⟩
    refine ⟨a, a * b + c, ?_⟩
    have e1 : yP b * (xP a * wP c) * (yP b)⁻¹ =
        (yP b * xP a * (yP b)⁻¹) * (yP b * wP c * (yP b)⁻¹) := by group
    rw [e1, yP_conj_xP, ← wP_mul_yP c b, mul_assoc (wP c), mul_inv_cancel, mul_one, wP_add]
    group
  exact mem_normalizer_of_conj _ key (by rw [yP_inv]; simpa [yP_inv] using key)

theorem xP_mem_normalizer_V2 (a : F) :
    xP a ∈ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ v ∈ (V2 : Subgroup (projectiveSL 3 F)), xP a * v * (xP a)⁻¹ ∈ V2 := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨b, a * b + c, ?_⟩
    have e1 : xP a * (yP b * wP c) * (xP a)⁻¹ =
        (xP a * yP b * (xP a)⁻¹) * (xP a * wP c * (xP a)⁻¹) := by group
    have e2 : xP a * wP c * (xP a)⁻¹ = wP c := by rw [← wP_mul_xP c a]; group
    rw [e1, xP_conj_yP, e2]
    calc wP (a * b) * yP b * wP c = yP b * wP (a * b) * wP c := by rw [wP_mul_yP]
      _ = yP b * (wP (a * b) * wP c) := by group
      _ = yP b * wP (a * b + c) := by rw [wP_add]
  exact mem_normalizer_of_conj _ key (by rw [xP_inv]; simpa [xP_inv] using key)

theorem U_le_normalizer_V1 : projUnitriangular 3 F ≤
    Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  intro g hg
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hg
  refine mul_mem (mul_mem ?_ ?_) (yP_mem_normalizer_V1 b)
  · exact Subgroup.le_normalizer (⟨0, c, by rw [xP_zero (F := F), one_mul]⟩ :
      wP c ∈ (V1 : Subgroup (projectiveSL 3 F)))
  · exact Subgroup.le_normalizer (⟨a, 0, by rw [wP_zero (F := F), mul_one]⟩ :
      xP a ∈ (V1 : Subgroup (projectiveSL 3 F)))

theorem U_le_normalizer_V2 : projUnitriangular 3 F ≤
    Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  intro g hg
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hg
  refine mul_mem (mul_mem ?_ (xP_mem_normalizer_V2 a)) ?_
  · exact Subgroup.le_normalizer (⟨0, c, by rw [yP_zero (F := F), one_mul]⟩ :
      wP c ∈ (V2 : Subgroup (projectiveSL 3 F)))
  · exact Subgroup.le_normalizer (⟨b, 0, by rw [wP_zero (F := F), mul_one]⟩ :
      yP b ∈ (V2 : Subgroup (projectiveSL 3 F)))

omit [CharP F 2] in
theorem diag_ne_zero {d : Matrix.SpecialLinearGroup (Fin 3) F}
    (hd : Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F)) (i : Fin 3) :
    (d : Matrix (Fin 3) (Fin 3) F) i i ≠ 0 := by
  have h1 : (d : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun i => (d : Matrix (Fin 3) (Fin 3) F) i i) :=
    (Matrix.IsDiag.diagonal_diag hd).symm
  have h2 := d.2
  rw [h1, Matrix.det_diagonal, Fin.prod_univ_three] at h2
  intro h
  fin_cases i <;> simp at h <;> simp [h] at h2

omit [CharP F 2] in
theorem isDiag_inv {d : Matrix.SpecialLinearGroup (Fin 3) F}
    (hd : Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F)) :
    Matrix.IsDiag ((d⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  have h1 : (d : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun i => (d : Matrix (Fin 3) (Fin 3) F) i i) :=
    (Matrix.IsDiag.diagonal_diag hd).symm
  rw [h1, Matrix.adjugate_diagonal]
  exact Matrix.isDiag_diagonal _

omit [CharP F 2] in
theorem diag_offdiag {d : Matrix.SpecialLinearGroup (Fin 3) F}
    (hd : Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F)) :
    (d : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (d : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
    (d : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (d : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
    (d : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (d : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 :=
  ⟨hd (by decide), hd (by decide), hd (by decide), hd (by decide), hd (by decide),
    hd (by decide)⟩

omit [CharP F 2] in
theorem diag_mul_xMat {d : Matrix.SpecialLinearGroup (Fin 3) F}
    (hd : Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F)) (a : F) :
    ∃ a' : F, d * xMat a = xMat a' * d := by
  have h1 := diag_ne_zero hd 1
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ := diag_offdiag hd
  refine ⟨(d : Matrix (Fin 3) (Fin 3) F) 0 0 * ((d : Matrix (Fin 3) (Fin 3) F) 1 1)⁻¹ * a, ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change (d : Matrix (Fin 3) (Fin 3) F) * xM a = xM _ * (d : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xM, Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21]
  field_simp

omit [CharP F 2] in
theorem diag_mul_yMat {d : Matrix.SpecialLinearGroup (Fin 3) F}
    (hd : Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F)) (b : F) :
    ∃ b' : F, d * yMat b = yMat b' * d := by
  have h1 := diag_ne_zero hd 2
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ := diag_offdiag hd
  refine ⟨(d : Matrix (Fin 3) (Fin 3) F) 1 1 * ((d : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ * b, ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change (d : Matrix (Fin 3) (Fin 3) F) * yM b = yM _ * (d : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yM, Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21]
  field_simp

omit [CharP F 2] in
theorem diag_mul_wMat {d : Matrix.SpecialLinearGroup (Fin 3) F}
    (hd : Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F)) (c : F) :
    ∃ c' : F, d * wMat c = wMat c' * d := by
  have h1 := diag_ne_zero hd 2
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ := diag_offdiag hd
  refine ⟨(d : Matrix (Fin 3) (Fin 3) F) 0 0 * ((d : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ * c, ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change (d : Matrix (Fin 3) (Fin 3) F) * wM c = wM _ * (d : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21]
  field_simp

theorem proj_diag_mem_normalizer_V1 {d : Matrix.SpecialLinearGroup (Fin 3) F}
    (hd : Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F)) :
    proj 3 F d ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ d : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F) →
      ∀ v ∈ (V1 : Subgroup (projectiveSL 3 F)), proj 3 F d * v * (proj 3 F d)⁻¹ ∈ V1 := by
    intro d hd
    rintro _ ⟨a, c, rfl⟩
    obtain ⟨a', ha'⟩ := diag_mul_xMat hd a
    obtain ⟨c', hc'⟩ := diag_mul_wMat hd c
    refine ⟨a', c', ?_⟩
    have hx : proj 3 F d * xP a * (proj 3 F d)⁻¹ = xP a' := by
      have : proj 3 F d * xP a = xP a' * proj 3 F d := by
        have := congrArg (proj 3 F) ha'
        rwa [map_mul, map_mul] at this
      rw [this]
      group
    have hw : proj 3 F d * wP c * (proj 3 F d)⁻¹ = wP c' := by
      have : proj 3 F d * wP c = wP c' * proj 3 F d := by
        have := congrArg (proj 3 F) hc'
        rwa [map_mul, map_mul] at this
      rw [this]
      group
    calc proj 3 F d * (xP a * wP c) * (proj 3 F d)⁻¹ =
        (proj 3 F d * xP a * (proj 3 F d)⁻¹) * (proj 3 F d * wP c * (proj 3 F d)⁻¹) := by group
      _ = xP a' * wP c' := by rw [hx, hw]
  refine mem_normalizer_of_conj _ (key d hd) fun v hv => ?_
  have := key d⁻¹ (isDiag_inv hd) v hv
  simpa [map_inv] using this

theorem proj_diag_mem_normalizer_V2 {d : Matrix.SpecialLinearGroup (Fin 3) F}
    (hd : Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F)) :
    proj 3 F d ∈ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ d : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.IsDiag (d : Matrix (Fin 3) (Fin 3) F) →
      ∀ v ∈ (V2 : Subgroup (projectiveSL 3 F)), proj 3 F d * v * (proj 3 F d)⁻¹ ∈ V2 := by
    intro d hd
    rintro _ ⟨b, c, rfl⟩
    obtain ⟨b', hb'⟩ := diag_mul_yMat hd b
    obtain ⟨c', hc'⟩ := diag_mul_wMat hd c
    refine ⟨b', c', ?_⟩
    have hy : proj 3 F d * yP b * (proj 3 F d)⁻¹ = yP b' := by
      have : proj 3 F d * yP b = yP b' * proj 3 F d := by
        have := congrArg (proj 3 F) hb'
        rwa [map_mul, map_mul] at this
      rw [this]
      group
    have hw : proj 3 F d * wP c * (proj 3 F d)⁻¹ = wP c' := by
      have : proj 3 F d * wP c = wP c' * proj 3 F d := by
        have := congrArg (proj 3 F) hc'
        rwa [map_mul, map_mul] at this
      rw [this]
      group
    calc proj 3 F d * (yP b * wP c) * (proj 3 F d)⁻¹ =
        (proj 3 F d * yP b * (proj 3 F d)⁻¹) * (proj 3 F d * wP c * (proj 3 F d)⁻¹) := by group
      _ = yP b' * wP c' := by rw [hy, hw]
  refine mem_normalizer_of_conj _ (key d hd) fun v hv => ?_
  have := key d⁻¹ (isDiag_inv hd) v hv
  simpa [map_inv] using this

theorem normalizer_U_le_normalizer_V1 [Finite F] :
    Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) ≤
    Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(sylow_normalizers (K := F) (n := 3) 2 (by norm_num)).2.1]
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := CFSG.QuasithinUnique.Setup.X7a.exists_unitriangular_mul_diagonal hB
  rw [map_mul]
  exact mul_mem (U_le_normalizer_V1 (Subgroup.mem_map_of_mem _ hu)) (proj_diag_mem_normalizer_V1 hd)

theorem normalizer_U_le_normalizer_V2 [Finite F] :
    Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) ≤
    Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(sylow_normalizers (K := F) (n := 3) 2 (by norm_num)).2.1]
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := CFSG.QuasithinUnique.Setup.X7a.exists_unitriangular_mul_diagonal hB
  rw [map_mul]
  exact mul_mem (U_le_normalizer_V2 (Subgroup.mem_map_of_mem _ hu)) (proj_diag_mem_normalizer_V2 hd)

@[expose] def zMat (b : F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, b, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def vMat (a : F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; a, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

omit [CharP F 2] in
theorem coe_zMat (b : F) :
    (zMat b : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 1, 0; 0, b, 1] := rfl

omit [CharP F 2] in
theorem coe_vMat (a : F) :
    (vMat a : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; a, 1, 0; 0, 0, 1] := rfl

theorem s23Mat_mul_yMat_mul_s23Mat (b : F) : s₂₃Mat * yMat b * s₂₃Mat = zMat b := by
  apply Subtype.ext
  change (s₂₃M : Matrix (Fin 3) (Fin 3) F) * yM b * s₂₃M = !![1, 0, 0; 0, 1, 0; 0, b, 1]
  simp only [s₂₃M, yM, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem s12Mat_mul_xMat_mul_s12Mat (a : F) : s₁₂Mat * xMat a * s₁₂Mat = vMat a := by
  apply Subtype.ext
  change (s₁₂M : Matrix (Fin 3) (Fin 3) F) * xM a * s₁₂M = !![1, 0, 0; a, 1, 0; 0, 0, 1]
  simp only [s₁₂M, xM, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [CharP F 2] in
theorem exists_smul_of_proj_eq {A B : Matrix.SpecialLinearGroup (Fin 3) F}
    (h : proj 3 F A = proj 3 F B) :
    ∃ c : F, c ≠ 0 ∧ (B : Matrix (Fin 3) (Fin 3) F) = c • (A : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨c, hc, hA⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h)
  refine ⟨c, c.ne_zero, ?_⟩
  have h0 : A * (A⁻¹ * B) = B := mul_inv_cancel_left A B
  have h1 : ((A * (A⁻¹ * B) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ * B : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := Matrix.SpecialLinearGroup.coe_mul A (A⁻¹ * B)
  rw [h0] at h1
  rw [h1, hA]
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

omit [CharP F 2] in
theorem proj_zMat_not_mem_U {b : F} (hb : b ≠ 0) :
    proj 3 F (zMat b) ∉ projUnitriangular 3 F := by
  rintro ⟨u, hu, hu'⟩
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_proj_eq hu'
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp hu
  have e00 := congrFun (congrFun hc 0) 0
  have e21 := congrFun (congrFun hc 2) 1
  rw [coe_zMat] at e00 e21
  simp [hd 0, hl 2 1 (by decide)] at e00 e21
  exact hb e21

omit [CharP F 2] in
theorem proj_vMat_not_mem_U {a : F} (ha : a ≠ 0) :
    proj 3 F (vMat a) ∉ projUnitriangular 3 F := by
  rintro ⟨u, hu, hu'⟩
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_proj_eq hu'
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp hu
  have e00 := congrFun (congrFun hc 0) 0
  have e10 := congrFun (congrFun hc 1) 0
  rw [coe_vMat] at e00 e10
  simp [hd 0, hl 1 0 (by decide)] at e00 e10
  exact ha e10

theorem s23P_mul_self : (s₂₃P : projectiveSL 3 F) * s₂₃P = 1 := by
  calc (s₂₃P : projectiveSL 3 F) * s₂₃P = s₂₃P * s₂₃P⁻¹ := by rw [s₂₃P_inv]
    _ = 1 := mul_inv_cancel _

theorem s12P_mul_self : (s₁₂P : projectiveSL 3 F) * s₁₂P = 1 := by
  calc (s₁₂P : projectiveSL 3 F) * s₁₂P = s₁₂P * s₁₂P⁻¹ := by rw [s₁₂P_inv]
    _ = 1 := mul_inv_cancel _

theorem s23P_conj_xP' (a : F) : s₂₃P * xP a * s₂₃P⁻¹ = wP a := by
  have h := s₂₃P_conj_xP (k := F) a
  rw [s₂₃P_inv] at h
  rw [s₂₃P_inv]
  exact h

theorem s23P_conj_wP' (c : F) : s₂₃P * wP c * s₂₃P⁻¹ = xP c := by
  have h := s23P_conj_xP' (F := F) c
  rw [← h]
  calc (s₂₃P : projectiveSL 3 F) * (s₂₃P * xP c * s₂₃P⁻¹) * s₂₃P⁻¹ =
      (s₂₃P * s₂₃P) * xP c * (s₂₃P⁻¹ * s₂₃P⁻¹) := by group
    _ = xP c := by rw [s23P_mul_self, ← mul_inv_rev, s23P_mul_self]; simp

theorem s12P_conj_yP' (b : F) : s₁₂P * yP b * s₁₂P⁻¹ = wP b := by
  have h := s₁₂P_conj_yP (k := F) b
  rw [s₁₂P_inv] at h
  rw [s₁₂P_inv]
  exact h

theorem s12P_conj_wP' (c : F) : s₁₂P * wP c * s₁₂P⁻¹ = yP c := by
  have h := s12P_conj_yP' (F := F) c
  rw [← h]
  calc (s₁₂P : projectiveSL 3 F) * (s₁₂P * yP c * s₁₂P⁻¹) * s₁₂P⁻¹ =
      (s₁₂P * s₁₂P) * yP c * (s₁₂P⁻¹ * s₁₂P⁻¹) := by group
    _ = yP c := by rw [s12P_mul_self, ← mul_inv_rev, s12P_mul_self]; simp

theorem s23P_conj_yP' (b : F) : s₂₃P * yP b * s₂₃P⁻¹ = proj 3 F (zMat b) := by
  rw [s₂₃P_inv, s₂₃P, yP, ← map_mul, ← map_mul, s23Mat_mul_yMat_mul_s23Mat]

theorem s12P_conj_xP' (a : F) : s₁₂P * xP a * s₁₂P⁻¹ = proj 3 F (vMat a) := by
  rw [s₁₂P_inv, s₁₂P, xP, ← map_mul, ← map_mul, s12Mat_mul_xMat_mul_s12Mat]

theorem s23P_mem_normalizer_V1 : (s₂₃P : projectiveSL 3 F) ∈
    Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ v ∈ (V1 : Subgroup (projectiveSL 3 F)), s₂₃P * v * s₂₃P⁻¹ ∈ V1 := by
    rintro _ ⟨a, c, rfl⟩
    refine ⟨c, a, ?_⟩
    calc (s₂₃P : projectiveSL 3 F) * (xP a * wP c) * s₂₃P⁻¹ =
        (s₂₃P * xP a * s₂₃P⁻¹) * (s₂₃P * wP c * s₂₃P⁻¹) := by group
      _ = xP c * wP a := by rw [s23P_conj_xP', s23P_conj_wP', wP_mul_xP]
  refine mem_normalizer_of_conj _ key fun v hv => ?_
  have := key v hv
  rw [s₂₃P_inv] at this ⊢
  exact this

theorem s12P_mem_normalizer_V2 : (s₁₂P : projectiveSL 3 F) ∈
    Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ v ∈ (V2 : Subgroup (projectiveSL 3 F)), s₁₂P * v * s₁₂P⁻¹ ∈ V2 := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨c, b, ?_⟩
    calc (s₁₂P : projectiveSL 3 F) * (yP b * wP c) * s₁₂P⁻¹ =
        (s₁₂P * yP b * s₁₂P⁻¹) * (s₁₂P * wP c * s₁₂P⁻¹) := by group
      _ = yP c * wP b := by rw [s12P_conj_yP', s12P_conj_wP', wP_mul_yP]
  refine mem_normalizer_of_conj _ key fun v hv => ?_
  have := key v hv
  rw [s₁₂P_inv] at this ⊢
  exact this

theorem s23P_not_mem_normalizer_U : (s₂₃P : projectiveSL 3 F) ∉
    Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
  intro h
  have := (Subgroup.mem_normalizer_iff.mp h (yP 1)).mp ((projRoots (K := F)).y_mem 1)
  rw [s23P_conj_yP'] at this
  exact proj_zMat_not_mem_U one_ne_zero this

theorem s12P_not_mem_normalizer_U : (s₁₂P : projectiveSL 3 F) ∉
    Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
  intro h
  have := (Subgroup.mem_normalizer_iff.mp h (xP 1)).mp ((projRoots (K := F)).x_mem 1)
  rw [s12P_conj_xP'] at this
  exact proj_vMat_not_mem_U one_ne_zero this

theorem s12P_not_mem_normalizer_V1 : (s₁₂P : projectiveSL 3 F) ∉
    Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  intro h
  have h1 : xP (1 : F) ∈ (V1 : Subgroup (projectiveSL 3 F)) :=
    ⟨1, 0, by rw [wP_zero (F := F), mul_one]⟩
  have := (Subgroup.mem_normalizer_iff.mp h (xP 1)).mp h1
  rw [s12P_conj_xP'] at this
  exact proj_vMat_not_mem_U one_ne_zero (V1_le_U this)

theorem s23P_not_mem_normalizer_V2 : (s₂₃P : projectiveSL 3 F) ∉
    Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  intro h
  have h1 : yP (1 : F) ∈ (V2 : Subgroup (projectiveSL 3 F)) :=
    ⟨1, 0, by rw [wP_zero (F := F), mul_one]⟩
  have := (Subgroup.mem_normalizer_iff.mp h (yP 1)).mp h1
  rw [s23P_conj_yP'] at this
  exact proj_zMat_not_mem_U one_ne_zero (V2_le_U this)

theorem lt_normalizer_V1 [Finite F] : Subgroup.normalizer ((projUnitriangular 3 F :
    Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) <
    Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) :=
  lt_of_le_of_ne normalizer_U_le_normalizer_V1
    fun h => s23P_not_mem_normalizer_U (h ▸ s23P_mem_normalizer_V1)

theorem lt_normalizer_V2 [Finite F] : Subgroup.normalizer ((projUnitriangular 3 F :
    Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) <
    Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) :=
  lt_of_le_of_ne normalizer_U_le_normalizer_V2
    fun h => s12P_not_mem_normalizer_U (h ▸ s12P_mem_normalizer_V2)

theorem normalizer_V1_lt_top : Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) :
    Set (projectiveSL 3 F)) < ⊤ :=
  lt_top_iff_ne_top.mpr fun h => s12P_not_mem_normalizer_V1 (by rw [h]; exact Subgroup.mem_top _)

theorem normalizer_V2_lt_top : Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) :
    Set (projectiveSL 3 F)) < ⊤ :=
  lt_top_iff_ne_top.mpr fun h => s23P_not_mem_normalizer_V2 (by rw [h]; exact Subgroup.mem_top _)

theorem isPGroup_V1 : IsPGroup 2 (V1 : Subgroup (projectiveSL 3 F)) :=
  fun x => ⟨1, Subtype.ext (by simpa using (isElemAbelian_V1 (F := F)).2 _ x.2)⟩

theorem isPGroup_V2 : IsPGroup 2 (V2 : Subgroup (projectiveSL 3 F)) :=
  fun x => ⟨1, Subtype.ext (by simpa using (isElemAbelian_V2 (F := F)).2 _ x.2)⟩

theorem isSylowTwoOf_U [Finite F] :
    IsSylowTwoOf (projUnitriangular 3 F) (⊤ : Subgroup (projectiveSL 3 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  refine ⟨le_top, hP ▸ P.isPGroup', ?_⟩
  have h := Sylow.not_dvd_index P
  rw [hP] at h
  change ¬ 2 ∣ (projUnitriangular 3 F).relIndex ⊤
  rwa [Subgroup.relIndex_top_right]

omit [CharP F 2] in
theorem center_trivial_M [Finite F] :
    ∀ m : projectiveSL 3 F, (∀ y, m * y = y * m) → m = 1 := by
  intro m hm
  have : m ∈ Subgroup.center (projectiveSL 3 F) :=
    Subgroup.mem_center_iff.mpr fun y => (hm y).symm
  rw [CFSG.QuasithinUnique.Setup.X7a.center_projectiveSL_three_eq_bot'] at this
  exact Subgroup.mem_bot.mp this

theorem isSylowTwoOf_U_normalizer [Finite F] {N : Subgroup (projectiveSL 3 F)}
    (hN : projUnitriangular 3 F ≤ N) : IsSylowTwoOf (projUnitriangular 3 F) N := by
  refine ⟨hN, (isSylowTwoOf_U (F := F)).2.1, ?_⟩
  have h1 := (isSylowTwoOf_U (F := F)).2.2
  change ¬ 2 ∣ (projUnitriangular 3 F).relIndex ⊤ at h1
  rw [Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.relIndex_mul_index hN
  exact fun h => h1 (h.trans (Dvd.intro _ h2))

theorem core_V1 [Finite F] : pCoreOf 2 (Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) :
    Set (projectiveSL 3 F))) = V1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · set N := Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))
      with hN
    have hSyl : IsSylowTwoOf (projUnitriangular 3 F) N := isSylowTwoOf_U_normalizer U_le_normalizer_V1
    have hC := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl
    intro c hc
    have hcU := hC hc
    obtain ⟨c₀, a, b, rfl⟩ := mem_Ubar.mp hcU
    have hcn : s₂₃P * (wP c₀ * xP a * yP b) * s₂₃P⁻¹ ∈ pCoreOf 2 N := by
      have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N s23P_mem_normalizer_V1
      exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp hc
    have hcU' := hC hcn
    have e : s₂₃P * (wP c₀ * xP a * yP b) * s₂₃P⁻¹ = (xP c₀ * wP a) * proj 3 F (zMat b) := by
      calc _ = (s₂₃P * wP c₀ * s₂₃P⁻¹) * (s₂₃P * xP a * s₂₃P⁻¹) * (s₂₃P * yP b * s₂₃P⁻¹) := by
            group
        _ = _ := by rw [s23P_conj_wP', s23P_conj_xP', s23P_conj_yP', mul_assoc]
    have hz : proj 3 F (zMat b) ∈ projUnitriangular 3 F := by
      have h1 : xP c₀ * wP a ∈ projUnitriangular 3 F :=
        mul_mem ((projRoots (K := F)).x_mem c₀) ((projRoots (K := F)).w_mem a)
      have := mul_mem (inv_mem h1) (e ▸ hcU')
      have e2 : (xP c₀ * wP a)⁻¹ * (xP c₀ * wP a * proj 3 F (zMat b)) = proj 3 F (zMat b) := by
        group
      rwa [e2] at this
    have hb : b = 0 := by
      by_contra hb
      exact proj_zMat_not_mem_U hb hz
    subst hb
    rw [yP_zero (F := F), mul_one]
    exact ⟨a, c₀, by rw [wP_mul_xP]⟩
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      isPGroup_V1

theorem core_V2 [Finite F] : pCoreOf 2 (Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) :
    Set (projectiveSL 3 F))) = V2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · set N := Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))
      with hN
    have hSyl : IsSylowTwoOf (projUnitriangular 3 F) N := isSylowTwoOf_U_normalizer U_le_normalizer_V2
    have hC := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl
    intro c hc
    have hcU := hC hc
    obtain ⟨c₀, a, b, rfl⟩ := mem_Ubar.mp hcU
    have hcn : s₁₂P * (wP c₀ * xP a * yP b) * s₁₂P⁻¹ ∈ pCoreOf 2 N := by
      have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N s12P_mem_normalizer_V2
      exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp hc
    have hcU' := hC hcn
    have e : s₁₂P * (wP c₀ * xP a * yP b) * s₁₂P⁻¹ = yP c₀ * proj 3 F (vMat a) * wP b := by
      calc _ = (s₁₂P * wP c₀ * s₁₂P⁻¹) * (s₁₂P * xP a * s₁₂P⁻¹) * (s₁₂P * yP b * s₁₂P⁻¹) := by
            group
        _ = _ := by rw [s12P_conj_wP', s12P_conj_xP', s12P_conj_yP']
    have hz : proj 3 F (vMat a) ∈ projUnitriangular 3 F := by
      have h1 : yP c₀ ∈ projUnitriangular 3 F := (projRoots (K := F)).y_mem c₀
      have h2 : wP b ∈ projUnitriangular 3 F := (projRoots (K := F)).w_mem b
      have := mul_mem (mul_mem (inv_mem h1) (e ▸ hcU')) (inv_mem h2)
      have e2 : (yP c₀)⁻¹ * (yP c₀ * proj 3 F (vMat a) * wP b) * (wP b)⁻¹ = proj 3 F (vMat a) := by
        group
      rwa [e2] at this
    have ha : a = 0 := by
      by_contra ha
      exact proj_vMat_not_mem_U ha hz
    subst ha
    rw [xP_zero (F := F), mul_one]
    exact ⟨b, c₀, by rw [wP_mul_yP]⟩
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      isPGroup_V2

end L3

end CFSG.QuasithinUnique.Fin257
