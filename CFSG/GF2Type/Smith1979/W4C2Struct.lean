module

public import CFSG.GF2Type.Smith1979.W4C2Model
public import CFSG.GF2Type.Smith1979.W4C2Check
public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LargeExtraspecial.Types
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

namespace LocalTest

open Module QuadraticMap CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

local notation "mat" => rowsMatrix 4

local notation "vec" => toVecD 4

@[expose] def vecE (v : Nat × Nat) : Vm := (vec v.1, vec v.2)

@[expose] def act (G H : Mat4) (s : Bool) (v : Vm) : Vm :=
  if s then (v.2 ᵥ* G, v.1 ᵥ* H) else (v.1 ᵥ* G, v.2 ᵥ* H)

@[expose] def semE (E : El) : Vm → Vm := act (mat E.G) (mat E.H) E.s

@[expose] def Valid (E : El) : Prop := mat E.G * (mat E.H)ᵀ = 1

@[expose] def Rel (E E' : El) : Prop :=
  mat E.G = mat E'.G ∧ mat E.H = mat E'.H ∧ E.s = E'.s

theorem vec_eq_iff (x y : Nat) : vec x = vec y ↔ x % 16 = y % 16 := by
  have h : ∀ n : Nat, vec n = vec (n % 16) := fun n => by
    funext j
    simp only [toVecD_apply]
    rw [show (16 : Nat) = 2 ^ 4 by norm_num, Nat.testBit_mod_two_pow]
    simp [j.isLt]
  constructor
  · intro hxy
    rw [h x, h y] at hxy
    exact toVecD_injective (by omega) (by omega) hxy
  · intro hxy
    rw [h x, h y, hxy]

theorem eqN_iff {a b : Nat} : eqN a b = true ↔ vec a = vec b := by
  rw [vec_eq_iff, eqN, beq_iff_eq]

theorem eqV_iff {u v : Nat × Nat} : eqV u v = true ↔ vecE u = vecE v := by
  simp only [eqV, Bool.and_eq_true, eqN_iff, vecE, Prod.mk.injEq]

theorem eqR_iff {R R' : Array Nat} : eqR R R' = true ↔ mat R = mat R' := by
  simp only [eqR, List.all_eq_true, List.mem_range, eqN_iff]
  constructor
  · intro h
    ext i j
    rw [rowsMatrix_apply, rowsMatrix_apply, h i.val i.isLt]
  · intro h i hi
    funext j
    have := congrFun (congrFun h ⟨i, hi⟩) j
    simpa [rowsMatrix_apply] using this

theorem eqE_iff {E E' : El} : eqE E E' = true ↔ Rel E E' := by
  simp only [eqE, Bool.and_eq_true, eqR_iff, beq_iff_eq, Rel, and_assoc]

theorem semE_mul (E E' : El) (v : Vm) : semE (mulE E E') v = semE E (semE E' v) := by
  rcases hs : E.s <;> rcases hs' : E'.s <;>
    simp [semE, act, mulE, hs, hs', rowsMatrix_mulRows, Matrix.vecMul_vecMul]

theorem semE_idE (v : Vm) : semE idE v = v := by
  simp [semE, act, idE, rowsMatrix_idRows]

theorem semE_congr {E E' : El} (h : Rel E E') : semE E = semE E' := by
  obtain ⟨h1, h2, h3⟩ := h
  funext v
  simp [semE, act, h1, h2, h3]

theorem Valid.all4 {E : El} (h : Valid E) :
    mat E.G * (mat E.H)ᵀ = 1 ∧ (mat E.H)ᵀ * mat E.G = 1 ∧ mat E.H * (mat E.G)ᵀ = 1 ∧
      (mat E.G)ᵀ * mat E.H = 1 := by
  have h1 : mat E.G * (mat E.H)ᵀ = 1 := h
  have h2 : (mat E.H)ᵀ * mat E.G = 1 := mul_eq_one_comm.mp h1
  have h3 : mat E.H * (mat E.G)ᵀ = 1 := by
    simpa using congrArg Matrix.transpose h1
  exact ⟨h1, h2, h3, mul_eq_one_comm.mp h3⟩

theorem valid_idE : Valid idE := by
  simp [Valid, idE, rowsMatrix_idRows]

theorem valid_mulE {E E' : El} (h : Valid E) (h' : Valid E') : Valid (mulE E E') := by
  obtain ⟨a1, a2, a3, a4⟩ := h.all4
  obtain ⟨b1, b2, b3, b4⟩ := h'.all4
  unfold Valid mulE
  rcases hs : E.s
  · simp only [Bool.false_eq_true, ↓reduceIte, rowsMatrix_mulRows, Matrix.transpose_mul]
    calc _ = mat E'.G * (mat E.G * (mat E.H)ᵀ) * (mat E'.H)ᵀ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [a1, Matrix.mul_one, b1]
  · simp only [↓reduceIte, rowsMatrix_mulRows, Matrix.transpose_mul]
    calc _ = mat E'.H * (mat E.G * (mat E.H)ᵀ) * (mat E'.G)ᵀ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [a1, Matrix.mul_one, b3]

theorem valid_invE {E : El} (h : Valid E) : Valid (invE E) := by
  obtain ⟨a1, a2, a3, a4⟩ := h.all4
  unfold Valid invE
  rcases hs : E.s
  · simp [rowsMatrix_transposeRows, a2]
  · simp [rowsMatrix_transposeRows, a4]

theorem rel_mulE_invE {E : El} (h : Valid E) : Rel (mulE E (invE E)) idE := by
  obtain ⟨a1, a2, a3, a4⟩ := h.all4
  unfold Rel mulE invE idE
  rcases hs : E.s
  · simp [rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_idRows, a2, a4]
  · simp [rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_idRows, a2, a4]

theorem rel_invE_mulE {E : El} (h : Valid E) : Rel (mulE (invE E) E) idE := by
  obtain ⟨a1, a2, a3, a4⟩ := h.all4
  unfold Rel mulE invE idE
  rcases hs : E.s
  · simp [rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_idRows, a1, a3]
  · simp [rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_idRows, a1, a3]

@[expose] def actLin (G H : Mat4) (s : Bool) : Vm →ₗ[ZMod 2] Vm :=
  if s then
    (G.vecMulLinear ∘ₗ LinearMap.snd (ZMod 2) V4 V4).prod
      (H.vecMulLinear ∘ₗ LinearMap.fst (ZMod 2) V4 V4)
  else
    (G.vecMulLinear ∘ₗ LinearMap.fst (ZMod 2) V4 V4).prod
      (H.vecMulLinear ∘ₗ LinearMap.snd (ZMod 2) V4 V4)

theorem actLin_apply (G H : Mat4) (s : Bool) (v : Vm) : actLin G H s v = act G H s v := by
  cases s <;> rfl

@[expose] def semLin (E : El) : Vm →ₗ[ZMod 2] Vm := actLin (mat E.G) (mat E.H) E.s

theorem semLin_apply (E : El) (v : Vm) : semLin E v = semE E v := actLin_apply _ _ _ _

theorem semE_invE_semE {E : El} (h : Valid E) (v : Vm) : semE (invE E) (semE E v) = v := by
  rw [← semE_mul, semE_congr (rel_invE_mulE h), semE_idE]

theorem semE_semE_invE {E : El} (h : Valid E) (v : Vm) : semE E (semE (invE E) v) = v := by
  rw [← semE_mul, semE_congr (rel_mulE_invE h), semE_idE]

@[expose] def decE (E : El) (h : Valid E) : Vm ≃ₗ[ZMod 2] Vm :=
  LinearEquiv.ofLinear (semLin E) (semLin (invE E))
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, semLin_apply, semLin_apply, semE_semE_invE h]; rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, semLin_apply, semLin_apply, semE_invE_semE h]; rfl)

theorem decE_apply {E : El} (h : Valid E) (v : Vm) : decE E h v = semE E v := by
  simp [decE, semLin_apply]

open Classical in
@[expose] noncomputable def dec (E : El) : Vm ≃ₗ[ZMod 2] Vm :=
  if h : Valid E then decE E h else 1

theorem dec_apply {E : El} (h : Valid E) (v : Vm) : dec E v = semE E v := by
  simp [dec, h, decE_apply]

theorem dec_mul {E E' : El} (h : Valid E) (h' : Valid E') : dec (mulE E E') = dec E * dec E' := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, dec_apply (valid_mulE h h'), dec_apply h', dec_apply h, semE_mul]

theorem dec_idE : dec idE = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [dec_apply valid_idE, semE_idE]; rfl

theorem valid_congr {E E' : El} (h : Rel E E') : Valid E ↔ Valid E' := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [Valid, h1, h2]

theorem dec_congr {E E' : El} (h : Rel E E') : dec E = dec E' := by
  by_cases hv : Valid E
  · have hv' : Valid E' := (valid_congr h).mp hv
    refine LinearEquiv.ext fun v => ?_
    rw [dec_apply hv, dec_apply hv', semE_congr h]
  · have hv' : ¬ Valid E' := fun x => hv ((valid_congr h).mpr x)
    simp [dec, hv, hv']

theorem dec_invE {E : El} (h : Valid E) : dec (invE E) = (dec E)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← dec_mul (valid_invE h) h, dec_congr (rel_invE_mulE h), dec_idE]

theorem symm_dec_apply {E : El} (h : Valid E) (w : Vm) : (dec E).symm w = semE (invE E) w := by
  rw [LinearEquiv.symm_apply_eq, dec_apply h, semE_semE_invE h]

theorem dot_vecMul {G H : Mat4} (h : G * Hᵀ = 1) (x y : V4) :
    (x ᵥ* G) ⬝ᵥ (y ᵥ* H) = x ⬝ᵥ y := by
  rw [← Matrix.mulVec_transpose H y, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h,
    Matrix.vecMul_one]

theorem dec_q0 {E : El} (h : Valid E) (v : Vm) : q0 (dec E v) = q0 v := by
  obtain ⟨a1, a2, a3, a4⟩ := h.all4
  rw [dec_apply h, q0_apply, q0_apply]
  unfold semE act
  cases hs : E.s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact dot_vecMul a1 _ _
  · simp only [↓reduceIte]
    rw [dotProduct_comm]
    exact dot_vecMul a3 _ _

theorem mem_Nsub {w : Vm} : w ∈ Nsub ↔ w.2 = 0 := by
  simp [Nsub, Submodule.mem_prod]

theorem mem_Nssub {w : Vm} : w ∈ Nssub ↔ w.1 = 0 := by
  simp [Nssub, Submodule.mem_prod]

theorem map_eq_of_forward_back {S T : Submodule (ZMod 2) Vm} (f : Vm ≃ₗ[ZMod 2] Vm)
    (h1 : ∀ u ∈ S, f u ∈ T) (h2 : ∀ w ∈ T, f.symm w ∈ S) :
    S.map (f : Vm →ₗ[ZMod 2] Vm) = T := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact h1 u hu
  · intro hw
    exact ⟨f.symm w, h2 w hw, f.apply_symm_apply w⟩

theorem semE_snd_of_snd {E : El} (hs : E.s = false) {u : Vm} (hu : u.2 = 0) :
    (semE E u).2 = 0 := by
  simp [semE, act, hs, hu]

theorem semE_fst_of_fst {E : El} (hs : E.s = false) {u : Vm} (hu : u.1 = 0) :
    (semE E u).1 = 0 := by
  simp [semE, act, hs, hu]

theorem semE_fst_of_snd {E : El} (hs : E.s = true) {u : Vm} (hu : u.2 = 0) :
    (semE E u).1 = 0 := by
  simp [semE, act, hs, hu]

theorem semE_snd_of_fst {E : El} (hs : E.s = true) {u : Vm} (hu : u.1 = 0) :
    (semE E u).2 = 0 := by
  simp [semE, act, hs, hu]

theorem invE_s (E : El) : (invE E).s = E.s := by
  unfold invE
  cases E.s <;> simp

theorem dec_mem_Hm {E : El} (h : Valid E) : dec E ∈ Hm := by
  rw [mem_Hm_iff]
  refine ⟨dec_q0 h, ?_⟩
  rcases hs : E.s
  · have hs' : (invE E).s = false := by rw [invE_s, hs]
    left
    refine ⟨map_eq_of_forward_back _ (fun u hu => ?_) (fun w hw => ?_),
      map_eq_of_forward_back _ (fun u hu => ?_) (fun w hw => ?_)⟩
    · rw [dec_apply h]; exact mem_Nsub.mpr (semE_snd_of_snd hs (mem_Nsub.mp hu))
    · rw [symm_dec_apply h]; exact mem_Nsub.mpr (semE_snd_of_snd hs' (mem_Nsub.mp hw))
    · rw [dec_apply h]; exact mem_Nssub.mpr (semE_fst_of_fst hs (mem_Nssub.mp hu))
    · rw [symm_dec_apply h]; exact mem_Nssub.mpr (semE_fst_of_fst hs' (mem_Nssub.mp hw))
  · have hs' : (invE E).s = true := by rw [invE_s, hs]
    right
    refine ⟨map_eq_of_forward_back _ (fun u hu => ?_) (fun w hw => ?_),
      map_eq_of_forward_back _ (fun u hu => ?_) (fun w hw => ?_)⟩
    · rw [dec_apply h]; exact mem_Nssub.mpr (semE_fst_of_snd hs (mem_Nsub.mp hu))
    · rw [symm_dec_apply h]; exact mem_Nsub.mpr (semE_snd_of_fst hs' (mem_Nssub.mp hw))
    · rw [dec_apply h]; exact mem_Nsub.mpr (semE_snd_of_fst hs (mem_Nssub.mp hu))
    · rw [symm_dec_apply h]; exact mem_Nssub.mpr (semE_fst_of_snd hs' (mem_Nsub.mp hw))

theorem eq_of_forall_vecMul {A B : Mat4} (h : ∀ x : V4, x ᵥ* A = x ᵥ* B) : A = B := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  simpa [Matrix.single_one_vecMul] using this

theorem eq_zero_of_forall_vecMul {A : Mat4} (h : ∀ x : V4, x ᵥ* A = 0) : A = 0 :=
  eq_of_forall_vecMul fun x => by rw [h x, Matrix.vecMul_zero]

theorem dec_inj {E E' : El} (h : Valid E) (h' : Valid E') (hE : dec E = dec E') : Rel E E' := by
  have hv : ∀ v, semE E v = semE E' v := fun v => by
    rw [← dec_apply h, ← dec_apply h', hE]
  have one_ne : (1 : Mat4) ≠ 0 := one_ne_zero
  rcases hs : E.s <;> rcases hs' : E'.s
  · refine ⟨?_, ?_, by rw [hs, hs']⟩
    · refine eq_of_forall_vecMul fun x => ?_
      have := congrArg Prod.fst (hv (x, 0))
      simpa [semE, act, hs, hs'] using this
    · refine eq_of_forall_vecMul fun y => ?_
      have := congrArg Prod.snd (hv (0, y))
      simpa [semE, act, hs, hs'] using this
  · exfalso
    have hG : mat E.G = 0 := by
      refine eq_zero_of_forall_vecMul fun x => ?_
      have := congrArg Prod.fst (hv (x, 0))
      simpa [semE, act, hs, hs'] using this
    exact one_ne (by rw [← h, hG, Matrix.zero_mul])
  · exfalso
    have hG : mat E'.G = 0 := by
      refine eq_zero_of_forall_vecMul fun x => ?_
      have := congrArg Prod.fst (hv (x, 0))
      simpa [semE, act, hs, hs'] using this.symm
    exact one_ne (by rw [← h', hG, Matrix.zero_mul])
  · refine ⟨?_, ?_, by rw [hs, hs']⟩
    · refine eq_of_forall_vecMul fun y => ?_
      have := congrArg Prod.fst (hv (0, y))
      simpa [semE, act, hs, hs'] using this
    · refine eq_of_forall_vecMul fun x => ?_
      have := congrArg Prod.snd (hv (x, 0))
      simpa [semE, act, hs, hs'] using this

theorem vecE_appE (E : El) (v : Nat × Nat) : vecE (appE E v) = semE E (vecE v) := by
  unfold appE vecE semE act
  cases hs : E.s <;> simp [toVecD_vecMulN]

theorem ite_add_ite_xor (p q : Bool) :
    ((if p then 1 else 0 : ZMod 2) + if q then 1 else 0) = if (p ^^ q) then 1 else 0 := by
  cases p <;> cases q <;> decide

theorem ite_mul_ite_and (p q : Bool) :
    ((if p then 1 else 0 : ZMod 2) * if q then 1 else 0) = if (p && q) then 1 else 0 := by
  cases p <;> cases q <;> decide

theorem dot_vec (x y : Nat) : vec x ⬝ᵥ vec y = if dot4 x y then 1 else 0 := by
  have h3 : ((3 : Fin 4) : Nat) = 3 := rfl
  simp only [dotProduct, Fin.sum_univ_four, toVecD_apply, dot4, Fin.val_zero, Fin.val_one,
    Fin.val_two, h3, Fin.isValue, ite_mul_ite_and, ite_add_ite_xor]
  rfl

theorem q0_vecE (v : Nat × Nat) : q0 (vecE v) = if dot4 v.1 v.2 then 1 else 0 := by
  rw [q0_apply]
  exact dot_vec _ _

theorem polar_q0 (x y : Vm) : polar q0 x y = x.1 ⬝ᵥ y.2 + y.1 ⬝ᵥ x.2 := by
  unfold polar
  rw [q0_apply, q0_apply, q0_apply]
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring

theorem polar_q0_vecE (a b : Nat × Nat) :
    polar q0 (vecE a) (vecE b) = if polarB a b then 1 else 0 := by
  rw [polar_q0]
  simp only [vecE, dot_vec, polarB, ite_add_ite_xor]
  rfl

theorem zmod2_val_le_one (a : ZMod 2) : a.val ≤ 1 := by
  have := ZMod.val_lt a
  omega

@[expose] def codeV (x : V4) : Nat :=
  (x 0).val + 2 * (x 1).val + 4 * (x 2).val + 8 * (x 3).val

theorem codeV_lt (x : V4) : codeV x < 16 := by
  have h := fun j => zmod2_val_le_one (x j)
  have := h 0; have := h 1; have := h 2; have := h 3
  unfold codeV
  omega

theorem testBit_codeV (x : V4) (j : Fin 4) : (codeV x).testBit j = decide ((x j).val = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  have h := fun j => zmod2_val_le_one (x j)
  have := h 0; have := h 1; have := h 2; have := h 3
  unfold codeV
  apply propext
  fin_cases j <;> simp <;> omega

theorem vec_codeV (x : V4) : vec (codeV x) = x := by
  funext j
  rw [toVecD_apply, testBit_codeV]
  generalize x j = a
  revert a
  decide

end LocalTest

end CFSG.GF2Type.Smith1979.W4C2
