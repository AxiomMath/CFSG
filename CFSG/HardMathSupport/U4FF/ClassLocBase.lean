module

public import CFSG.HardMathSupport.U4FF.ClassKron
public import CFSG.HardMathSupport.U4FF.ClassCompound

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups

inductive FK
  | N
  | W
  | S
  deriving DecidableEq

@[expose] def FK.dim : FK → ℕ
  | .N => 4
  | .W => 6
  | .S => 4

noncomputable section Reps

variable (k : Type*) [Field k]

@[expose] def repN : SL(4, k) →* Matrix (Fin 4) (Fin 4) k where
  toFun g := (g : Matrix (Fin 4) (Fin 4) k)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def repS : SL(4, k) →* Matrix (Fin 4) (Fin 4) k where
  toFun g := ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)ᵀ
  map_one' := by simp
  map_mul' g h := by
    simp only [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

@[expose] def repW : SL(4, k) →* Matrix (Fin 6) (Fin 6) k where
  toFun g := compound2 (g : Matrix (Fin 4) (Fin 4) k)
  map_one' := by simp [compound2_one]
  map_mul' g h := by simp [compound2_mul]

@[expose] def repK : (K : FK) → SL(4, k) →* Matrix (Fin K.dim) (Fin K.dim) k
  | .N => repN k
  | .W => repW k
  | .S => repS k

@[simp] theorem repK_N : repK k FK.N = repN k := rfl
@[simp] theorem repK_W : repK k FK.W = repW k := rfl
@[simp] theorem repK_S : repK k FK.S = repS k := rfl

theorem repN_apply (g : SL(4, k)) : repN k g = (g : Matrix (Fin 4) (Fin 4) k) := rfl
theorem repS_apply (g : SL(4, k)) :
    repS k g = ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)ᵀ := rfl
theorem repW_apply (g : SL(4, k)) :
    repW k g = compound2 (g : Matrix (Fin 4) (Fin 4) k) := rfl

end Reps

abbrev AmbIdx (fs : List FK) : Type := (i : Fin fs.length) → Fin (fs.get i).dim

noncomputable section Ambient

variable (k : Type*) [Field k] (fs : List FK)

@[expose] def ambRep : SL(4, k) →* Matrix (AmbIdx fs) (AmbIdx fs) k where
  toFun g := kronDep (fun i : Fin fs.length => Fin (fs.get i).dim)
    (fun i => repK k (fs.get i) g)
  map_one' := by
    simp only [map_one]
    exact kronDep_one
  map_mul' g h := by
    simp only [map_mul]
    exact kronDep_mul _ _

theorem ambRep_apply (g : SL(4, k)) :
    ambRep k fs g = kronDep (fun i : Fin fs.length => Fin (fs.get i).dim)
      (fun i => repK k (fs.get i) g) := rfl

end Ambient

@[expose] def derK : (K : FK) → Fin 4 → Fin 4 → Matrix (Fin K.dim) (Fin K.dim) (ZMod 2)
  | .N, i, j => Matrix.single i j 1
  | .W, i, j => deriv2 i j
  | .S, i, j => Matrix.single j i 1

section Transvection

variable {k : Type*} [Field k] [CharP k 2]

@[expose] def f2 (k : Type*) [Field k] [CharP k 2] : ZMod 2 →+* k := ZMod.castHom (dvd_refl 2) k

theorem repK_transvection (K : FK) {i j : Fin 4} (hij : i ≠ j) (a : k) :
    repK k K (Matrix.SpecialLinearGroup.transvection hij a) =
      1 + a • (derK K i j).map (f2 k) := by
  cases K with
  | N =>
    show (1 + Matrix.single i j a : Matrix (Fin 4) (Fin 4) k) =
      1 + a • (Matrix.single i j (1 : ZMod 2)).map (f2 k)
    ext x y
    simp [Matrix.single_apply, f2]
  | W =>
    exact compound2_transvection i j hij a
  | S =>
    show (((Matrix.SpecialLinearGroup.transvection hij a)⁻¹ : SL(4, k)) :
        Matrix (Fin 4) (Fin 4) k)ᵀ = 1 + a • (Matrix.single j i (1 : ZMod 2)).map (f2 k)
    rw [Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.transvection_coe]
    ext x y
    simp [Matrix.single_apply, f2, CharTwo.neg_eq, Matrix.transpose_apply, Matrix.one_apply,
      eq_comm]
    simp only [and_comm]

end Transvection


section Expansion

variable {k : Type*} [Field k]

theorem kronDep_one_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (κ : ι → Type*)
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (a : k)
    (D : (i : ι) → Matrix (κ i) (κ i) k) :
    kronDep κ (fun i => 1 + a • D i) =
      ∑ S : Finset ι, a ^ S.card • kronDep κ (fun i => if i ∈ S then D i else 1) := by
  ext x y
  simp only [kronDep, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 : ∀ i, (1 + a • D i) (x i) (y i) =
      a * D i (x i) (y i) + (1 : Matrix (κ i) (κ i) k) (x i) (y i) := by
    intro i
    simp [add_comm]
  simp_rw [h1]
  rw [Finset.prod_add]
  refine Finset.sum_congr (by simp) fun S _ => ?_
  have h2 : (∏ i, (if i ∈ S then D i else 1) (x i) (y i)) =
      (∏ i ∈ S, D i (x i) (y i)) * ∏ i ∈ Sᶜ, (1 : Matrix (κ i) (κ i) k) (x i) (y i) := by
    rw [← Finset.prod_mul_prod_compl S]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [Finset.mem_compl.mp hi]
  rw [h2, Finset.prod_mul_distrib, Finset.prod_const]
  simp [Finset.compl_eq_univ_sdiff]
  ring

end Expansion


theorem kronDep_map {R S : Type*} [Field R] [Field S] (φ : R →+* S) {ι : Type*}
    [Fintype ι] (κ : ι → Type*) [∀ i, Fintype (κ i)] (z : (i : ι) → Matrix (κ i) (κ i) R) :
    (kronDep κ z).map φ = kronDep κ (fun i => (z i).map φ) := by
  ext x y
  simp [kronDep, map_prod]

section Degrees

variable (fs : List FK)

@[expose] def ambZ (i j : Fin 4) (S : Finset (Fin fs.length)) :
    Matrix (AmbIdx fs) (AmbIdx fs) (ZMod 2) :=
  kronDep (fun f : Fin fs.length => Fin (fs.get f).dim)
    (fun f => if f ∈ S then derK (fs.get f) i j else 1)

@[expose] def ambD (i j : Fin 4) (r : ℕ) : Matrix (AmbIdx fs) (AmbIdx fs) (ZMod 2) :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin fs.length))).filter (fun S => S.card = r),
    ambZ fs i j S

theorem ambD_eq_zero_of_lt (i j : Fin 4) {r : ℕ} (hr : fs.length < r) : ambD fs i j r = 0 := by
  unfold ambD
  have : ((Finset.univ : Finset (Finset (Fin fs.length))).filter (fun S => S.card = r)) = ∅ := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h
    have := Finset.card_le_univ S
    simp only [Fintype.card_fin] at this
    omega
  rw [this, Finset.sum_empty]

variable {k : Type*} [Field k] [CharP k 2]

theorem ambRep_transvection {i j : Fin 4} (hij : i ≠ j) (a : k) :
    ambRep k fs (Matrix.SpecialLinearGroup.transvection hij a) =
      ∑ r ∈ Finset.range (fs.length + 1), a ^ r • (ambD fs i j r).map (f2 k) := by
  rw [ambRep_apply]
  have h1 : (fun f : Fin fs.length => repK k (fs.get f)
      (Matrix.SpecialLinearGroup.transvection hij a)) =
      fun f => 1 + a • (derK (fs.get f) i j).map (f2 k) :=
    funext fun f => repK_transvection (fs.get f) hij a
  rw [h1, kronDep_one_add_smul]
  have h2 : ∀ S : Finset (Fin fs.length),
      kronDep (fun f : Fin fs.length => Fin (fs.get f).dim)
        (fun f => if f ∈ S then (derK (fs.get f) i j).map (f2 k) else 1) =
      (ambZ fs i j S).map (f2 k) := by
    intro S
    rw [ambZ, kronDep_map]
    congr 1
    funext f
    by_cases hf : f ∈ S <;> simp [hf]
  simp_rw [h2]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (fs.length + 1))
    (fun S _ => by
      have := Finset.card_le_univ S
      simp only [Fintype.card_fin] at this
      exact Finset.mem_range.mpr (by omega))]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h3 : ((∑ S ∈ (Finset.univ : Finset (Finset (Fin fs.length))).filter
      (fun S => S.card = r), ambZ fs i j S).map (f2 k)) =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin fs.length))).filter (fun S => S.card = r),
        (ambZ fs i j S).map (f2 k) :=
    map_sum (f2 k).mapMatrix.toAddMonoidHom _ _
  rw [ambD, h3, Finset.smul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [(Finset.mem_filter.mp hS).2]

end Degrees


abbrev ambDim (fs : List FK) : ℕ := ∏ i : Fin fs.length, (fs.get i).dim

@[expose] def ambEq (fs : List FK) : AmbIdx fs ≃ Fin (ambDim fs) := finPiFinEquiv

@[expose] def ambDF (fs : List FK) (i j : Fin 4) (r : ℕ) :
    Matrix (Fin (ambDim fs)) (Fin (ambDim fs)) (ZMod 2) :=
  (ambD fs i j r).submatrix (ambEq fs).symm (ambEq fs).symm

theorem ambDF_eq_zero_of_lt (fs : List FK) (i j : Fin 4) {r : ℕ} (hr : fs.length < r) :
    ambDF fs i j r = 0 := by
  ext x y
  simp [ambDF, ambD_eq_zero_of_lt fs i j hr]

noncomputable section AmbientF

variable (k : Type*) [Field k] (fs : List FK)

@[expose] def ambRepF : SL(4, k) →* Matrix (Fin (ambDim fs)) (Fin (ambDim fs)) k where
  toFun g := (ambRep k fs g).submatrix (ambEq fs).symm (ambEq fs).symm
  map_one' := by
    simp only [map_one]
    exact Matrix.submatrix_one_equiv (ambEq fs).symm
  map_mul' g h := by
    simp only [map_mul]
    exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

theorem ambRepF_apply (g : SL(4, k)) :
    ambRepF k fs g = (ambRep k fs g).submatrix (ambEq fs).symm (ambEq fs).symm := rfl

variable [CharP k 2]

theorem ambRepF_transvection {i j : Fin 4} (hij : i ≠ j) (a : k) :
    ambRepF k fs (Matrix.SpecialLinearGroup.transvection hij a) =
      ∑ r ∈ Finset.range (fs.length + 1), a ^ r • (ambDF fs i j r).map (f2 k) := by
  rw [ambRepF_apply, ambRep_transvection fs hij a]
  ext x y
  simp [ambDF, Matrix.submatrix_apply, Matrix.sum_apply]

end AmbientF

section LocSpec

structure LocSpec (fs : List FK) where
  m : ℕ
  B : Matrix (Fin (ambDim fs)) (Fin m) (ZMod 2)
  Pm : Matrix (Fin m) (Fin (ambDim fs)) (ZMod 2)
  z : Fin (ambDim fs) → ZMod 2
  zeta : Fin (ambDim fs) → ZMod 2
  pm_B : Pm * B = 1
  pm_z : Pm *ᵥ z = 0
  zeta_B : zeta ᵥ* B = 0
  pi_z : (B * Pm + vecMulVec z zeta) *ᵥ z = z
  inv : ∀ i j : Fin 4, i ≠ j → ∀ r : ℕ,
    (B * Pm + vecMulVec z zeta) * (ambDF fs i j r * B) = ambDF fs i j r * B
  z_fix : ∀ i j : Fin 4, i ≠ j → ∀ r : ℕ, ambDF fs i j r *ᵥ z = if r = 0 then z else 0

variable {fs : List FK} (S : LocSpec fs) (k : Type*) [Field k] [CharP k 2]

@[expose] def LocSpec.Bk : Matrix (Fin (ambDim fs)) (Fin S.m) k := S.B.map (f2 k)
@[expose] def LocSpec.Pmk : Matrix (Fin S.m) (Fin (ambDim fs)) k := S.Pm.map (f2 k)
@[expose] def LocSpec.zk : Fin (ambDim fs) → k := fun x => f2 k (S.z x)
@[expose] def LocSpec.zetak : Fin (ambDim fs) → k := fun x => f2 k (S.zeta x)
@[expose] def LocSpec.Pi : Matrix (Fin (ambDim fs)) (Fin (ambDim fs)) (ZMod 2) :=
  S.B * S.Pm + vecMulVec S.z S.zeta

@[expose] def LocSpec.Pik : Matrix (Fin (ambDim fs)) (Fin (ambDim fs)) k :=
  S.Bk k * S.Pmk k + vecMulVec (S.zk k) (S.zetak k)

theorem LocSpec.Pik_eq_map : S.Pik k = S.Pi.map (f2 k) := by
  unfold LocSpec.Pi
  rw [Matrix.map_add _ (map_add (f2 k)), Matrix.map_mul]
  have h2 : (vecMulVec S.z S.zeta).map (f2 k) = vecMulVec (S.zk k) (S.zetak k) := by
    ext x y
    simp [Matrix.vecMulVec_apply, LocSpec.zk, LocSpec.zetak]
  rw [h2]
  rfl

theorem LocSpec.inv' (i j : Fin 4) (hij : i ≠ j) (r : ℕ) :
    S.Pi * (ambDF fs i j r * S.B) = ambDF fs i j r * S.B := S.inv i j hij r

end LocSpec

section Invariance

theorem map_mulVec' {R T : Type*} [CommSemiring R] [CommSemiring T] (φ : R →+* T) {α β : Type*}
    [Fintype α] [Fintype β] (M : Matrix α β R) (v : β → R) :
    M.map φ *ᵥ (fun x => φ (v x)) = fun x => φ ((M *ᵥ v) x) :=
  funext fun x => (RingHom.map_mulVec φ M v x).symm

variable {fs : List FK} (S : LocSpec fs) {k : Type*} [Field k] [CharP k 2]

theorem LocSpec.Pi_B : S.Pi * S.B = S.B := by
  unfold LocSpec.Pi
  rw [Matrix.add_mul, Matrix.mul_assoc, S.pm_B, Matrix.mul_one, Matrix.vecMulVec_mul, S.zeta_B]
  ext x y
  simp [Matrix.vecMulVec_apply]

theorem LocSpec.Pik_B : S.Pik k * S.Bk k = S.Bk k := by
  have := congrArg (fun M => M.map (f2 k)) S.Pi_B
  rw [LocSpec.Pik_eq_map]
  simpa [LocSpec.Bk, Matrix.map_mul] using this

theorem LocSpec.Pik_z : S.Pik k *ᵥ S.zk k = S.zk k := by
  have h : S.Pi *ᵥ S.z = S.z := S.pi_z
  rw [LocSpec.Pik_eq_map]
  show S.Pi.map (f2 k) *ᵥ (fun x => f2 k (S.z x)) = fun x => f2 k (S.z x)
  rw [map_mulVec', h]

theorem LocSpec.inv_k (i j : Fin 4) (hij : i ≠ j) (r : ℕ) :
    S.Pik k * ((ambDF fs i j r).map (f2 k) * S.Bk k) = (ambDF fs i j r).map (f2 k) * S.Bk k := by
  have := congrArg (fun M => M.map (f2 k)) (S.inv' i j hij r)
  rw [LocSpec.Pik_eq_map]
  simpa [LocSpec.Bk, Matrix.map_mul] using this

theorem LocSpec.z_fix_k (i j : Fin 4) (hij : i ≠ j) (r : ℕ) :
    (ambDF fs i j r).map (f2 k) *ᵥ S.zk k = if r = 0 then S.zk k else 0 := by
  have h := S.z_fix i j hij r
  show (ambDF fs i j r).map (f2 k) *ᵥ (fun x => f2 k (S.z x)) = _
  rw [map_mulVec', h]
  split_ifs
  · rfl
  · funext x; simp

@[expose] def LocSpec.Stab (g : SL(4, k)) : Prop :=
  S.Pik k * (ambRepF k fs g * S.Bk k) = ambRepF k fs g * S.Bk k ∧
    ambRepF k fs g *ᵥ S.zk k = S.zk k

theorem LocSpec.Stab_one : S.Stab (k := k) 1 := by
  refine ⟨?_, ?_⟩
  · rw [map_one, Matrix.one_mul]
    exact S.Pik_B
  · rw [map_one, Matrix.one_mulVec]

theorem LocSpec.Stab_mul {g h : SL(4, k)} (hg : S.Stab g) (hh : S.Stab h) : S.Stab (g * h) := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  refine ⟨?_, ?_⟩
  · rw [map_mul, Matrix.mul_assoc]
    set X := ambRepF k fs h * S.Bk k with hX
    have e1 : X = S.Bk k * (S.Pmk k * X) + vecMulVec (S.zk k) (S.zetak k ᵥ* X) := by
      conv_lhs => rw [← hh1]
      unfold LocSpec.Pik
      rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.vecMulVec_mul]
    have e2 : ambRepF k fs g * X = (ambRepF k fs g * S.Bk k) * (S.Pmk k * X) +
        vecMulVec (S.zk k) (S.zetak k ᵥ* X) := by
      conv_lhs => rw [e1]
      rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_vecMulVec, hg2]
    rw [e2, Matrix.mul_add, ← Matrix.mul_assoc, hg1, Matrix.mul_vecMulVec, S.Pik_z]
  · rw [map_mul, ← Matrix.mulVec_mulVec, hh2, hg2]

theorem LocSpec.Stab_transvection {i j : Fin 4} (hij : i ≠ j) (a : k) :
    S.Stab (Matrix.SpecialLinearGroup.transvection hij a) := by
  refine ⟨?_, ?_⟩
  · rw [ambRepF_transvection k fs hij a]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul]
    exact Finset.sum_congr rfl fun r _ => by rw [S.inv_k i j hij r]
  · rw [ambRepF_transvection k fs hij a, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec]
    simp only [S.z_fix_k i j hij]
    rw [Finset.sum_eq_single 0 (fun r _ hr => by simp [hr]) (by simp)]
    simp

theorem LocSpec.Stab_all (g : SL(4, k)) : S.Stab g := by
  have hgen : g ∈ Subgroup.closure (Set.range
      (Matrix.TransvectionStruct.toSpecialLinearGroup : Matrix.TransvectionStruct (Fin 4) k →
        SL(4, k))) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    trivial
  have key : S.Stab g ∧ S.Stab g⁻¹ := by
    refine Subgroup.closure_induction (p := fun g _ => S.Stab g ∧ S.Stab g⁻¹) ?_ ?_ ?_ ?_ hgen
    · rintro _ ⟨t, rfl⟩
      refine ⟨S.Stab_transvection t.hij t.c, ?_⟩
      rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def,
        Matrix.SpecialLinearGroup.transvection_inv]
      exact S.Stab_transvection t.hij (-t.c)
    · exact ⟨S.Stab_one, by simpa using S.Stab_one⟩
    · intro x y _ _ hx hy
      exact ⟨S.Stab_mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact S.Stab_mul hy.2 hx.2⟩
    · intro x _ hx
      exact ⟨hx.2, by simpa using hx.1⟩
  exact key.1

end Invariance

noncomputable section LocRep

variable {fs : List FK} (S : LocSpec fs) (k : Type*) [Field k] [CharP k 2]

theorem LocSpec.Pmk_z : S.Pmk k *ᵥ S.zk k = 0 := by
  have h : S.Pm *ᵥ S.z = 0 := S.pm_z
  show S.Pm.map (f2 k) *ᵥ (fun x => f2 k (S.z x)) = 0
  rw [map_mulVec', h]
  funext x
  simp

theorem LocSpec.Pmk_Bk : S.Pmk k * S.Bk k = 1 := by
  have := congrArg (fun M => M.map (f2 k)) S.pm_B
  simpa [LocSpec.Pmk, LocSpec.Bk, Matrix.map_mul] using this

@[expose] def LocSpec.locMat (g : SL(4, k)) : Matrix (Fin S.m) (Fin S.m) k :=
  S.Pmk k * (ambRepF k fs g * S.Bk k)

theorem LocSpec.amb_B (g : SL(4, k)) :
    ambRepF k fs g * S.Bk k = S.Bk k * S.locMat k g +
      vecMulVec (S.zk k) (S.zetak k ᵥ* (ambRepF k fs g * S.Bk k)) := by
  have h := (S.Stab_all (k := k) g).1
  conv_lhs => rw [← h]
  unfold LocSpec.Pik LocSpec.locMat
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.vecMulVec_mul]

theorem LocSpec.locMat_one : S.locMat k 1 = 1 := by
  unfold LocSpec.locMat
  rw [map_one, Matrix.one_mul]
  exact S.Pmk_Bk k

theorem LocSpec.locMat_mul (g h : SL(4, k)) :
    S.locMat k (g * h) = S.locMat k g * S.locMat k h := by
  have e := S.amb_B k h
  have hz := (S.Stab_all (k := k) g).2
  unfold LocSpec.locMat at e ⊢
  generalize hM : S.Pmk k * (ambRepF k fs h * S.Bk k) = M at e ⊢
  generalize hw : S.zetak k ᵥ* (ambRepF k fs h * S.Bk k) = w at e
  calc S.Pmk k * (ambRepF k fs (g * h) * S.Bk k)
      = S.Pmk k * (ambRepF k fs g * (ambRepF k fs h * S.Bk k)) := by
        rw [map_mul, Matrix.mul_assoc]
    _ = S.Pmk k * (ambRepF k fs g * (S.Bk k * M + vecMulVec (S.zk k) w)) := by rw [← e]
    _ = S.Pmk k * (ambRepF k fs g * S.Bk k) * M +
          vecMulVec (S.Pmk k *ᵥ (ambRepF k fs g *ᵥ S.zk k)) w := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc (ambRepF k fs g) (S.Bk k) M, Matrix.mul_vecMulVec,
          Matrix.mul_add, ← Matrix.mul_assoc (S.Pmk k) (ambRepF k fs g * S.Bk k) M,
          Matrix.mul_vecMulVec]
    _ = S.Pmk k * (ambRepF k fs g * S.Bk k) * M := by
        rw [hz, S.Pmk_z k]
        ext x y
        simp [Matrix.vecMulVec_apply]

@[expose] noncomputable def LocSpec.locRep : SL(4, k) →* Matrix (Fin S.m) (Fin S.m) k where
  toFun := S.locMat k
  map_one' := S.locMat_one k
  map_mul' := S.locMat_mul k

end LocRep

end CFSG.HardMathSupport.U4FF
