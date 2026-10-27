module

public import CFSG.GroupTheory.GL52.OrderThreeConj
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.StronglyEmbedded.Catalog

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix Polynomial

@[expose] def F4poly : (ZMod 2)[X] :=
  X ^ 2 + X + 1

theorem F4poly_natDegree : F4poly.natDegree = 2 := by
  unfold F4poly
  compute_degree!

theorem F4poly_irreducible : Irreducible F4poly := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [F4poly_natDegree]) (by rw [F4poly_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  have hne : F4poly ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [F4poly_natDegree] at this
    simp at this
  rw [Polynomial.mem_roots hne, IsRoot.def] at hx
  simp only [F4poly, eval_add, eval_pow, eval_X, eval_one] at hx
  revert hx
  revert x
  decide

instance F4poly_fact : Fact (Irreducible F4poly) :=
  ⟨F4poly_irreducible⟩

abbrev F4 : Type :=
  AdjoinRoot F4poly

abbrev F4root : F4 :=
  AdjoinRoot.root F4poly

@[expose] def F4Omega : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![0, 1; 1, 1]

theorem F4Omega_poly : aeval F4Omega F4poly = 0 := by
  simp only [F4poly, map_add, map_pow, aeval_X, map_one]
  decide

@[expose] def F4L : F4 →+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Ideal.Quotient.lift _ (aeval F4Omega).toRingHom (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    change aeval F4Omega (b * F4poly) = 0
    rw [map_mul, F4Omega_poly, mul_zero])

theorem F4L_root : F4L F4root = F4Omega := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ X) = _
  rw [Ideal.Quotient.lift_mk]
  simp

theorem F4L_of (c : ZMod 2) : F4L (AdjoinRoot.of F4poly c) = c • 1 := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (C c)) = _
  rw [Ideal.Quotient.lift_mk]
  simp [Algebra.algebraMap_eq_smul_one]

theorem F4L_injective : Function.Injective F4L :=
  F4L.injective

theorem F4poly_ne_zero : F4poly ≠ 0 :=
  F4poly_irreducible.ne_zero

@[expose] def F4basis : Module.Basis (Fin 2) (ZMod 2) F4 :=
  (AdjoinRoot.powerBasis F4poly_ne_zero).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, F4poly_natDegree]))

instance F4_moduleFinite : Module.Finite (ZMod 2) F4 :=
  Module.Finite.of_basis F4basis

instance F4_finite : Finite F4 :=
  Module.finite_of_finite (ZMod 2)

theorem card_F4 : Nat.card F4 = 4 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_eq_card_basis F4basis]
  simp

theorem F4L_lin (a b : ZMod 2) :
    F4L (AdjoinRoot.of F4poly a + AdjoinRoot.of F4poly b * F4root) = a • 1 + b • F4Omega := by
  rw [map_add, map_mul, F4L_of, F4L_of, F4L_root, smul_mul_assoc, one_mul]

theorem F4L_lin_apply (a b : ZMod 2) :
    F4L (AdjoinRoot.of F4poly a + AdjoinRoot.of F4poly b * F4root) 0 0 = a ∧
    F4L (AdjoinRoot.of F4poly a + AdjoinRoot.of F4poly b * F4root) 1 0 = b := by
  rw [F4L_lin]
  simp [F4Omega]

theorem F4_elems (x : F4) :
    ∃ a b : ZMod 2, x = AdjoinRoot.of F4poly a + AdjoinRoot.of F4poly b * F4root := by
  classical
  let f : ZMod 2 × ZMod 2 → F4 := fun p =>
    AdjoinRoot.of F4poly p.1 + AdjoinRoot.of F4poly p.2 * F4root
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' := congrArg F4L h
    simp only [f] at h'
    rw [F4L_lin, F4L_lin] at h'
    have h1 := congrFun (congrFun h' 0) 0
    have h2 := congrFun (congrFun h' 0) 1
    simp [F4Omega] at h1 h2
    rw [h1, h2]
  have hbij : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Nat.card_prod, Nat.card_zmod, card_F4]
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 x
  exact ⟨a, b, hab.symm⟩

theorem F4_omega_facts : F4Omega ^ 3 = 1 ∧ F4Omega ≠ 1 ∧ F4Omega ≠ 0 ∧ 1 + F4Omega = F4Omega ^ 2 ∧
    F4Omega ^ 2 ≠ 1 ∧ F4Omega ^ 4 ≠ 1 := by
  decide +kernel

theorem F4root_cube : F4root ^ 3 = 1 :=
  F4L_injective (by rw [map_pow, F4L_root, map_one]; exact F4_omega_facts.1)

theorem F4root_ne_zero : F4root ≠ 0 := fun h =>
  F4_omega_facts.2.2.1 (by rw [← F4L_root, h, map_zero])

theorem F4_nonzero {x : F4} (hx : x ≠ 0) : x = 1 ∨ x = F4root ∨ x = F4root ^ 2 := by
  obtain ⟨a, b, rfl⟩ := F4_elems x
  have hcase : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases hcase a with rfl | rfl <;> rcases hcase b with rfl | rfl
  · exact absurd (by simp) hx
  · right; left; simp
  · left; simp
  · right; right
    apply F4L_injective
    rw [F4L_lin, map_pow, F4L_root, ← F4_omega_facts.2.2.2.1]
    simp

@[expose] def F4rootUnit : F4ˣ :=
  Units.mk0 F4root F4root_ne_zero

theorem F4_unit_eq_pow (u : F4ˣ) : ∃ k < 3, u = F4rootUnit ^ k := by
  rcases F4_nonzero u.ne_zero with h | h | h
  · exact ⟨0, by norm_num, Units.ext (by simpa using h)⟩
  · exact ⟨1, by norm_num, Units.ext (by simpa [F4rootUnit] using h)⟩
  · exact ⟨2, by norm_num, Units.ext (by simpa [F4rootUnit] using h)⟩

theorem F4rootUnit_cube : F4rootUnit ^ 3 = 1 :=
  Units.ext (by simpa [F4rootUnit] using F4root_cube)

theorem F4_unit_cube (u : F4ˣ) : u ^ 3 = 1 := by
  obtain ⟨k, -, rfl⟩ := F4_unit_eq_pow u
  rw [← pow_mul, mul_comm, pow_mul, F4rootUnit_cube, one_pow]

theorem F4_unit_sq_eq_one {u : F4ˣ} (h : u ^ 2 = 1) : u = 1 := by
  have h3 := F4_unit_cube u
  calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h, inv_one, one_mul]

@[expose] def ord3PhiM (A : Matrix (Fin 2) (Fin 2) F4) : M5 :=
  !![F4L (A 0 0) 0 0, F4L (A 0 0) 0 1, F4L (A 0 1) 0 0, F4L (A 0 1) 0 1, 0;
    F4L (A 0 0) 1 0, F4L (A 0 0) 1 1, F4L (A 0 1) 1 0, F4L (A 0 1) 1 1, 0;
    F4L (A 1 0) 0 0, F4L (A 1 0) 0 1, F4L (A 1 1) 0 0, F4L (A 1 1) 0 1, 0;
    F4L (A 1 0) 1 0, F4L (A 1 0) 1 1, F4L (A 1 1) 1 0, F4L (A 1 1) 1 1, 0;
    0, 0, 0, 0, 1]

set_option maxHeartbeats 4000000 in
theorem ord3PhiM_mul (A B : Matrix (Fin 2) (Fin 2) F4) :
    ord3PhiM (A * B) = ord3PhiM A * ord3PhiM B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ord3PhiM, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two, map_add, map_mul] <;>
    ring

theorem ord3PhiM_one : ord3PhiM 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ord3PhiM]

theorem ord3PhiM_injective : Function.Injective ord3PhiM := by
  intro A B h
  have hblk : ∀ i j : Fin 2, F4L (A i j) = F4L (B i j) := by
    intro i j
    ext a b
    have e := congrFun
      (congrFun h (2 * i.castSucc.castSucc.castSucc + a.castSucc.castSucc.castSucc))
      (2 * j.castSucc.castSucc.castSucc + b.castSucc.castSucc.castSucc)
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> simpa [ord3PhiM] using e
  ext i j
  exact F4L_injective (hblk i j)

@[expose] def ord3PhiHom : GL (Fin 2) F4 →* G52 where
  toFun A := mk5 (ord3PhiM A) (ord3PhiM ((A⁻¹ : GL (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4)) (by
    rw [← ord3PhiM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ord3PhiM_one])
  map_one' := Units.ext (by rw [coe_mk5, Units.val_one, Units.val_one, ord3PhiM_one])
  map_mul' A B := Units.ext (by
    rw [coe_mk5, Units.val_mul, Units.val_mul, coe_mk5, coe_mk5, ord3PhiM_mul])

theorem coe_ord3PhiHom (A : GL (Fin 2) F4) :
    ((ord3PhiHom A : G52) : M5) = ord3PhiM (A : Matrix (Fin 2) (Fin 2) F4) :=
  rfl

theorem ord3PhiHom_injective : Function.Injective ord3PhiHom := by
  intro A B h
  exact Units.ext (ord3PhiM_injective (congrArg (fun g : G52 => (g : M5)) h))

theorem ord3PhiM_scalar : ord3PhiM (F4root • 1) = ord3T4M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ord3PhiM, ord3T4M, F4L_root, F4Omega]

theorem ord3_facts4 :
    (∀ v : V5, (ord3T4M * ord3T4M + ord3T4M + 1) *ᵥ v = 0 → v 4 = 0) ∧
    (∀ v : V5, (ord3T4M + 1) *ᵥ v = 0 → v = 0 ∨ v = Pi.single 4 1) ∧
    (ord3T4M * ord3T4M + ord3T4M + 1) *ᵥ Pi.single 0 1 = 0 ∧
    (ord3T4M * ord3T4M + ord3T4M + 1) *ᵥ Pi.single 2 1 = 0 ∧
    (ord3T4M + 1) *ᵥ Pi.single 4 1 = 0 ∧
    ord3T4M *ᵥ Pi.single 0 1 = Pi.single 1 1 ∧ ord3T4M *ᵥ Pi.single 2 1 = Pi.single 3 1 := by
  decide +kernel

theorem ord3_T4_matrix_commute {g : G52} (hg : g ∈ Subgroup.centralizer {ord3T4}) :
    (g : M5) * ord3T4M = ord3T4M * (g : M5) := by
  have := congrArg (fun x : G52 => (x : M5)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [ord3T4] using this

theorem ord3_T4_eq_of_commute {A B : M5} (hA : A * ord3T4M = ord3T4M * A)
    (hB : B * ord3T4M = ord3T4M * B) (h0 : A *ᵥ Pi.single 0 1 = B *ᵥ Pi.single 0 1)
    (h2 : A *ᵥ Pi.single 2 1 = B *ᵥ Pi.single 2 1)
    (h4 : A *ᵥ Pi.single 4 1 = B *ᵥ Pi.single 4 1) : A = B := by
  obtain ⟨-, -, -, -, -, v1, v3⟩ := ord3_facts4
  have e1 : A *ᵥ Pi.single 1 1 = B *ᵥ Pi.single 1 1 := by
    rw [← v1, mulVec_comm hA, mulVec_comm hB, h0]
  have e3 : A *ᵥ Pi.single 3 1 = B *ᵥ Pi.single 3 1 := by
    rw [← v3, mulVec_comm hA, mulVec_comm hB, h2]
  refine ext_cols fun j => ?_
  fin_cases j
  exacts [h0, e1, h2, e3, h4]

theorem ord3PhiM_commute (A : Matrix (Fin 2) (Fin 2) F4) :
    ord3PhiM A * ord3T4M = ord3T4M * ord3PhiM A := by
  rw [← ord3PhiM_scalar, ← ord3PhiM_mul, ← ord3PhiM_mul, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one]

@[expose] def ord3Coord (g : M5) : Matrix (Fin 2) (Fin 2) F4 :=
  !![AdjoinRoot.of F4poly (g 0 0) + AdjoinRoot.of F4poly (g 1 0) * F4root,
    AdjoinRoot.of F4poly (g 0 2) + AdjoinRoot.of F4poly (g 1 2) * F4root;
    AdjoinRoot.of F4poly (g 2 0) + AdjoinRoot.of F4poly (g 3 0) * F4root,
    AdjoinRoot.of F4poly (g 2 2) + AdjoinRoot.of F4poly (g 3 2) * F4root]

theorem ord3_eq_Phi {g : G52} (hg : g ∈ Subgroup.centralizer {ord3T4}) :
    (g : M5) = ord3PhiM (ord3Coord (g : M5)) := by
  obtain ⟨kP, kC, hP0, hP2, hC4, -, -⟩ := ord3_facts4
  have hc := ord3_T4_matrix_commute hg
  have hcP : (g : M5) * (ord3T4M * ord3T4M + ord3T4M + 1) =
      (ord3T4M * ord3T4M + ord3T4M + 1) * (g : M5) := by
    simp only [mul_add, add_mul, mul_one, one_mul, ← mul_assoc, hc]
    rw [mul_assoc, hc, ← mul_assoc]
  have hc1 : (g : M5) * (ord3T4M + 1) = (ord3T4M + 1) * (g : M5) := by
    rw [mul_add, add_mul, hc, mul_one, one_mul]
  have g0 := kP _ (by rw [← mulVec_comm hcP, hP0, mulVec_zero])
  have g2 := kP _ (by rw [← mulVec_comm hcP, hP2, mulVec_zero])
  have g4 : (g : M5) *ᵥ Pi.single 4 1 = Pi.single 4 1 := by
    rcases kC _ (by rw [← mulVec_comm hc1, hC4, mulVec_zero]) with h | h
    · exact absurd (eq_zero_of_mulVec_eq_zero g h) (by decide)
    · exact h
  simp only [mulVec_single_one, col_apply] at g0 g2
  refine ord3_T4_eq_of_commute hc (ord3PhiM_commute _) ?_ ?_ ?_
  · ext i
    rw [mulVec_single_one, mulVec_single_one, col_apply, col_apply]
    fin_cases i <;> simp [ord3PhiM, ord3Coord, F4L_lin_apply, g0]
  · ext i
    rw [mulVec_single_one, mulVec_single_one, col_apply, col_apply]
    fin_cases i <;> simp [ord3PhiM, ord3Coord, F4L_lin_apply, g2]
  · rw [g4]
    ext i
    fin_cases i <;> simp [ord3PhiM]

theorem ord3_range_Phi_le : ord3PhiHom.range ≤ Subgroup.centralizer {ord3T4} := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_ord3PhiHom]
  exact ord3PhiM_commute _

theorem ord3_centralizer_T4_eq_range : Subgroup.centralizer {ord3T4} = ord3PhiHom.range := by
  refine le_antisymm (fun g hg => ?_) ord3_range_Phi_le
  have h1 := ord3_eq_Phi hg
  have h2 := ord3_eq_Phi (inv_mem hg)
  have hAA : ord3Coord (g : M5) * ord3Coord ((g⁻¹ : G52) : M5) = 1 := by
    apply ord3PhiM_injective
    rw [ord3PhiM_mul, ← h1, ← h2, ← Units.val_mul, mul_inv_cancel, Units.val_one, ord3PhiM_one]
  exact ⟨⟨_, _, hAA, mul_eq_one_comm.1 hAA⟩, Units.ext h1.symm⟩

@[expose] def ord3ScalarU : F4ˣ →* GL (Fin 2) F4 :=
  Units.map (Matrix.scalar (Fin 2) : F4 →+* Matrix (Fin 2) (Fin 2) F4).toMonoidHom

theorem ord3_det_scalarU (u : F4ˣ) :
    Matrix.GeneralLinearGroup.det (ord3ScalarU u) = u ^ 2 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val]
  change (Matrix.scalar (Fin 2) (u : F4)).det = _
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, sq]

theorem ord3_Phi_scalarU_root : ord3PhiHom (ord3ScalarU F4rootUnit) = ord3T4 := by
  refine Units.ext ?_
  rw [coe_ord3PhiHom]
  change ord3PhiM (Matrix.scalar (Fin 2) F4root) = ord3T4M
  rw [Matrix.scalar_apply, ← ord3PhiM_scalar]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def ord3K4Hom : Matrix.SpecialLinearGroup (Fin 2) F4 →* G52 :=
  ord3PhiHom.comp Matrix.SpecialLinearGroup.toGL

theorem ord3K4Hom_injective : Function.Injective ord3K4Hom :=
  ord3PhiHom_injective.comp Matrix.SpecialLinearGroup.toGL_injective

@[expose] def ord3K4 : Subgroup G52 :=
  ord3K4Hom.range

theorem ord3_centralizer_T4 :
    IsInnerDirectProduct (Subgroup.zpowers ord3T4) ord3K4 (Subgroup.centralizer {ord3T4}) := by
  classical
  have hK : ord3K4 ≤ Subgroup.centralizer {ord3T4} := by
    rintro _ ⟨S, rfl⟩
    exact ord3_range_Phi_le ⟨_, rfl⟩
  refine ⟨le_antisymm (sup_le ?_ hK) fun g hg => ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  · rw [ord3_centralizer_T4_eq_range] at hg
    obtain ⟨A, rfl⟩ := hg
    set d := Matrix.GeneralLinearGroup.det A with hd
    set A' := (ord3ScalarU (d ^ 2))⁻¹ * A with hA'
    have hdet : Matrix.GeneralLinearGroup.det A' = 1 := by
      rw [hA', map_mul, map_inv, ord3_det_scalarU, ← hd, ← pow_mul]
      have h3 := F4_unit_cube d
      calc (d ^ (2 * 2))⁻¹ * d = (d ^ 3)⁻¹ * (d ^ 3)⁻¹ * d ^ 3 := by group
        _ = 1 := by rw [h3]; group
    have hA'K : ord3PhiHom A' ∈ ord3K4 := by
      have : A' ∈ (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 2) F4 →* GL (Fin 2) F4).range := by
        rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
        exact hdet
      obtain ⟨S, hS⟩ := this
      exact ⟨S, by rw [ord3K4Hom, MonoidHom.comp_apply, hS]⟩
    obtain ⟨k, -, hk⟩ := F4_unit_eq_pow (d ^ 2)
    have hz : ord3PhiHom (ord3ScalarU (d ^ 2)) ∈ Subgroup.zpowers ord3T4 := by
      rw [hk, map_pow, map_pow, ord3_Phi_scalarU_root]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    have e : A = ord3ScalarU (d ^ 2) * A' := by rw [hA', mul_inv_cancel_left]
    rw [e, map_mul]
    exact mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hA'K)
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxz, ⟨S, rfl⟩⟩ := Subgroup.mem_inf.1 hx
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_ord3T4] at hxz
    obtain ⟨m, -, hmx⟩ := Finset.mem_image.1 hxz
    have heq : ord3ScalarU (F4rootUnit ^ m) = Matrix.SpecialLinearGroup.toGL S := by
      apply ord3PhiHom_injective
      rw [map_pow, map_pow, ord3_Phi_scalarU_root, hmx]
      rfl
    have hdet := congrArg Matrix.GeneralLinearGroup.det heq
    rw [ord3_det_scalarU, Matrix.SpecialLinearGroup.coeToGL_det] at hdet
    have h1 : F4rootUnit ^ m = 1 := F4_unit_sq_eq_one hdet
    rw [Subgroup.mem_bot, ← hmx]
    have : ord3T4 ^ m = ord3PhiHom (ord3ScalarU (F4rootUnit ^ m)) := by
      rw [map_pow, map_pow, ord3_Phi_scalarU_root]
    rw [this, h1, map_one, map_one]
  · intro a ha b hb
    have hbC := hK hb
    rw [Subgroup.mem_centralizer_singleton_iff] at hbC
    have hle : Subgroup.zpowers ord3T4 ≤ Subgroup.centralizer {b} := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hbC.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)

theorem ord3_center_SL2_F4 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F4) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hu : Units.mk0 r hr0 ^ 2 = 1 := Units.ext (by simpa using hr)
  have h1 : r = 1 := by
    have := congrArg Units.val (F4_unit_sq_eq_one hu)
    simpa using this
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, h1]
  simp

theorem ord3_card_SL2_F4 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F4) = 60 := by
  classical
  have : Fintype F4 := Fintype.ofFinite F4
  have hq : Fintype.card F4 = 4 := by rw [← Nat.card_eq_fintype_card, card_F4]
  rw [Matrix.card_SL_field, hq, Fin.prod_univ_two]
  norm_num

theorem ord3_isSimple_SL2_F4 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F4) := by
  classical
  have : Fintype F4 := Fintype.ofFinite F4
  have h := (CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 2) le_rfl
    (Or.inr ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_F4]⟩)).2.1
  have e : Matrix.SpecialLinearGroup (Fin 2) F4 ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F4 :=
    (QuotientGroup.quotientBot (G := Matrix.SpecialLinearGroup (Fin 2) F4)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq ord3_center_SL2_F4.symm)
  exact e.isSimpleGroup

theorem ord3_K4_equiv_alternating :
    Nonempty (ord3K4 ≃* alternatingGroup (Fin 5)) := by
  have e : Matrix.SpecialLinearGroup (Fin 2) F4 ≃* ord3K4 :=
    MonoidHom.ofInjective ord3K4Hom_injective
  have : IsSimpleGroup ord3K4 := by
    have := ord3_isSimple_SL2_F4
    exact e.symm.isSimpleGroup
  have hcard : Nat.card ord3K4 = 60 := by
    rw [← Nat.card_congr e.toEquiv, ord3_card_SL2_F4]
  exact CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hcard

end CFSG.GroupTheory.GL52
