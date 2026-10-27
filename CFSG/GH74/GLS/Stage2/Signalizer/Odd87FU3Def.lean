module

public import CFSG.GH74.KGroups.L3EpsUniBlock

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.GH74.KGroups.L3Eps.Uni CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

section Fixed

variable {F : Type} [Field F]

abbrev w3 (a b c : F) : Fin 3 → F := ![a, b, c]

omit [Field F] in
theorem w3_eq (w : Fin 3 → F) : w = w3 (w 0) (w 1) (w 2) := by
  ext i
  fin_cases i <;> rfl

@[expose] def fixedSpace (X : Subgroup (GL (Fin 3) F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' := fun {a b} ha hb x hx => by rw [Matrix.mulVec_add, ha x hx, hb x hx]
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c a ha x hx => by rw [Matrix.mulVec_smul, ha x hx]

theorem fixedSpace_invariant {X : Subgroup (GL (Fin 3) F)} {b : GL (Fin 3) F}
    (hb : b ∈ normalizer (X : Set (GL (Fin 3) F))) {v : Fin 3 → F} (hv : v ∈ fixedSpace X) :
    (b : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ fixedSpace X := by
  intro x hx
  have hb' : b⁻¹ ∈ normalizer (X : Set (GL (Fin 3) F)) :=
    (normalizer (X : Set (GL (Fin 3) F))).inv_mem hb
  have hx' : b⁻¹ * x * b ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp hb' x).mp hx
    simpa using this
  have h1 := hv _ hx'
  have e : (x : Matrix (Fin 3) (Fin 3) F) * (b : Matrix (Fin 3) (Fin 3) F) =
      (b : Matrix (Fin 3) (Fin 3) F) * ((b⁻¹ * x * b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, h1]

theorem components_mem {Xt : Subgroup (GL (Fin 3) F)} {dM : Matrix (Fin 3) (Fin 3) F} {μ : F}
    (hdM : ∀ v : Fin 3 → F, dM *ᵥ v = w3 (μ * v 0) (μ⁻¹ * v 1) (v 2))
    (hDinv : ∀ v ∈ fixedSpace Xt, dM *ᵥ v ∈ fixedSpace Xt) (hμ1 : μ - 1 ≠ 0)
    (hμi1 : μ⁻¹ - 1 ≠ 0) (hμμ : μ - μ⁻¹ ≠ 0) {v : Fin 3 → F} (hv : v ∈ fixedSpace Xt) :
    w3 (v 0) 0 0 ∈ fixedSpace Xt ∧ w3 0 (v 1) 0 ∈ fixedSpace Xt := by
  have hu : dM *ᵥ v - v ∈ fixedSpace Xt := (fixedSpace Xt).sub_mem (hDinv v hv) hv
  have hu_eq : dM *ᵥ v - v = w3 ((μ - 1) * v 0) ((μ⁻¹ - 1) * v 1) 0 := by
    rw [hdM]
    ext i
    fin_cases i <;> (simp; try ring)
  set u := dM *ᵥ v - v with hudef
  have ha : dM *ᵥ u - μ⁻¹ • u ∈ fixedSpace Xt :=
    (fixedSpace Xt).sub_mem (hDinv u hu) ((fixedSpace Xt).smul_mem _ hu)
  have hb : dM *ᵥ u - μ • u ∈ fixedSpace Xt :=
    (fixedSpace Xt).sub_mem (hDinv u hu) ((fixedSpace Xt).smul_mem _ hu)
  rw [hu_eq] at ha hb
  have ha_eq : dM *ᵥ w3 ((μ - 1) * v 0) ((μ⁻¹ - 1) * v 1) 0 -
      μ⁻¹ • w3 ((μ - 1) * v 0) ((μ⁻¹ - 1) * v 1) 0 = ((μ - μ⁻¹) * (μ - 1)) • w3 (v 0) 0 0 := by
    rw [hdM]
    ext i
    fin_cases i <;> (simp; try ring)
  have hb_eq : dM *ᵥ w3 ((μ - 1) * v 0) ((μ⁻¹ - 1) * v 1) 0 -
      μ • w3 ((μ - 1) * v 0) ((μ⁻¹ - 1) * v 1) 0 = ((μ⁻¹ - μ) * (μ⁻¹ - 1)) • w3 0 (v 1) 0 := by
    rw [hdM]
    ext i
    fin_cases i <;> (simp; try ring)
  rw [ha_eq] at ha
  rw [hb_eq] at hb
  have hc1 : (μ - μ⁻¹) * (μ - 1) ≠ 0 := mul_ne_zero hμμ hμ1
  have hc2 : (μ⁻¹ - μ) * (μ⁻¹ - 1) ≠ 0 :=
    mul_ne_zero (by intro h0; exact hμμ (by linear_combination -h0)) hμi1
  refine ⟨?_, ?_⟩
  · have := (fixedSpace Xt).smul_mem (((μ - μ⁻¹) * (μ - 1))⁻¹) ha
    rwa [smul_smul, inv_mul_cancel₀ hc1, one_smul] at this
  · have := (fixedSpace Xt).smul_mem (((μ⁻¹ - μ) * (μ⁻¹ - 1))⁻¹) hb
    rwa [smul_smul, inv_mul_cancel₀ hc2, one_smul] at this

end Fixed

section FixedPoints

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ]

omit [Fact ℓ.Prime] in
theorem dvd_card_field : ℓ ∣ Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F ℓ
  rw [Nat.card_eq_fintype_card, hcard]
  exact dvd_pow_self ℓ n.pos.ne'

theorem exists_fixed_vector (X : Subgroup (GL (Fin 3) F)) (hX : IsPGroup ℓ ↥X) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
  classical
  have hdvd : ℓ ∣ Nat.card (Fin 3 → F) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3)]
    simp
    exact dvd_pow (dvd_card_field (F := F) (ℓ := ℓ)) (by norm_num)
  have h0 : (0 : Fin 3 → F) ∈ MulAction.fixedPoints X (Fin 3 → F) := by
    intro x
    show (x : GL (Fin 3) F) • (0 : Fin 3 → F) = 0
    simp
  obtain ⟨b, hb, hne⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 3 → F) hdvd h0
  refine ⟨b, fun h => hne h.symm, fun x hx => ?_⟩
  have := hb ⟨x, hx⟩
  exact this

theorem exists_fixed_in_plane (Xt : Subgroup (GL (Fin 3) F)) (hXp : IsPGroup ℓ ↥Xt)
    (hpres : ∀ x ∈ Xt, ∀ y : Fin 3 → F, y 2 = 0 → ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ y) 2 = 0) :
    ∃ u : Fin 3 → F, u ≠ 0 ∧ u 2 = 0 ∧ ∀ x ∈ Xt, (x : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u := by
  classical
  let α := {y : Fin 3 → F // y 2 = 0}
  let _ : MulAction ↥Xt α :=
    { smul := fun x y => ⟨(x : GL (Fin 3) F).val *ᵥ y.1, hpres x x.2 y.1 y.2⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : GL (Fin 3) F).val : Matrix (Fin 3) (Fin 3) F) *ᵥ y.1 = y.1
        simp)
      mul_smul := fun x x' y => Subtype.ext (by
        show (((x * x' : ↥Xt) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y.1 =
          (x : GL (Fin 3) F).val *ᵥ ((x' : GL (Fin 3) F).val *ᵥ y.1)
        rw [Matrix.mulVec_mulVec]
        rfl) }
  have hα : Nat.card α = Nat.card F ^ 2 := by
    let e : α ≃ (Fin 2 → F) :=
      { toFun := fun y => ![y.1 0, y.1 1]
        invFun := fun u => ⟨![u 0, u 1, 0], rfl⟩
        left_inv := fun y => by
          apply Subtype.ext
          ext i
          fin_cases i <;> simp [y.2]
        right_inv := fun u => by
          ext i
          fin_cases i <;> simp }
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2)]
    simp
  have hdvd : ℓ ∣ Nat.card α := by
    rw [hα]
    exact dvd_pow (dvd_card_field (F := F) (ℓ := ℓ)) (by norm_num)
  have h0 : (⟨0, rfl⟩ : α) ∈ MulAction.fixedPoints ↥Xt α := by
    intro x
    apply Subtype.ext
    show (x : GL (Fin 3) F).val *ᵥ (0 : Fin 3 → F) = 0
    simp
  obtain ⟨b, hb, hne⟩ := hXp.exists_fixed_point_of_prime_dvd_card_of_fixed_point α hdvd h0
  refine ⟨b.1, ?_, b.2, fun x hx => ?_⟩
  · intro h
    apply hne
    apply Subtype.ext
    exact h.symm
  · have := hb ⟨x, hx⟩
    exact congrArg Subtype.val this

end FixedPoints

section Block

variable {F : Type} [Field F] {ℓ f : ℕ}

theorem exists_norm_one_sq_ne_one (h : UnitaryFieldData ℓ f F) (h3 : 3 ≤ ℓ ^ f) :
    ∃ μ : F, μ ^ (ℓ ^ f + 1) = 1 ∧ μ ^ 2 ≠ 1 := by
  classical
  have : Finite F := h.finite
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Fintype.card Fˣ = (ℓ ^ f) ^ 2 - 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h.card, ← pow_mul, mul_comm, pow_mul, sq]
  have hord : orderOf g = (ℓ ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  generalize hq : ℓ ^ f = q at h3 hord ⊢
  have key : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    have := Nat.sq_sub_sq q 1
    rw [one_pow] at this
    rw [this, mul_comm]
  refine ⟨((g ^ (q - 1) : Fˣ) : F), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul, key, ← hord, pow_orderOf_eq_one]
    rfl
  · intro h1
    rw [← Units.val_pow_eq_pow_val, ← pow_mul] at h1
    have h2 : g ^ ((q - 1) * 2) = 1 := Units.ext (by simpa using h1)
    have h4 : q ^ 2 - 1 ∣ (q - 1) * 2 := hord ▸ orderOf_dvd_of_pow_eq_one h2
    have h5 : q ^ 2 - 1 ≤ (q - 1) * 2 := Nat.le_of_dvd (by omega) h4
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 3 := ⟨q - 3, by omega⟩
    have : (m + 3) ^ 2 - 1 = m ^ 2 + 6 * m + 8 := by
      have : (m + 3) ^ 2 = m ^ 2 + 6 * m + 9 := by ring
      omega
    omega

theorem exists_su2_of_matrix (h : UnitaryFieldData ℓ f F) (M : Matrix (Fin 2) (Fin 2) F)
    (hdet : M.det = 1) (hu : (M.map h.bar)ᵀ * M = 1) :
    ∃ B : ↥(unitarySU ℓ f F 2), ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = M := by
  let A : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = M := rfl
  refine ⟨⟨A, ?_⟩, hA⟩
  rw [mem_unitarySU_iff h]
  rw [hA]
  exact ⟨hdet, hu⟩

theorem exists_su2_diag (h : UnitaryFieldData ℓ f F) {μ : F} (hμ : μ ^ (ℓ ^ f + 1) = 1) :
    ∃ B : ↥(unitarySU ℓ f F 2), ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![μ, 0; 0, μ⁻¹] := by
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero _)] at hμ
    exact zero_ne_one hμ
  have hn : h.bar μ * μ = 1 := by
    rw [h.bar_apply, ← pow_succ]; exact hμ
  apply exists_su2_of_matrix h
  · rw [Matrix.det_fin_two_of]
    field_simp
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, map_inv₀]
    · exact hn
    · rw [← mul_inv, hn, inv_one]

theorem exists_su2_swap (h : UnitaryFieldData ℓ f F) :
    ∃ B : ↥(unitarySU ℓ f F 2), ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
  apply exists_su2_of_matrix h
  · rw [Matrix.det_fin_two_of]; ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_one_of_fix_two (h : UnitaryFieldData ℓ f F) {x : GL (Fin 3) F}
    (hx : x ∈ unitarySU ℓ f F 3)
    (h0 : (x : Matrix (Fin 3) (Fin 3) F) *ᵥ w3 1 0 0 = w3 1 0 0)
    (h1 : (x : Matrix (Fin 3) (Fin 3) F) *ᵥ w3 0 1 0 = w3 0 1 0) : x = 1 := by
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).mp hx
  set M : Matrix (Fin 3) (Fin 3) F := (x : Matrix (Fin 3) (Fin 3) F) with hM
  have c00 : M 0 0 = 1 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h0 0
  have c10 : M 1 0 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h0 1
  have c20 : M 2 0 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h0 2
  have c01 : M 0 1 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h1 0
  have c11 : M 1 1 = 1 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h1 1
  have c21 : M 2 1 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h1 2
  have u02 := congrFun (congrFun hu 0) 2
  have u12 := congrFun (congrFun hu 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, c00, c10, c20, c01, c11, c21] at u02 u12
  rw [Matrix.det_fin_three] at hdet
  simp [c00, c10, c20, c01, c11, c21, u02, u12] at hdet
  apply Units.ext
  ext i j
  rw [← hM]
  fin_cases i <;> fin_cases j <;> simp [c00, c10, c20, c01, c11, c21, u02, u12, hdet]

theorem preserves_plane_of_fix_e2 (h : UnitaryFieldData ℓ f F) {x : GL (Fin 3) F}
    (hx : x ∈ unitarySU ℓ f F 3) (h2 : (x : Matrix (Fin 3) (Fin 3) F) *ᵥ w3 0 0 1 = w3 0 0 1)
    (y : Fin 3 → F) (hy : y 2 = 0) : ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ y) 2 = 0 := by
  obtain ⟨-, hu⟩ := (mem_unitarySU_iff h).mp hx
  set M : Matrix (Fin 3) (Fin 3) F := (x : Matrix (Fin 3) (Fin 3) F) with hM
  have c02 : M 0 2 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h2 0
  have c12 : M 1 2 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h2 1
  have c22 : M 2 2 = 1 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h2 2
  have u20 := congrFun (congrFun hu 2) 0
  have u21 := congrFun (congrFun hu 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, c02, c12, c22] at u20 u21
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hy, u20, u21]

end Block

section BlockMain

variable {F : Type} [Field F] [Finite F] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP F ℓ]

theorem block_no_lgroup (h : UnitaryFieldData ℓ f F) (hq1 : 1 ≤ ℓ ^ f) (hq3 : 3 ≤ ℓ ^ f)
    (Xt : Subgroup (GL (Fin 3) F)) (hXU : Xt ≤ unitarySU ℓ f F 3) (hXp : IsPGroup ℓ ↥Xt)
    (hX1 : Xt ≠ ⊥)
    (hnorm : ∀ B : ↥(unitarySU ℓ f F 2),
      ((levU hq1 B : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) ∈ normalizer (Xt : Set (GL (Fin 3) F))) :
    False := by
  classical
  obtain ⟨μ, hμ, hμ2⟩ := exists_norm_one_sq_ne_one h hq3
  obtain ⟨D, hD⟩ := exists_su2_diag h hμ
  obtain ⟨W, hW⟩ := exists_su2_swap h
  have hμ1 : μ - 1 ≠ 0 := fun h1 => hμ2 (by rw [sub_eq_zero.mp h1]; norm_num)
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero _)] at hμ
    exact zero_ne_one hμ
  have hμi1 : μ⁻¹ - 1 ≠ 0 := by
    intro h1
    apply hμ1
    have : μ⁻¹ = 1 := sub_eq_zero.mp h1
    have h2 : μ = 1 := inv_eq_one.mp this
    rw [h2]; simp
  have hμμ : μ - μ⁻¹ ≠ 0 := by
    intro h1
    apply hμ2
    have : μ = μ⁻¹ := sub_eq_zero.mp h1
    field_simp at this
    linear_combination this
  set dM : Matrix (Fin 3) (Fin 3) F :=
    (((levU hq1 D : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hdM
  set wM : Matrix (Fin 3) (Fin 3) F :=
    (((levU hq1 W : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hwM
  have hdM_apply : ∀ v : Fin 3 → F, dM *ᵥ v = w3 (μ * v 0) (μ⁻¹ * v 1) (v 2) := by
    intro v
    rw [hdM, coe_levU hq1 D, hD]
    ext i
    fin_cases i <;> simp [leviMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hwM_apply : ∀ v : Fin 3 → F, wM *ᵥ v = w3 (v 1) (-v 0) (v 2) := by
    intro v
    rw [hwM, coe_levU hq1 W, hW]
    ext i
    fin_cases i <;> simp [leviMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hDinv : ∀ v ∈ fixedSpace Xt, dM *ᵥ v ∈ fixedSpace Xt :=
    fun v hv => fixedSpace_invariant (hnorm D) hv
  have hWinv : ∀ v ∈ fixedSpace Xt, wM *ᵥ v ∈ fixedSpace Xt :=
    fun v hv => fixedSpace_invariant (hnorm W) hv
  have lem_i : ∀ v ∈ fixedSpace Xt, (v 0 ≠ 0 ∨ v 1 ≠ 0) → Xt = ⊥ := by
    intro v hv hv01
    obtain ⟨hc0, hc1⟩ := components_mem hdM_apply hDinv hμ1 hμi1 hμμ hv
    have he0e1 : w3 (1 : F) 0 0 ∈ fixedSpace Xt ∧ w3 (0 : F) 1 0 ∈ fixedSpace Xt := by
      rcases hv01 with h0 | h1
      · have he0 : w3 (1 : F) 0 0 ∈ fixedSpace Xt := by
          have := (fixedSpace Xt).smul_mem (v 0)⁻¹ hc0
          convert this using 1
          ext i
          fin_cases i <;> simp [h0]
        refine ⟨he0, ?_⟩
        have := (fixedSpace Xt).smul_mem (-1 : F) (hWinv _ he0)
        convert this using 1
        rw [hwM_apply]
        ext i
        fin_cases i <;> simp
      · have he1 : w3 (0 : F) 1 0 ∈ fixedSpace Xt := by
          have := (fixedSpace Xt).smul_mem (v 1)⁻¹ hc1
          convert this using 1
          ext i
          fin_cases i <;> simp [h1]
        refine ⟨?_, he1⟩
        have := hWinv _ he1
        convert this using 1
        rw [hwM_apply]
        ext i
        fin_cases i <;> simp
    exact (Subgroup.eq_bot_iff_forall Xt).mpr fun x hx =>
      eq_one_of_fix_two h (hXU hx) (he0e1.1 x hx) (he0e1.2 x hx)
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector Xt hXp
  have hvV : v ∈ fixedSpace Xt := hv
  by_cases h01 : v 0 ≠ 0 ∨ v 1 ≠ 0
  · exact hX1 (lem_i v hvV h01)
  · push Not at h01
    obtain ⟨h0, h1⟩ := h01
    have hv2 : v 2 ≠ 0 := by
      intro h2
      apply hv0
      rw [w3_eq v, h0, h1, h2]
      ext i
      fin_cases i <;> simp
    have he2 : w3 (0 : F) 0 1 ∈ fixedSpace Xt := by
      have := (fixedSpace Xt).smul_mem (v 2)⁻¹ hvV
      convert this using 1
      rw [w3_eq v, h0, h1]
      ext i
      fin_cases i <;> simp [hv2]
    have hpres : ∀ x ∈ Xt, ∀ y : Fin 3 → F, y 2 = 0 → ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ y) 2 = 0 :=
      fun x hx y hy => preserves_plane_of_fix_e2 h (hXU hx) (he2 x hx) y hy
    obtain ⟨u, hu0, hu2, hu⟩ := exists_fixed_in_plane Xt hXp hpres
    have huV : u ∈ fixedSpace Xt := hu
    have hu01 : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hu0
      rw [w3_eq u, hcon.1, hcon.2, hu2]
      ext i
      fin_cases i <;> simp
    exact hX1 (lem_i u huV hu01)

end BlockMain

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
