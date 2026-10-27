module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsForms
public import CFSG.LieType.Chevalley.E6GraphLeviUnitary
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {n : ℕ} {F : Type} [Field F]

variable (n F) in
@[expose] noncomputable def revGL : GL (Fin n) F where
  val := (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix F
  inv := (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix F
  val_inv := by
    rw [← Matrix.permMatrix_mul]
    have : (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 := by
      ext i
      simp
    rw [this, Matrix.permMatrix_one]
  inv_val := by
    rw [← Matrix.permMatrix_mul]
    have : (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 := by
      ext i
      simp
    rw [this, Matrix.permMatrix_one]

theorem revGL_apply (i j : Fin n) :
    (revGL n F : Matrix (Fin n) (Fin n) F) i j = if j = Fin.rev i then 1 else 0 := by
  change ((Fin.revPerm : Equiv.Perm (Fin n)).permMatrix F) i j = _
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Fin.revPerm_apply, Option.mem_def, Option.some.injEq]
  by_cases h : j = Fin.rev i
  · rw [ite_eq_left_iff.mpr (fun h' => absurd h.symm h'),
      ite_eq_left_iff.mpr (fun h' => absurd h h')]
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h'.symm h),
      ite_eq_right_iff.mpr (fun h' => absurd h' h)]

theorem revGL_mul_self : (revGL n F : Matrix (Fin n) (Fin n) F) * revGL n F = 1 :=
  (revGL n F).val_inv

theorem revGL_transpose : (revGL n F : Matrix (Fin n) (Fin n) F)ᵀ = revGL n F := by
  ext i j
  rw [transpose_apply, revGL_apply, revGL_apply]
  by_cases h : j = Fin.rev i
  · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'),
      ite_eq_left_iff.mpr (fun h' => absurd (by rw [h, Fin.rev_rev]) h')]
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h),
      ite_eq_right_iff.mpr (fun h' => absurd (by rw [h', Fin.rev_rev]) h)]

theorem revGL_map (σ : F →+* F) : (revGL n F : Matrix (Fin n) (Fin n) F).map σ = revGL n F := by
  ext i j
  rw [Matrix.map_apply, revGL_apply]
  split_ifs <;> simp

theorem revGL_eq_antidiag :
    (revGL n F : Matrix (Fin n) (Fin n) F) = CFSG.LieType.Universal.Unitary.antidiag n := by
  ext i j
  rw [revGL_apply]
  rfl

theorem revGL_six_eq_antiId :
    (revGL 6 F : Matrix (Fin 6) (Fin 6) F) = CFSG.LieType.Chevalley.E6GraphLevi.antiId F := by
  ext i j
  rw [revGL_apply]
  rfl

theorem card_slUnitary_eq_card_gramSU {p f : ℕ} (h : UnitaryFieldData p f F) {σ : F →+* F}
    (hσ : ∀ c, σ c = h.bar c) (J : Matrix (Fin n) (Fin n) F) :
    Nat.card (slUnitary σ J) = Nat.card (gramSU h J) := by
  have hmap : ∀ M : Matrix (Fin n) (Fin n) F, M.map σ = M.map h.bar := fun M => by
    ext i j
    exact hσ _
  refine Nat.card_congr
    { toFun := fun x => ⟨SpecialLinearGroup.toGL (x : SL(n, F)), ?_, ?_⟩
      invFun := fun g => ⟨⟨(g : GL (Fin n) F), g.2.2⟩, ?_⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun g => Subtype.ext (Units.ext rfl) }
  · rw [SpecialLinearGroup.coe_GL_coe_matrix, ← hmap]
    exact x.2
  · rw [SpecialLinearGroup.coe_GL_coe_matrix]
    exact (x : SL(n, F)).2
  · change (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J *
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = J
    rw [hmap]
    exact g.2.1

theorem card_slUnitary {p f : ℕ} (h : UnitaryFieldData p f F) {σ : F →+* F}
    (hσ : ∀ c, σ c = h.bar c) {J : Matrix (Fin n) (Fin n) F} (hJ : (J.map h.bar)ᵀ = J)
    (hdet : J.det ≠ 0) (hn : 1 ≤ n) :
    (Nat.card (slUnitary σ J) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  rw [card_slUnitary_eq_card_gramSU h hσ, card_gramSU]
  exact (CFSG.LinearGroups.unitary_full_group_order h (gramForm_isSymm h hJ)
    (gramForm_separatingLeft h hdet) (Module.finrank_fin_fun F) hn).2.1

theorem unitaryFieldData_of_card_four (hF : Nat.card F = 4) : UnitaryFieldData 2 1 F :=
  ⟨Nat.prime_two, le_rfl, by rw [hF]; norm_num⟩

theorem det_revGL_ne_zero : (revGL n F : Matrix (Fin n) (Fin n) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (revGL n F).isUnit).ne_zero

theorem card_slUnitary_six (hF : Nat.card F = 4) {σ : F →+* F} (hσ : ∀ c, σ c = c ^ 2) :
    Nat.card (slUnitary σ (revGL 6 F : Matrix (Fin 6) (Fin 6) F)) = 27590492160 := by
  have h := unitaryFieldData_of_card_four hF
  have hσ' : ∀ c, σ c = h.bar c := fun c => by rw [hσ, h.bar_apply, pow_one]
  have key := card_slUnitary h hσ' (J := (revGL 6 F : Matrix (Fin 6) (Fin 6) F))
    (by rw [revGL_map, revGL_transpose]) det_revGL_ne_zero (by norm_num)
  have hval : ((2 ^ 1 : ℕ) : ℤ) ^ (6 * (6 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 6, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 27590492160 := by
    decide
  rw [hval] at key
  exact_mod_cast key

theorem card_slUnitary_four (hF : Nat.card F = 4) {σ : F →+* F} (hσ : ∀ c, σ c = c ^ 2) :
    Nat.card (slUnitary σ (revGL 4 F : Matrix (Fin 4) (Fin 4) F)) = 25920 := by
  have h := unitaryFieldData_of_card_four hF
  have hσ' : ∀ c, σ c = h.bar c := fun c => by rw [hσ, h.bar_apply, pow_one]
  have key := card_slUnitary h hσ' (J := (revGL 4 F : Matrix (Fin 4) (Fin 4) F))
    (by rw [revGL_map, revGL_transpose]) det_revGL_ne_zero (by norm_num)
  have hval : ((2 ^ 1 : ℕ) : ℤ) ^ (4 * (4 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 4, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 25920 := by
    decide
  rw [hval] at key
  exact_mod_cast key

theorem exists_witt [Finite F] (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2)
    (n : ℕ) : ∃ Q : GL (Fin n) F,
      ((Q : Matrix (Fin n) (Fin n) F).map σ)ᵀ * Q = revGL n F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_two_of_card_four hF
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := 2) (f := 1)
    (F := F) (by rw [hF]; norm_num) n
  refine ⟨P, ?_⟩
  rw [revGL_eq_antidiag, ← hP]
  congr 2
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, hσ,
    CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one]

theorem slUnitary_six_eq (σ : F →+* F) :
    slUnitary σ (revGL 6 F : Matrix (Fin 6) (Fin 6) F) =
      CFSG.LieType.Chevalley.E6GraphLevi.unitarySL σ := by
  ext x
  rw [mem_slUnitary, CFSG.LieType.Chevalley.E6GraphLevi.mem_unitarySL_iff, revGL_six_eq_antiId]

theorem commutator_eq_self_of_isPerfect {M : Type*} [Group M] {H : Subgroup M}
    (hH : Group.IsPerfect H) : ⁅H, H⁆ = H := by
  have h := Subgroup.map_commutator (⊤ : Subgroup H) ⊤ H.subtype
  have htop := hH.commutator_eq_top
  rw [commutator_def] at htop
  rw [htop, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h.symm

theorem commutator_slUnitary_six [Finite F] (hF : Nat.card F = 4) {σ : F →+* F}
    (hσ : ∀ c, σ c = c ^ 2) :
    ⁅slUnitary σ (revGL 6 F : Matrix (Fin 6) (Fin 6) F),
      slUnitary σ (revGL 6 F : Matrix (Fin 6) (Fin 6) F)⁆ =
      slUnitary σ (revGL 6 F : Matrix (Fin 6) (Fin 6) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_two_of_card_four hF
  rw [slUnitary_six_eq]
  exact commutator_eq_self_of_isPerfect
    (CFSG.LieType.Chevalley.E6GraphLevi.isPerfect_unitarySL (f := 1) (by rw [hF]; norm_num)
      (fun c => by rw [hσ, pow_one]))

theorem center_le_slUnitary [Finite F] (hF : Nat.card F = 4) {σ : F →+* F}
    (hσ : ∀ c, σ c = c ^ 2) (J : Matrix (Fin n) (Fin n) F) :
    center SL(n, F) ≤ slUnitary σ J := by
  intro z hz
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_center hz
  have hc3 : (c : F) ^ 3 = 1 := pow_three_eq_one_of_card_four hF c.ne_zero
  rw [mem_slUnitary, hc, scalar_apply, diagonal_map (map_zero σ), diagonal_transpose,
    ← smul_one_eq_diagonal, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, hσ, ← pow_succ', hc3, one_smul]

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
