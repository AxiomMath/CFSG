module

public import CFSG.LieType.Chevalley.E6GraphLeviRealization
public import CFSG.LieType.Universal.Unitary.Clause0

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphLevi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
open Matrix

variable {K : Type} [Field K]

theorem antiId_transpose : (antiId K)ᵀ = antiId K := by
  ext i j
  simp only [Matrix.transpose_apply, antiId, Matrix.of_apply]
  by_cases h : j = Fin.rev i
  · rw [ite_eq_left h, ite_eq_left (by rw [h, Fin.rev_rev])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', Fin.rev_rev]))]

theorem antiId_map {K' : Type} [Field K'] (σ : K →+* K') : (antiId K).map σ = antiId K' := by
  ext i j
  simp only [Matrix.map_apply, antiId, Matrix.of_apply]
  split_ifs <;> simp

theorem map_graphSL {K' : Type} [Field K'] (σ : K →+* K') (B : SpecialLinearGroup (Fin 6) K) :
    Matrix.SpecialLinearGroup.map σ (graphSL K B) =
      graphSL K' (Matrix.SpecialLinearGroup.map σ B) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_graphSL, coe_graphSL, ← map_inv,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    Matrix.map_mul, Matrix.map_mul, antiId_map, Matrix.transpose_map]

theorem graphSL_graphSL (B : SpecialLinearGroup (Fin 6) K) : graphSL K (graphSL K B) = B := by
  apply Subtype.ext
  rw [coe_graphSL, ← map_inv, coe_graphSL, inv_inv, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, antiId_transpose]
  simp only [Matrix.mul_assoc]
  rw [antiId_mul_self, Matrix.mul_one, ← Matrix.mul_assoc, antiId_mul_self, Matrix.one_mul]

variable (σ : K →+* K)

@[expose] def unitaryTwist : SpecialLinearGroup (Fin 6) K →* SpecialLinearGroup (Fin 6) K :=
  (graphSL K).comp (Matrix.SpecialLinearGroup.map σ)

@[expose] def unitarySL : Subgroup (SpecialLinearGroup (Fin 6) K) :=
  MonoidHom.eqLocus (unitaryTwist σ) (MonoidHom.id _)

variable {σ}

theorem mem_unitarySL_iff_unitaryTwist {B : SpecialLinearGroup (Fin 6) K} :
    B ∈ unitarySL σ ↔ unitaryTwist σ B = B :=
  Iff.rfl

theorem mem_unitarySL_iff {B : SpecialLinearGroup (Fin 6) K} :
    B ∈ unitarySL σ ↔
      ((B : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K * (B : Matrix (Fin 6) (Fin 6) K) =
        antiId K := by
  rw [mem_unitarySL_iff_unitaryTwist]
  set N := ((Matrix.SpecialLinearGroup.map σ B : SpecialLinearGroup (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K) with hN
  set N' := (((Matrix.SpecialLinearGroup.map σ B)⁻¹ : SpecialLinearGroup (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K) with hN'
  have hNN : N * N' = 1 := by
    rw [hN, hN', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hN'N : N' * N = 1 := by
    rw [hN, hN', ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hNmap : N = (B : Matrix (Fin 6) (Fin 6) K).map σ := by
    rw [hN, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hψ : ((unitaryTwist σ B : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      antiId K * N'ᵀ * antiId K := coe_graphSL _
  rw [← hNmap]
  constructor
  · intro h
    have h' := congrArg (fun B : SpecialLinearGroup (Fin 6) K => (B : Matrix (Fin 6) (Fin 6) K)) h
    rw [← h', hψ]
    calc Nᵀ * antiId K * (antiId K * N'ᵀ * antiId K) =
          Nᵀ * (antiId K * antiId K) * N'ᵀ * antiId K := by simp only [Matrix.mul_assoc]
      _ = (N' * N)ᵀ * antiId K := by
          rw [antiId_mul_self, Matrix.mul_one, Matrix.transpose_mul]
      _ = antiId K := by rw [hN'N, Matrix.transpose_one, Matrix.one_mul]
  · intro h
    apply Subtype.ext
    rw [hψ]
    calc antiId K * N'ᵀ * antiId K = antiId K * N'ᵀ * (Nᵀ * antiId K *
          (B : Matrix (Fin 6) (Fin 6) K)) := by rw [h]
      _ = antiId K * (N * N')ᵀ * antiId K * (B : Matrix (Fin 6) (Fin 6) K) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (B : Matrix (Fin 6) (Fin 6) K) := by
          rw [hNN, Matrix.transpose_one, Matrix.mul_one, antiId_mul_self, Matrix.one_mul]

theorem map_map_of_involutive (hσσ : ∀ c, σ (σ c) = c) (B : SpecialLinearGroup (Fin 6) K) :
    Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ B) = B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map]
  ext i j
  exact hσσ _

theorem unitaryTwist_unitaryTwist (hσσ : ∀ c, σ (σ c) = c) (B : SpecialLinearGroup (Fin 6) K) :
    unitaryTwist σ (unitaryTwist σ B) = B := by
  change graphSL K (Matrix.SpecialLinearGroup.map σ (graphSL K
    (Matrix.SpecialLinearGroup.map σ B))) = B
  rw [map_graphSL, graphSL_graphSL, map_map_of_involutive hσσ]

theorem graphSL_of_mem_unitarySL {B : SpecialLinearGroup (Fin 6) K} (hB : B ∈ unitarySL σ) :
    graphSL K B = Matrix.SpecialLinearGroup.map σ B := by
  have h : graphSL K (Matrix.SpecialLinearGroup.map σ B) = B := hB
  rw [← h, graphSL_graphSL, h]

theorem map_mem_unitarySL (hσσ : ∀ c, σ (σ c) = c) {B : SpecialLinearGroup (Fin 6) K}
    (hB : B ∈ unitarySL σ) : Matrix.SpecialLinearGroup.map σ B ∈ unitarySL σ := by
  change graphSL K (Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ B)) =
    Matrix.SpecialLinearGroup.map σ B
  rw [map_map_of_involutive hσσ, graphSL_of_mem_unitarySL hB]

variable (σ) in
theorem twistHom_realize
    (h2 : (2 : K) = 0) (B : SpecialLinearGroup (Fin 6) K) :
    twistHom TwistTag.E6 K σ (realize h2 B) = realize h2 (unitaryTwist σ B) := by
  rw [twistHom_apply]
  have e : Units.map (entrywiseHom σ) (realize h2 B) = baseChangeGL σ (realize h2 B) := rfl
  rw [e, baseChangeGL_realize, diagramMap_conj_realize]
  rfl

theorem diagramMap_conj_realize_of_mem_unitarySL
    (h2 : (2 : K) = 0)
    {B : SpecialLinearGroup (Fin 6) K} (hB : B ∈ unitarySL σ) :
    diagramMap TwistTag.E6 K * realize h2 B * (diagramMap TwistTag.E6 K)⁻¹ =
      realize h2 (Matrix.SpecialLinearGroup.map σ B) := by
  rw [diagramMap_conj_realize, graphSL_of_mem_unitarySL hB]

theorem pow_three_eq_one_of_mem_ker
    (h2 : (2 : K) = 0) {z : SpecialLinearGroup (Fin 6) K}
    (hz : z ∈ (realize h2).ker) : z ^ 3 = 1 := by
  obtain ⟨l, hl3, hl⟩ := (mem_ker_realize h2 z).1 hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hl, ← map_pow, hl3, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem exists_mem_unitarySL_of_twistHom
    (h2 : (2 : K) = 0) (hσσ : ∀ c, σ (σ c) = c)
    (B : SpecialLinearGroup (Fin 6) K)
    (hB : twistHom TwistTag.E6 K σ (realize h2 B) = realize h2 B) :
    ∃ B' ∈ unitarySL σ, realize h2 B' = realize h2 B := by
  rw [twistHom_realize] at hB
  set z := unitaryTwist σ B * B⁻¹ with hz
  have hzk : z ∈ (realize h2).ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hB, mul_inv_cancel]
  have hψB : unitaryTwist σ B = z * B := by rw [hz, inv_mul_cancel_right]
  have hψz : unitaryTwist σ z = z⁻¹ := by
    have h := unitaryTwist_unitaryTwist hσσ B
    rw [hψB, map_mul, hψB] at h
    refine eq_inv_of_mul_eq_one_left ?_
    calc unitaryTwist σ z * z = unitaryTwist σ z * (z * B) * B⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  have hz3 := pow_three_eq_one_of_mem_ker h2 hzk
  have hzinv : z⁻¹ = z ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz3])).symm
  refine ⟨z ^ 2 * B, ?_, ?_⟩
  · change unitaryTwist σ (z ^ 2 * B) = z ^ 2 * B
    rw [map_mul, map_pow, hψz, hψB, ← mul_assoc]
    congr 1
    calc z⁻¹ ^ 2 * z = z⁻¹ := by group
      _ = z ^ 2 := hzinv
  · rw [map_mul, map_pow, MonoidHom.mem_ker.1 hzk, one_pow, one_mul]

theorem conj_mem_center_iff {G : Type*} [Group G] (P g : G) :
    P * g * P⁻¹ ∈ Subgroup.center G ↔ g ∈ Subgroup.center G := by
  constructor
  · intro h
    have := (Subgroup.center G).normal_of_characteristic.conj_mem _ h P⁻¹
    rwa [show P⁻¹ * (P * g * P⁻¹) * P⁻¹⁻¹ = g by group] at this
  · intro h
    exact (Subgroup.center G).normal_of_characteristic.conj_mem _ h P

section Finite

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

variable [Finite K] {f : ℕ} [Fact (Nat.Prime 2)] [CharP K 2]

theorem conjTr_unitaryInvolution (hσ : ∀ c, σ c = c ^ 2 ^ f) (M : Matrix (Fin 6) (Fin 6) K) :
    conjTr (unitaryInvolution K 2 f) M = (M.map σ)ᵀ := by
  rw [conjTr]
  congr 1
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, unitaryInvolution_apply, hσ]

theorem map_toGL_unitarySL (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (unitarySL σ).map Matrix.SpecialLinearGroup.toGL = SU (unitaryInvolution K 2 f) 6 := by
  ext g
  constructor
  · rintro ⟨B, hB, rfl⟩
    refine ⟨B.2, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, conjTr_unitaryInvolution hσ]
    exact mem_unitarySL_iff.1 hB
  · rintro ⟨hdet, hiso⟩
    rw [conjTr_unitaryInvolution hσ] at hiso
    exact ⟨⟨(g : Matrix (Fin 6) (Fin 6) K), hdet⟩, mem_unitarySL_iff.2 hiso, Units.ext rfl⟩

@[expose] def unitarySLEquiv (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    unitarySL σ ≃* SU (unitaryInvolution K 2 f) 6 :=
  ((unitarySL σ).equivMapOfInjective _ Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (map_toGL_unitarySL hσ))

theorem coe_unitarySLEquiv (hσ : ∀ c, σ c = c ^ 2 ^ f) (B : unitarySL σ) :
    ((unitarySLEquiv hσ B : SU (unitaryInvolution K 2 f) 6) : GL (Fin 6) K) =
      Matrix.SpecialLinearGroup.toGL (B : SpecialLinearGroup (Fin 6) K) :=
  rfl

theorem isPerfect_unitarySL (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Group.IsPerfect (unitarySL σ) := by
  have : Group.IsPerfect (SU (unitaryInvolution K 2 f) 6) :=
    (isQuasisimple_SU hK (n := 6) (by norm_num) (by simp)).1
  exact Group.IsPerfect.ofSurjective (f := (unitarySLEquiv hσ).symm.toMonoidHom)
    (unitarySLEquiv hσ).symm.surjective

theorem mem_center_unitarySL_iff (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (B : unitarySL σ) : B ∈ Subgroup.center (unitarySL σ) ↔
      ∃ l : K, ((B : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        Matrix.scalar (Fin 6) l := by
  set P := (exists_wittMatrix hK 6).choose with hP
  set e := (unitarySLEquiv hσ).trans ((conjEquiv P (exists_wittMatrix hK 6).choose_spec).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 6))) with he
  have hZ := (isQuasisimple_statedSU_of_card hK (n := 6) (by norm_num) (by simp)).2
  have hcen : B ∈ Subgroup.center (unitarySL σ) ↔
      e B ∈ Subgroup.center (StatedSU 6 (2 ^ f) K) := by
    rw [← map_center_mulEquiv e]
    constructor
    · intro hB
      exact ⟨B, hB, rfl⟩
    · rintro ⟨B', hB', hBB'⟩
      rwa [← e.injective hBB']
  have hcoe : ((e B : StatedSU 6 (2 ^ f) K) : GL (Fin 6) K) =
      P * Matrix.SpecialLinearGroup.toGL (B : SpecialLinearGroup (Fin 6) K) * P⁻¹ := rfl
  rw [hcen, hZ, Subgroup.mem_subgroupOf, StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar, hcoe, conj_mem_center_iff,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨(u : K), ?_⟩
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hu
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
    exact this.symm
  · rintro ⟨l, hl⟩
    have hl0 : l ≠ 0 := by
      rintro rfl
      have hdet := (B : SpecialLinearGroup (Fin 6) K).2
      rw [hl, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
      simp at hdet
    refine ⟨Units.mk0 l hl0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hl]

end Finite

end CFSG.LieType.Chevalley.E6GraphLevi
