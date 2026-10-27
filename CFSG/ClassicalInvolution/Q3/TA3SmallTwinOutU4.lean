module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinOutL4
public import CFSG.ClassicalInvolution.AschTight.S19KUniStd

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution CFSG.GH74.L5U5 Matrix CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem map_inv_of_mem_SUid (σ : F ≃+* F) {n : ℕ} {x : GL (Fin n) F} (hx : x ∈ SUid σ n) :
    (x : Matrix (Fin n) (Fin n) F).map σ =
      ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := by
  have h' : conjTr σ (x : Matrix (Fin n) (Fin n) F) = ((x⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) := by
    calc conjTr σ (x : Matrix (Fin n) (Fin n) F) = conjTr σ (x : Matrix (Fin n) (Fin n) F) *
        ((x : Matrix (Fin n) (Fin n) F) * ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          rw [← Matrix.mul_assoc, hx.2, Matrix.one_mul]
  rw [← h', conjTr, Matrix.transpose_transpose]

theorem coe_inv_eq_adjugate {x : GL (Fin 2) F} (hx : (x : Matrix (Fin 2) (Fin 2) F).det = 1) :
    ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      adjugate (x : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, hx, Ring.inverse_one, one_smul]

theorem blk4_map_SUid (σ : F ≃+* F) {a b : GL (Fin 2) F} (ha : a ∈ SUid σ 2) (hb : b ∈ SUid σ 2) :
    (blk4 (a : Matrix (Fin 2) (Fin 2) F) b).map σ =
      blk4 !![0, -1; 1, 0] !![0, -1; 1, 0] * blk4 (a : Matrix (Fin 2) (Fin 2) F) b *
        blk4 !![0, 1; -1, 0] !![0, 1; -1, 0] := by
  rw [blk4_map, map_inv_of_mem_SUid σ ha, map_inv_of_mem_SUid σ hb, coe_inv_eq_adjugate ha.1,
    coe_inv_eq_adjugate hb.1, ← sMat_adjugate, ← sMat_adjugate, blk4_mul, blk4_mul]

theorem eq_scalar_of_comm_diag {u v : F} (huv : u ≠ v) {P : Matrix (Fin 2) (Fin 2) F}
    (hd : P * diagonal ![u, v] = diagonal ![u, v] * P)
    (hs : P * !![0, 1; -1, 0] = !![0, 1; -1, 0] * P) : P = Matrix.scalar (Fin 2) (P 0 0) := by
  have d01 := congrFun (congrFun hd 0) 1
  have d10 := congrFun (congrFun hd 1) 0
  have s01 := congrFun (congrFun hs 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at d01 d10 s01
  have h01 : P 0 1 = 0 := by
    have : P 0 1 * (v - u) = 0 := by linear_combination d01
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr huv.symm)
  have h10 : P 1 0 = 0 := by
    have : P 1 0 * (u - v) = 0 := by linear_combination d10
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr huv)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]
  linear_combination -s01

theorem neg_one_mem_SUid (σ : F ≃+* F) : (-1 : GL (Fin 2) F) ∈ SUid σ 2 := by
  refine mem_SUid.mpr ⟨by simp [Matrix.det_neg], ?_⟩
  simp [conjTr, Matrix.map_neg, Matrix.map_one _ (map_zero σ) (map_one σ)]

@[expose] def sGL : GL (Fin 2) F := ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], sMat_mul_sInv, sInv_mul_sMat⟩

theorem sGL_mem_SUid (σ : F ≃+* F) : (sGL : GL (Fin 2) F) ∈ SUid σ 2 := by
  refine mem_SUid.mpr ⟨by simp [sGL, Matrix.det_fin_two], ?_⟩
  have hmap : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).map σ = !![0, 1; -1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  show conjTr σ (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] = 1
  rw [conjTr, hmap, sMat_transpose, sInv_mul_sMat]

@[expose] def diagUnit (u : Fˣ) : GL (Fin 2) F :=
  ⟨diagonal ![(u : F), (u⁻¹ : Fˣ)], diagonal ![((u⁻¹ : Fˣ) : F), u], by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; fin_cases i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; fin_cases i <;> simp⟩

theorem diagUnit_mem_SUid (σ : F ≃+* F) {u : Fˣ} (hu : σ (u : F) * u = 1) :
    diagUnit u ∈ SUid σ 2 := by
  refine mem_SUid.mpr ⟨by simp [diagUnit], ?_⟩
  show conjTr σ (diagonal ![(u : F), (u⁻¹ : Fˣ)]) * diagonal ![(u : F), (u⁻¹ : Fˣ)] = 1
  rw [conjTr_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simpa using hu
  · show σ ((u⁻¹ : Fˣ) : F) * ((u⁻¹ : Fˣ) : F) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hu, inv_one]

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_normOne_ne_inv (hF : Nat.card F = (p ^ f) ^ 2) (hq : 2 ≤ p ^ f) :
    ∃ u : Fˣ, unitaryInvolution F p f (u : F) * u = 1 ∧ (u : F) ≠ ((u⁻¹ : Fˣ) : F) := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := normOne (unitaryInvolution F p f))
  rw [Phan.card_normOne hF] at hu
  refine ⟨u, u.2, fun h => ?_⟩
  have h1 : u ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    have hu0 : ((u : Fˣ) : F) ≠ 0 := Units.ne_zero _
    rw [Units.val_inv_eq_inv_val] at h
    simp only [Subgroup.coe_one, Units.val_one, sq]
    calc ((u : Fˣ) : F) * ((u : Fˣ) : F) = ((u : Fˣ) : F) * ((u : Fˣ) : F)⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ hu0
  have h3 := orderOf_dvd_of_pow_eq_one h1
  rw [hu] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem exists_blkScalar_of_comm_SUid (hF : Nat.card F = (p ^ f) ^ 2) (hq : 2 ≤ p ^ f)
    (h2 : (2 : F) ≠ 0) {B : Matrix (Fin 4) (Fin 4) F}
    (hB : ∀ a b : GL (Fin 2) F, a ∈ SUid (unitaryInvolution F p f) 2 →
      b ∈ SUid (unitaryInvolution F p f) 2 → (a = 1 ∨ b = 1) →
        B * blk4 (a : Matrix (Fin 2) (Fin 2) F) b = blk4 (a : Matrix (Fin 2) (Fin 2) F) b * B) :
    ∃ c d : F, B = blkScalar c d := by
  have h1 := hB (-1) 1 (neg_one_mem_SUid _) (SUid _ 2).one_mem (Or.inr rfl)
  rw [Units.val_neg, Units.val_one] at h1
  obtain ⟨P, Q, rfl⟩ := exists_blk4_of_comm h2 h1
  obtain ⟨u, hu1, hu2⟩ := exists_normOne_ne_inv hF hq
  have hP : ∀ a : GL (Fin 2) F, a ∈ SUid (unitaryInvolution F p f) 2 →
      P * (a : Matrix (Fin 2) (Fin 2) F) = a * P := fun a ha => by
    have := hB a 1 ha (SUid _ 2).one_mem (Or.inr rfl)
    rw [Units.val_one, blk4_mul, blk4_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact (blk4_inj this).1
  have hQ : ∀ a : GL (Fin 2) F, a ∈ SUid (unitaryInvolution F p f) 2 →
      Q * (a : Matrix (Fin 2) (Fin 2) F) = a * Q := fun a ha => by
    have := hB 1 a (SUid _ 2).one_mem ha (Or.inl rfl)
    rw [Units.val_one, blk4_mul, blk4_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact (blk4_inj this).2
  exact ⟨P 0 0, Q 0 0, by
    rw [blkScalar, ← eq_scalar_of_comm_diag hu2 (hP _ (diagUnit_mem_SUid _ hu1))
      (hP _ (sGL_mem_SUid _)), ← eq_scalar_of_comm_diag hu2 (hQ _ (diagUnit_mem_SUid _ hu1))
      (hQ _ (sGL_mem_SUid _))]⟩

theorem field_eq_of_fix_SUid (hF : Nat.card F = (p ^ f) ^ 2) {G Gi : Matrix (Fin 4) (Fin 4) F}
    (hGiG : Gi * G = 1) (φ : F ≃+* F)
    (hfix : ∀ a : GL (Fin 2) F, a ∈ SUid (unitaryInvolution F p f) 2 →
      G * (blk4 (a : Matrix (Fin 2) (Fin 2) F) 1).map φ * Gi =
        blk4 (a : Matrix (Fin 2) (Fin 2) F) 1) :
    φ = RingEquiv.refl F ∨ φ = unitaryInvolution F p f := by
  refine Disconnected.AschTight.S19K.ringEquiv_eq_of_fixes hF φ fun c hc => ?_
  obtain ⟨e₀, he₀⟩ := Disconnected.AschTight.S19K.exists_su2Equiv (K := F) (p := p) (f := f) hF
  set x := e₀ (GH74.Generic.companionSL (⟨c, hc⟩ : fixedSubfield F p f))
  have ht := congrArg Matrix.trace (hfix (x : GL (Fin 2) F) x.2)
  rw [Matrix.trace_mul_cycle, hGiG, Matrix.one_mul, blk4_map, trace_blk4, trace_blk4,
    trace_map_two, Matrix.map_one _ (map_zero φ) (map_one φ)] at ht
  have htr : ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = c := by
    rw [he₀]
    simp [GH74.Generic.companionSL, trace_fin_two]
  rw [htr] at ht
  linear_combination ht

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
