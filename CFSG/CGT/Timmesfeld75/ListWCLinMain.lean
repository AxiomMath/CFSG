module

public import CFSG.CGT.Timmesfeld75.ListWCLinPair

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix
open scoped MatrixGroups

theorem IsWC.eq_of_le_of_transitive {G : Type*} [Group G] [Finite G] {T U : Subgroup G}
    (hT : IsWC T) (hTU : T ≤ U) (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1)
    (htr : ∀ u ∈ U, u ≠ 1 → ∃ g : G, g * t₀ * g⁻¹ = u ∧ conjSubgroup g U ≤ U) : T = U := by
  refine le_antisymm hTU fun u hu => ?_
  rcases eq_or_ne u 1 with rfl | hu1
  · exact T.one_mem
  obtain ⟨g, hg, hgU⟩ := htr u hu hu1
  have hconj : conjSubgroup g T = T := by
    refine (hT.2 t₀ ht₀ ht₀1).2 g fun y hy => ?_
    have hyU : y ∈ U := hgU (Subgroup.map_mono hTU hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hU _ (hTU ht₀) _ hyU).symm
  rw [← hconj, mem_conjSubgroup, ← hg]
  simpa [mul_assoc] using ht₀

variable {K : Type} [Field K] {m : ℕ}

@[expose] def dotLin (a : Fin m → K) : Module.Dual K (Fin m → K) where
  toFun x := a ⬝ᵥ x
  map_add' x y := dotProduct_add a x y
  map_smul' r x := by simp [dotProduct_smul]

theorem dotLin_apply (a x : Fin m → K) : dotLin a x = a ⬝ᵥ x := rfl

@[expose] def tvCenterSL (c : Fin m → K) : Subgroup SL(m, K) where
  carrier := {x | ∃ a : Fin m → K, a ⬝ᵥ c = 0 ∧
    (x : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c a}
  one_mem' := ⟨0, by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a + b, by simp [add_dotProduct, ha, hb], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hx, hy, tv_mul_tv_center ha]
  inv_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨-a, by simp [ha], ?_⟩
    have hx' : x = tvSL c a ha := Subtype.ext hx
    rw [hx', coe_tvSL_inv, vecMulVec_neg, sub_eq_add_neg]

@[expose] def tvAxisSL (a : Fin m → K) : Subgroup SL(m, K) where
  carrier := {x | ∃ v : Fin m → K, a ⬝ᵥ v = 0 ∧
    (x : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec v a}
  one_mem' := ⟨0, by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨v, hv, hx⟩ ⟨w, hw, hy⟩
    refine ⟨v + w, by simp [dotProduct_add, hv, hw], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hx, hy, tv_mul_tv_axis hw]
  inv_mem' := by
    rintro x ⟨v, hv, hx⟩
    refine ⟨-v, by simp [hv], ?_⟩
    have hx' : x = tvSL v a hv := Subtype.ext hx
    rw [hx', coe_tvSL_inv, neg_vecMulVec, sub_eq_add_neg]

theorem mem_tvCenterSL {c : Fin m → K} {x : SL(m, K)} :
    x ∈ tvCenterSL c ↔ ∃ a : Fin m → K, a ⬝ᵥ c = 0 ∧
      (x : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c a :=
  Iff.rfl

theorem mem_tvAxisSL {a : Fin m → K} {x : SL(m, K)} :
    x ∈ tvAxisSL a ↔ ∃ v : Fin m → K, a ⬝ᵥ v = 0 ∧
      (x : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec v a :=
  Iff.rfl

theorem tvCenterSL_comm {c : Fin m → K} :
    ∀ x ∈ tvCenterSL c, ∀ y ∈ tvCenterSL c, x * y = y * x := by
  rintro x ⟨a, ha, hx⟩ y ⟨b, hb, hy⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx, hy,
    tv_mul_tv_center ha, tv_mul_tv_center hb, add_comm a b]

theorem tvAxisSL_comm {a : Fin m → K} :
    ∀ x ∈ tvAxisSL a, ∀ y ∈ tvAxisSL a, x * y = y * x := by
  rintro x ⟨v, hv, hx⟩ y ⟨w, hw, hy⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx, hy,
    tv_mul_tv_axis hw, tv_mul_tv_axis hv, add_comm v w]

theorem isTransvection_of_coe {x : SL(m, K)} {c a : Fin m → K} (hc : c ≠ 0) (ha : a ≠ 0)
    (hac : a ⬝ᵥ c = 0) (hx : (x : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c a) :
    IsTransvection x := by
  refine ⟨fun h => vecMulVec_ne_zero_of hc ha ?_, dotLin a, c, (show dotLin a c = 0 from hac), ?_⟩
  · rw [h, Matrix.SpecialLinearGroup.coe_one] at hx
    have := congrArg (fun M => M - 1) hx
    simpa using this.symm
  · refine LinearEquiv.ext fun v => ?_
    rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, hx,
      one_add_vecMulVec_mulVec]
    rfl

variable [Finite K] [CharP K 2]

theorem tvCenterSL_transitive {t₀ : SL(m, K)} {c φ : Fin m → K} (hc : c ≠ 0) (hφ : φ ≠ 0)
    (hφc : φ ⬝ᵥ c = 0) (ht₀ : (t₀ : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c φ) :
    ∀ u ∈ tvCenterSL c, u ≠ 1 → ∃ g : SL(m, K), g * t₀ * g⁻¹ = u ∧
      conjSubgroup g (tvCenterSL c) ≤ tvCenterSL c := by
  rintro u ⟨a, hac, hu⟩ hu1
  have ha : a ≠ 0 := by
    rintro rfl
    apply hu1
    apply Subtype.ext
    rw [hu, vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨g, hg⟩ := exists_conj_of_isTransvection (isTransvection_of_coe hc hφ hφc ht₀)
    (isTransvection_of_coe hc ha hac hu)
  refine ⟨g, hg, ?_⟩
  have hmat : ((g * t₀ * g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      (u : Matrix (Fin m) (Fin m) K) := by rw [hg]
  rw [coe_conj_of_coe g ht₀, hu] at hmat
  obtain ⟨μ, hμ, -⟩ := exists_smul_of_vecMulVec_eq (add_left_cancel hmat) hc
    (vecMul_ne_zero' _ hφ)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    exact mulVec_ne_zero' g hc hμ
  have hGinv : ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ c = μ⁻¹ • c := by
    have h1 := inv_mulVec_mulVec' g c
    rw [hμ, mulVec_smul] at h1
    calc ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ c
        = μ⁻¹ • (μ • (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ c)) := by
          rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • c := by rw [h1]
  intro x hx
  rw [mem_conjSubgroup] at hx
  obtain ⟨b, hbc, hb⟩ := hx
  have hxe : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  refine ⟨μ • (b ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)), ?_, ?_⟩
  · rw [smul_dotProduct, ← dotProduct_mulVec, hGinv, dotProduct_smul, hbc, smul_zero,
      smul_zero]
  · rw [hxe, coe_conj_of_coe g hb, hμ, smul_vecMulVec, ← vecMulVec_smul]

theorem tvAxisSL_transitive {t₀ : SL(m, K)} {c φ : Fin m → K} (hc : c ≠ 0) (hφ : φ ≠ 0)
    (hφc : φ ⬝ᵥ c = 0) (ht₀ : (t₀ : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c φ) :
    ∀ u ∈ tvAxisSL φ, u ≠ 1 → ∃ g : SL(m, K), g * t₀ * g⁻¹ = u ∧
      conjSubgroup g (tvAxisSL φ) ≤ tvAxisSL φ := by
  rintro u ⟨v, hφv, hu⟩ hu1
  have hv : v ≠ 0 := by
    rintro rfl
    apply hu1
    apply Subtype.ext
    rw [hu, zero_vecMulVec, add_zero, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨g, hg⟩ := exists_conj_of_isTransvection (isTransvection_of_coe hc hφ hφc ht₀)
    (isTransvection_of_coe hv hφ hφv hu)
  refine ⟨g, hg, ?_⟩
  have hmat : ((g * t₀ * g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      (u : Matrix (Fin m) (Fin m) K) := by rw [hg]
  rw [coe_conj_of_coe g ht₀, hu] at hmat
  obtain ⟨μ, -, hμ⟩ := exists_smul_of_vecMulVec_eq (add_left_cancel hmat) hv
    (vecMul_ne_zero' _ hφ)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    exact hφ hμ
  have hφG : φ ᵥ* (g : Matrix (Fin m) (Fin m) K) = μ • φ := by
    calc φ ᵥ* (g : Matrix (Fin m) (Fin m) K)
        = (μ • (φ ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K))) ᵥ*
            (g : Matrix (Fin m) (Fin m) K) := by rw [← hμ]
      _ = μ • φ := by rw [smul_vecMul, vecMul_inv_vecMul']
  have hφGinv : φ ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) = μ⁻¹ • φ := by
    calc φ ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)
        = μ⁻¹ • (μ • (φ ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K))) := by
          rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • φ := by rw [← hμ]
  intro x hx
  rw [mem_conjSubgroup] at hx
  obtain ⟨w, hφw, hw⟩ := hx
  have hxe : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  refine ⟨μ⁻¹ • ((g : Matrix (Fin m) (Fin m) K) *ᵥ w), ?_, ?_⟩
  · rw [dotProduct_smul, dotProduct_mulVec, hφG, smul_dotProduct, hφw, smul_zero, smul_zero]
  · rw [hxe, coe_conj_of_coe g hw, hφGinv, vecMulVec_smul, ← smul_vecMulVec]

end CFSG.CGT.Timmesfeld75
