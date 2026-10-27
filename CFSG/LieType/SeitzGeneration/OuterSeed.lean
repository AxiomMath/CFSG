module

public import CFSG.LieType.SeitzGeneration.OuterGeneric

public section

open scoped commutatorElement MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryModel

namespace CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem heisB12_le_of_generic_column (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hℓ3 : ℓ ≠ 3) (h17 : 17 ≤ ℓ ^ f) {a : K} (ha : orderOf a = ℓ ^ f + 1)
    {Q : Subgroup (unitarySU ℓ f K 3)}
    (hge1 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hge3 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {y : unitarySU ℓ f K 3} (hyQ : y ∈ Q)
    (hw0 : (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0 ≠ 0)
    (hw1 : (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1 ≠ 0)
    (hw2 : (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 ≠ 0)
    (hn2 : h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 ≠ 1) :
    heisB12 ℓ f K ≤ Q := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hyU := ((mem_unitarySU_iff h).1 y.2).2
  have hyP : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = 1 := mul_eq_one_comm.2 hyU
  have hwN : h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0 +
      h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1 +
      h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 = 1 := by
    have := congrFun (congrFun hyU 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct] using this
  obtain ⟨ge3, hge3Q, hge3m⟩ := hge3
  have hzc : y * ge3 * y⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hyQ hge3Q) (Q.inv_mem hyQ)
  have hzm : (((y * ge3 * y⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a)
        (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) := by
    have e : (((y * ge3 * y⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((ge3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
      rw [← val_inv_eq_star h y]
      rfl
    rw [e, hge3m, conj_homMat h _ hyP]
  obtain ⟨ge1, hge1Q, hge1m⟩ := hge1
  have hApp := su2_block_mem_of_generic h hℓ3 h17 hq3 ha (Q.map (unitarySU ℓ f K 3).subtype)
    ⟨(ge1 : GL (Fin 3) K), ⟨ge1, hge1Q, rfl⟩, hge1m⟩
    ⟨(ge3 : GL (Fin 3) K), ⟨ge3, hge3Q, rfl⟩, hge3m⟩
    (w := ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) hwN hw0 hw1 hw2
    (by
      intro h0
      apply hn2
      linear_combination hwN - h0)
    ⟨((y * ge3 * y⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K), ⟨_, hzc, rfl⟩, hzm⟩
  intro g hg
  obtain ⟨A, hA, hgA⟩ := mem_heisB12.1 hg
  obtain ⟨x, hx, hxA⟩ := hApp A hA
  have : x = g := Subtype.ext (hxA.trans (Units.ext hgA).symm)
  rw [← this]
  exact hx

theorem heisB12_le_outerHeisClosure_of_large
    (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (h17 : 17 ≤ ℓ ^ f) {ω α : K}
    (hω : IsPrimitiveRoot ω 3) (hαN : α ^ (ℓ ^ f + 1) = 1) (hnc : ¬ ∃ μ : K, μ ^ 3 = α) :
    heisB12 ℓ f K ≤ outerHeisClosure ℓ f K ω α := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h3f : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
    omega
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hbω : h.bar ω = ω ^ 2 := bar_eq_sq_of_cube h hq3 hω3
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hαN
  have hαb : h.bar α * α = 1 := by rw [bar_mul_self_eq_pow]; exact hαN
  obtain ⟨a, ha⟩ := exists_orderOf_eq h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    omega
  have hna : h.bar a * a = 1 := by
    rw [bar_mul_self_eq_pow, ← ha]
    exact pow_orderOf_eq_one a
  have hinvN : ∀ x : K, h.bar x * x = 1 → h.bar x⁻¹ * x⁻¹ = 1 := fun x hx => by
    rw [map_inv₀, ← mul_inv, hx, inv_one]
  have hsqN : ∀ x : K, h.bar x * x = 1 → h.bar (x ^ 2) * x ^ 2 = 1 := fun x hx => by
    rw [map_pow, ← mul_pow, hx, one_pow]
  obtain ⟨y, hyc, c₀, c₁, c₂, hcirc, hc0, hc1, hc2, hnot⟩ :=
    exists_generic_element h hq3 (by omega) hω hαN hnc
  obtain ⟨ge1, hge1⟩ := exists_homology_su h (ρ := a) (lam := a⁻¹ ^ 2) (n := 1) ![1, 0, 0]
    hna (hsqN _ (hinvN a hna)) (by field_simp) one_ne_zero (by simp)
  obtain ⟨ge3, hge3⟩ := exists_homology_su h (ρ := a) (lam := a⁻¹ ^ 2) (n := 1) ![0, 0, 1]
    hna (hsqN _ (hinvN a hna)) (by field_simp) one_ne_zero (by simp)
  have hDm : heisD ω ∈ outerHeisLines ω α := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hD' : heisD ω = hD ω := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisD, hD]
  have he1 : (![1, 0, 0] : Fin 3 → K) = Pi.single 0 1 := by
    ext j
    fin_cases j <;> simp
  have he3 : (![0, 0, 1] : Fin 3 → K) = Pi.single 2 1 := by
    ext j
    fin_cases j <;> simp
  have hge1c : ge1 ∈ outerHeisClosure ℓ f K ω α :=
    Subgroup.subset_closure ⟨_, hDm, mem_FixU_of_mul_comm (by
      rw [hge1, hD', he1]
      exact homMat_unit_comm_hD h _ _ ω 0)⟩
  have hge3c : ge3 ∈ outerHeisClosure ℓ f K ω α :=
    Subgroup.subset_closure ⟨_, hDm, mem_FixU_of_mul_comm (by
      rw [hge3, hD', he3]
      exact homMat_unit_comm_hD h _ _ ω 2)⟩
  obtain ⟨s, hs, hsc⟩ := exists_shift_mem_outerHeisClosure h hω3 α
  have hmulmat : ∀ u v : unitarySU ℓ f K 3,
      (((u * v : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun u v => rfl
  have hv1 : hS *ᵥ ![0, 0, 1] = (![1, 0, 0] : Fin 3 → K) := by
    ext i
    fin_cases i <;> simp [hS, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hv2 : hS *ᵥ ![1, 0, 0] = (![0, 1, 0] : Fin 3 → K) := by
    ext i
    fin_cases i <;> simp [hS, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hy0 : circMat α c₀ c₁ c₂ *ᵥ ![1, 0, 0] = ![c₀, c₁, c₂] := by
    ext i
    fin_cases i <;> simp [circMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hy1 : circMat α c₀ c₁ c₂ *ᵥ ![0, 1, 0] = ![α * c₂, c₀, c₁] := by
    ext i
    fin_cases i <;> simp [circMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hy2 : circMat α c₀ c₁ c₂ *ᵥ ![0, 0, 1] = ![α * c₁, α * c₂, c₀] := by
    ext i
    fin_cases i <;> simp [circMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hsmat : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS := hs
  have hge1' : ∃ g ∈ outerHeisClosure ℓ f K ω α, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0] := ⟨ge1, hge1c, by rw [hge1, div_one]⟩
  have hge3' : ∃ g ∈ outerHeisClosure ℓ f K ω α, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1] := ⟨ge3, hge3c, by rw [hge3, div_one]⟩
  by_cases h2 : h.bar c₂ * c₂ = 1
  · by_cases h1 : h.bar c₁ * c₁ = 1
    ·
      have h0 : h.bar c₀ * c₀ ≠ 1 := fun h0 => hnot ⟨h0, h1, h2⟩
      have hw : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1] =
          ![α * c₁, α * c₂, c₀] := by rw [hcirc, hy2]
      refine heisB12_le_of_generic_column h hq3 hℓ3 h17 ha hge1' hge3' hyc ?_ ?_ ?_ ?_
      · rw [hw]; simpa using ⟨hα0, hc1⟩
      · rw [hw]; simpa using ⟨hα0, hc2⟩
      · rw [hw]; simpa using hc0
      · rw [hw]; simpa using h0
    ·
      have hw : (((y * s * s : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ![0, 0, 1] = ![α * c₂, c₀, c₁] := by
        rw [hmulmat, hmulmat, hsmat, hcirc, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hv1, hv2, hy1]
      refine heisB12_le_of_generic_column h hq3 hℓ3 h17 ha hge1' hge3' (y := y * s * s)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyc hsc) hsc) ?_ ?_ ?_ ?_
      · rw [hw]; simpa using ⟨hα0, hc2⟩
      · rw [hw]; simpa using hc0
      · rw [hw]; simpa using hc1
      · rw [hw]; simpa using h1
  ·
    have hw : (((y * s : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ![0, 0, 1] = ![c₀, c₁, c₂] := by
      rw [hmulmat, hsmat, hcirc, ← Matrix.mulVec_mulVec, hv1, hy0]
    refine heisB12_le_of_generic_column h hq3 hℓ3 h17 ha hge1' hge3' (y := y * s)
      (Subgroup.mul_mem _ hyc hsc) ?_ ?_ ?_ ?_
    · rw [hw]; simpa using hc0
    · rw [hw]; simpa using hc1
    · rw [hw]; simpa using hc2
    · rw [hw]; simpa using h2


end CFSG.LieType.SeitzGeneration
