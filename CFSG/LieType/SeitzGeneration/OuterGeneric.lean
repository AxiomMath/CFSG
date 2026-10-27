module

public import CFSG.LieType.SeitzGeneration.OuterCirc
public import CFSG.LieType.SeitzGeneration.UnitaryOuterB12
public import CFSG.LieType.SeitzGeneration.UnitaryHeisSeed
public import CFSG.LieType.SeitzGeneration.OuterHeisFixedUnitary

public section

open scoped commutatorElement MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryModel

namespace CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_heisD_su (h : UnitaryFieldData ℓ f K) {ω : K} (hω3 : ω ^ 3 = 1)
    (hωb : h.bar ω * ω = 1) :
    ∃ g : unitarySU ℓ f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisD ω := by
  have hU := heisD_unitary h hωb
  have hd : (heisD ω).det = 1 := by rw [det_heisD, hω3]
  exact ⟨⟨⟨heisD ω, ((heisD ω).map h.bar)ᵀ, mul_eq_one_comm.2 hU, hU⟩,
    (mem_unitarySU_iff h).2 ⟨hd, hU⟩⟩, rfl⟩

theorem generic_element_of_circ (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    {ω α : K} (hω : IsPrimitiveRoot ω 3) (hαN : α ^ (ℓ ^ f + 1) = 1)
    (hnc : ¬ ∃ μ : K, μ ^ 3 = α) {x₀ x₁ x₂ : K}
    (hU : ((circMat α x₀ x₁ x₂).map h.bar)ᵀ * circMat α x₀ x₁ x₂ = 1) (hx1 : x₁ ≠ 0)
    (hx2 : x₂ ≠ 0) :
    ∃ y : unitarySU ℓ f K 3, y ∈ outerHeisClosure ℓ f K ω α ∧
      ∃ c₀ c₁ c₂ : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = circMat α c₀ c₁ c₂ ∧
        c₀ ≠ 0 ∧ c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
        ¬ (h.bar c₀ * c₀ = 1 ∧ h.bar c₁ * c₁ = 1 ∧ h.bar c₂ * c₂ = 1) := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hαb : h.bar α * α = 1 := by rw [bar_mul_self_eq_pow]; exact hαN
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hαb
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hbω : h.bar ω = ω ^ 2 := bar_eq_sq_of_cube h hq3 hω3
  have hωb : h.bar ω * ω = 1 := by rw [hbω]; linear_combination hω3
  set gm : Matrix (Fin 3) (Fin 3) K := circMat α x₀ x₁ x₂ with hgm
  set gS : Matrix (Fin 3) (Fin 3) K := (gm.map h.bar)ᵀ with hgS
  have hgg : gm * gS = 1 := mul_eq_one_comm.2 hU
  let gGL : GL (Fin 3) K := ⟨gm, gS, hgg, hU⟩
  have hgP : gGL ∈ primeFormUnitary h (idGram K 3) := by
    rw [mem_primeFormUnitary]
    simpa [idGram] using hU
  let P : primeFormUnitary h (idGram K 3) := ⟨gGL, hgP⟩
  obtain ⟨Ds, hDs⟩ := exists_heisD_su h hω3 hωb
  have hD' : heisD ω = !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisD]
  have hDC : heisD ω * heisC α = ω • (heisC α * heisD ω) := by
    rw [hD']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have hDsF : Ds ∈ FixU ℓ f K (heisC α) := ⟨ω, by rw [hDs]; exact hDC⟩
  have hgC : gm * heisC α = heisC α * gm := circMat_comm α x₀ x₁ x₂
  have hMN : heisC α * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * heisC α := hgC.symm
  have hz : conjSU h P Ds ∈ FixU ℓ f K (heisC α) := mem_FixU_conj h P hMN hDsF
  have hCm : heisC α ∈ outerHeisLines ω α := Set.mem_insert _ _
  have hDm : heisD ω ∈ outerHeisLines ω α := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hzc : conjSU h P Ds ∈ outerHeisClosure ℓ f K ω α :=
    Subgroup.subset_closure ⟨_, hCm, hz⟩
  have hDc : Ds ∈ outerHeisClosure ℓ f K ω α :=
    Subgroup.subset_closure ⟨_, hDm, ⟨1, by rw [hDs, one_smul]⟩⟩
  refine ⟨conjSU h P Ds * Ds⁻¹, Subgroup.mul_mem _ hzc (Subgroup.inv_mem _ hDc), ?_⟩
  set y : unitarySU ℓ f K 3 := conjSU h P Ds * Ds⁻¹ with hy
  set ym : Matrix (Fin 3) (Fin 3) K := ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hym
  have hymat : ym = gm * heisD ω * gS * ((heisD ω).map h.bar)ᵀ := by
    rw [hym, hy, Subgroup.coe_mul, Units.val_mul, val_inv_eq_star h Ds, hDs, coe_conjSU,
      Units.val_mul, Units.val_mul, hDs]
    rfl
  have hyU := ((mem_unitarySU_iff h).1 y.2).2
  have hyd := ((mem_unitarySU_iff h).1 y.2).1
  have hDstar : ((heisD ω).map h.bar)ᵀ = !![1, 0, 0; 0, ω ^ 2, 0; 0, 0, ω] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisD, hbω]
    grind
  have hDsC : ((heisD ω).map h.bar)ᵀ * heisC α =
      ω ^ 2 • (heisC α * ((heisD ω).map h.bar)ᵀ) := by
    rw [hDstar]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have hgSC : gS * heisC α = heisC α * gS := by
    calc gS * heisC α = gS * heisC α * (gm * gS) := by rw [hgg, Matrix.mul_one]
      _ = gS * (heisC α * gm) * gS := by simp only [Matrix.mul_assoc]
      _ = gS * (gm * heisC α) * gS := by rw [hgC]
      _ = (gS * gm) * heisC α * gS := by simp only [Matrix.mul_assoc]
      _ = heisC α * gS := by rw [hU, Matrix.one_mul]
  have hyC : ym * heisC α = heisC α * ym := by
    rw [hymat]
    calc gm * heisD ω * gS * ((heisD ω).map h.bar)ᵀ * heisC α
        = gm * heisD ω * gS * (((heisD ω).map h.bar)ᵀ * heisC α) := by
          simp only [Matrix.mul_assoc]
      _ = gm * heisD ω * gS * (ω ^ 2 • (heisC α * ((heisD ω).map h.bar)ᵀ)) := by rw [hDsC]
      _ = ω ^ 2 • (gm * heisD ω * (gS * heisC α) * ((heisD ω).map h.bar)ᵀ) := by
          simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = ω ^ 2 • (gm * heisD ω * (heisC α * gS) * ((heisD ω).map h.bar)ᵀ) := by rw [hgSC]
      _ = ω ^ 2 • (gm * (heisD ω * heisC α) * gS * ((heisD ω).map h.bar)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = ω ^ 2 • (gm * (ω • (heisC α * heisD ω)) * gS * ((heisD ω).map h.bar)ᵀ) := by
          rw [hDC]
      _ = (ω ^ 2 * ω) • (gm * heisC α * heisD ω * gS * ((heisD ω).map h.bar)ᵀ) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      _ = (1 : K) • (heisC α * gm * heisD ω * gS * ((heisD ω).map h.bar)ᵀ) := by
          rw [hgC, show ω ^ 2 * ω = 1 by linear_combination hω3]
      _ = heisC α * (gm * heisD ω * gS * ((heisD ω).map h.bar)ᵀ) := by
          simp only [one_smul, Matrix.mul_assoc]
  obtain ⟨c₀, c₁, c₂, hcirc⟩ : ∃ c₀ c₁ c₂ : K, ym = circMat α c₀ c₁ c₂ :=
    ⟨_, _, _, eq_circMat_of_comm hyC⟩
  have hU' : ((circMat α c₀ c₁ c₂).map h.bar)ᵀ * circMat α c₀ c₁ c₂ = 1 := by
    rw [← hcirc]
    exact hyU
  have hdet : c₀ ^ 3 + α * c₁ ^ 3 + α ^ 2 * c₂ ^ 3 - 3 * α * c₀ * c₁ * c₂ = 1 := by
    rw [← det_circMat, ← hcirc]
    exact hyd
  have hnsc : ¬ (c₁ = 0 ∧ c₂ = 0) := by
    rintro ⟨h1, h2⟩
    have hsc : ym = c₀ • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [hcirc, h1, h2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [circMat]
    have hDD : ((heisD ω).map h.bar)ᵀ * heisD ω = 1 := heisD_unitary h hωb
    have e1 : gm * heisD ω * gS = c₀ • heisD ω := by
      calc gm * heisD ω * gS
          = (gm * heisD ω * gS * ((heisD ω).map h.bar)ᵀ) * heisD ω := by
            rw [Matrix.mul_assoc _ ((heisD ω).map h.bar)ᵀ, hDD, Matrix.mul_one]
        _ = ym * heisD ω := by rw [← hymat]
        _ = c₀ • heisD ω := by rw [hsc, Matrix.smul_mul, Matrix.one_mul]
    have e2 : gm * heisD ω = c₀ • (heisD ω * gm) := by
      calc gm * heisD ω = gm * heisD ω * (gS * gm) := by rw [hU, Matrix.mul_one]
        _ = (gm * heisD ω * gS) * gm := by simp only [Matrix.mul_assoc]
        _ = (c₀ • heisD ω) * gm := by rw [e1]
        _ = c₀ • (heisD ω * gm) := by rw [Matrix.smul_mul]
    have e21 := congrFun (congrFun e2 1) 0
    have e22 := congrFun (congrFun e2 2) 0
    rw [hD'] at e21 e22
    simp [hgm, circMat, Matrix.mul_apply, Fin.sum_univ_three] at e21 e22
    have h1' : c₀ * ω = 1 := mul_left_cancel₀ hx1 (by linear_combination (-1 : K) * e21)
    have h2' : c₀ * ω ^ 2 = 1 := mul_left_cancel₀ hx2 (by linear_combination (-1 : K) * e22)
    exact hω1 (by linear_combination (-ω) * h1' + h2')
  obtain ⟨hA0, hA1, hA2⟩ := circ_coord_ne_zero h hαb hU'
  have hc1 : c₁ ≠ 0 := by
    intro h1
    have h2 : c₂ ≠ 0 := fun h2 => hnsc ⟨h1, h2⟩
    have h0 : c₀ = 0 := (hA1 h1).resolve_right h2
    apply hnc
    refine ⟨α * c₂, ?_⟩
    rw [h0, h1] at hdet
    linear_combination α * hdet
  have hc2 : c₂ ≠ 0 := by
    intro h2
    have h1 : c₁ ≠ 0 := hc1
    have h0 : c₀ = 0 := (hA2 h2).resolve_right h1
    apply hnc
    refine ⟨c₁⁻¹, ?_⟩
    rw [h0, h2] at hdet
    field_simp
    linear_combination -hdet
  have hc0 : c₀ ≠ 0 := by
    intro h0
    rcases hA0 h0 with h | h
    · exact hc1 h
    · exact hc2 h
  exact ⟨c₀, c₁, c₂, hcirc, hc0, hc1, hc2, circ_not_all_norm_one h hαb hnc hU'⟩

theorem exists_generic_element (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) {ω α : K} (hω : IsPrimitiveRoot ω 3) (hαN : α ^ (ℓ ^ f + 1) = 1)
    (hnc : ¬ ∃ μ : K, μ ^ 3 = α) :
    ∃ y : unitarySU ℓ f K 3, y ∈ outerHeisClosure ℓ f K ω α ∧
      ∃ c₀ c₁ c₂ : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = circMat α c₀ c₁ c₂ ∧
        c₀ ≠ 0 ∧ c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
        ¬ (h.bar c₀ * c₀ = 1 ∧ h.bar c₁ * c₁ = 1 ∧ h.bar c₂ * c₂ = 1) := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  have hαb : h.bar α * α = 1 := by rw [bar_mul_self_eq_pow]; exact hαN
  obtain ⟨β, hβ0, hβN⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK hq
  have hβN' : h.bar β * β ≠ 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply] at hβN
    exact hβN
  have hbβ0 : h.bar β ≠ 0 := by simpa using hβ0
  have hρ0 : 1 - α * h.bar β ^ 3 ≠ 0 := by
    intro h0
    apply hnc
    refine ⟨(h.bar β)⁻¹, ?_⟩
    have : α * h.bar β ^ 3 = 1 := by linear_combination -h0
    field_simp
    linear_combination -this
  have hU := blaschke_unitary h hαb hρ0
  have hx1 : (1 - β * h.bar β) / (1 - α * h.bar β ^ 3) ≠ 0 := by
    refine div_ne_zero ?_ hρ0
    intro h0
    apply hβN'
    linear_combination -h0
  have hx2 : h.bar β * (1 - β * h.bar β) / (1 - α * h.bar β ^ 3) ≠ 0 := by
    have : h.bar β * (1 - β * h.bar β) / (1 - α * h.bar β ^ 3) =
        h.bar β * ((1 - β * h.bar β) / (1 - α * h.bar β ^ 3)) := by ring
    rw [this]
    exact mul_ne_zero hbβ0 hx1
  exact generic_element_of_circ h hq3 hω hαN hnc hU hx1 hx2

theorem exists_shift_mem_outerHeisClosure (h : UnitaryFieldData ℓ f K) {ω : K} (hω3 : ω ^ 3 = 1)
    (α : K) :
    ∃ s : unitarySU ℓ f K 3, ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS ∧
      s ∈ outerHeisClosure ℓ f K ω α := by
  obtain ⟨s, hs⟩ := exists_shift_su h
  have hDm : heisD ω ∈ outerHeisLines ω α := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hD' : heisD ω = hD ω := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisD, hD]
  refine ⟨s, hs, Subgroup.subset_closure ⟨_, hDm, ⟨ω ^ 2, ?_⟩⟩⟩
  rw [hs, hD']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hS, hD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

end CFSG.LieType.SeitzGeneration
