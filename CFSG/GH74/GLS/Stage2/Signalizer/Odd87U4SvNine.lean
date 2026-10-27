module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Pointwise

section Cyc

variable {K : Type} [Field K]

@[expose] def cyc9 (w : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, w, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, w⁻¹]

theorem cyc9_det (w : K) (hw : w ≠ 0) : (cyc9 w).det = 1 := by
  rw [cyc9, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  have h : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
  simp [h, hw]

theorem cyc9_sq (w : K) :
    cyc9 w * cyc9 w = !![0, w, 0, 0; 0, 0, w, 0; 1, 0, 0, 0; 0, 0, 0, w⁻¹ * w⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc9, Matrix.mul_apply, Fin.sum_univ_four]

theorem cyc9_cube (w : K) :
    cyc9 w * cyc9 w * cyc9 w = diagonal ![w, w, w, w⁻¹ * w⁻¹ * w⁻¹] := by
  rw [cyc9_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc9, Matrix.mul_apply, Fin.sum_univ_four]

theorem cyc9_cube_of_pow_three {w : K} (hw : w ^ 3 = 1) :
    cyc9 w ^ 3 = diagonal ![w, w, w, 1] := by
  have h1 : w⁻¹ * w⁻¹ * w⁻¹ = 1 := by
    rw [← mul_inv, ← mul_inv, ← pow_three', hw, inv_one]
  rw [pow_three', cyc9_cube, h1]

theorem cyc9_pow_nine {w : K} (hw : w ^ 3 = 1) : cyc9 w ^ 9 = 1 := by
  rw [show 9 = 3 * 3 by norm_num, pow_mul, cyc9_cube_of_pow_three hw, diagonal_pow]
  have : (![w, w, w, 1] : Fin 4 → K) ^ 3 = 1 := by
    ext i
    fin_cases i <;> simp [hw]
  rw [this]
  exact diagonal_one

theorem cyc9_unitary (σ : K →+* K) {w : K} (hw : σ w * w = 1) :
    ((cyc9 w).map σ)ᵀ * cyc9 w = 1 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have h2 : (σ w)⁻¹ * w⁻¹ = 1 := by
    rw [← mul_inv, hw, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc9, Matrix.mul_apply, Fin.sum_univ_four, hw, h2]

end Cyc

section Nine

variable {p₀ f₀ : ℕ} {K : Type} [Field K]

theorem exists_orderOf_nine_hypSU (h : UnitaryFieldData p₀ f₀ K) (hq : p₀ ^ f₀ = 5) :
    ∃ g : ↥(hypSU h 2 0), orderOf g = 9 := by
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card K = 25 := by rw [h.card, pow_mul', hq]; norm_num
  have hU : Nat.card Kˣ = 24 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hU]; norm_num)
  have hω3 : (ω : K) ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one ω
    rw [hω] at h1
    simpa using congrArg Units.val h1
  have hω1 : (ω : K) ≠ 1 := by
    intro h1
    have : ω = 1 := Units.ext h1
    rw [this, orderOf_one] at hω
    norm_num at hω
  have hnorm : h.bar (ω : K) * (ω : K) = 1 := by
    rw [h.bar_apply, hq]
    calc (ω : K) ^ 5 * ω = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3]; norm_num
  have hdet := cyc9_det (ω : K) ω.ne_zero
  let s : SL(4, K) := ⟨cyc9 (ω : K), hdet⟩
  let A : GL (Fin 4) K := Matrix.SpecialLinearGroup.toGL s
  have hAmem : A ∈ unitarySU p₀ f₀ K 4 := by
    rw [mem_unitarySU_iff h]
    exact ⟨hdet, cyc9_unitary (h.bar : K →+* K) hnorm⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  refine ⟨(hypTransport h hR).symm ⟨A, hAmem⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  have hA3 : (A : Matrix (Fin 4) (Fin 4) K) ^ 3 = diagonal ![(ω : K), ω, ω, 1] :=
    cyc9_cube_of_pow_three hω3
  have hnot : ¬ A ^ 3 ^ 1 = 1 := by
    intro h1
    have h2 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) h1
    simp only [pow_one, Units.val_pow_eq_pow_val, Units.val_one, hA3] at h2
    have h3 := congrFun (congrFun h2 0) 0
    simp at h3
    exact hω1 (Units.val_eq_one.2 h3)
  have hfin : A ^ 3 ^ (1 + 1) = 1 := by
    refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    exact cyc9_pow_nine hω3
  rw [orderOf_eq_prime_pow hnot hfin]
  norm_num

end Nine

section Sylow

theorem exists_pow_three_ne_one_of_card_81 {G : Type*} [Group G] [Finite G]
    (hG : (Nat.card G).factorization 3 = 4) {g : G} (hg : orderOf g = 9) {X : Subgroup G}
    (hcard : Nat.card X = 81) : ∃ x ∈ X, x ^ 3 ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  let SX : Sylow 3 G := Sylow.ofCard X (by rw [hcard, hG]; norm_num)
  have hQ : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hg]; norm_num : Nat.card (Subgroup.zpowers g) = 3 ^ 2)
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G SX S
  have hgS : g ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers g)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hgS
  obtain ⟨x, hx, hxg⟩ := hgS
  have hx' : x ∈ X := hx
  have h3 : g ^ 3 = 1 := by
    rw [← hxg, MulAut.smul_def, ← map_pow, hcon x hx', map_one]
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg] at this
  norm_num at this

end Sylow

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
