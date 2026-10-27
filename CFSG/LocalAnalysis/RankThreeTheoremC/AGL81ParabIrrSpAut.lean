module

import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
import CFSG.GH74.GLS.Stage2.OddAut.HeisField
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open SymplecticHigher (flagStabilizer fieldSp conjSp conjAut fieldAut gsp)

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

theorem exists_conj_fieldSp_of_three_le [Finite K] [CharP K 2] (hr : 3 ≤ r)
    (α : MulAut (StatedSp r K)) :
    ∃ (g : StatedSp r K) (σ : K ≃+* K), ∀ x, α x = g * fieldSp r K σ x * g⁻¹ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let e : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (SymplecticFlag.proj r K)
      ⟨proj_injective, SymplecticHigher.proj_surjective⟩
  let α' : MulAut (StatedProj (StatedSp r K)) := (MulAut.congr e) α
  obtain ⟨A, σ, hA⟩ : ∃ (A : gsp r K) (σ : K ≃+* K), α' = conjAut r K A * fieldAut r K σ :=
    (SymplecticHigher.automorphism_generation (K := K) hr).2 α'
  have hαx : ∀ x : StatedSp r K, α x = conjSp r K A (fieldSp r K σ x) := by
    intro x
    apply proj_injective
    have h2 : SymplecticFlag.proj r K (α x) = α' (SymplecticFlag.proj r K x) := by
      change e (α x) = α' (e x)
      simp [α', MulAut.congr_apply]
    rw [h2, hA]
    rfl
  obtain ⟨μ, hμ⟩ := SymplecticHigher.mem_gsp.mp A.2
  obtain ⟨ν₀, hν₀⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (μ : K)
  have hν₀ne : ν₀ ≠ 0 := by
    rintro rfl
    exact μ.ne_zero (by simpa using hν₀)
  set ν : Kˣ := Units.mk0 ν₀ hν₀ne with hν
  set z : GL (Fin r ⊕ Fin r) K := Matrix.GeneralLinearGroup.scalar _ ν⁻¹ with hz
  have hzc : z ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hzmat : ((z : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((ν⁻¹ : Kˣ) : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [hz, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hmem : z * (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, Units.val_mul, hzmat, Matrix.smul_mul,
      Matrix.one_mul]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hc : ((ν⁻¹ : Kˣ) : K) * ((ν⁻¹ : Kˣ) : K) * (μ : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, hν, Units.val_mk0, hν₀]
      field_simp
    have hJ := hμ
    change (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      SymplecticHigher.formJ r K * ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        (μ : K) • SymplecticHigher.formJ r K at hJ
    rw [hJ, smul_smul, hc, one_smul]
  refine ⟨⟨z * (A : GL (Fin r ⊕ Fin r) K), hmem⟩, σ, fun x => ?_⟩
  apply Subtype.ext
  rw [hαx x, Subgroup.coe_mul, Subgroup.coe_mul, SymplecticHigher.coe_conjSp]
  have hcomm := Subgroup.mem_center_iff.mp hzc
    ((A : GL (Fin r ⊕ Fin r) K) * (fieldSp r K σ x : GL (Fin r ⊕ Fin r) K) *
      (A : GL (Fin r ⊕ Fin r) K)⁻¹)
  have hinv : (((⟨z * (A : GL (Fin r ⊕ Fin r) K), hmem⟩ : StatedSp r K)⁻¹ : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K) = (A : GL (Fin r ⊕ Fin r) K)⁻¹ * z⁻¹ := by
    rw [Subgroup.coe_inv]
    simp [_root_.mul_inv_rev]
  rw [hinv]
  calc (A : GL (Fin r ⊕ Fin r) K) * (fieldSp r K σ x : GL (Fin r ⊕ Fin r) K) *
        (A : GL (Fin r ⊕ Fin r) K)⁻¹
      = (A * (fieldSp r K σ x : GL (Fin r ⊕ Fin r) K) * (A : GL (Fin r ⊕ Fin r) K)⁻¹) * z *
          z⁻¹ := by group
    _ = z * (A * (fieldSp r K σ x : GL (Fin r ⊕ Fin r) K) *
          (A : GL (Fin r ⊕ Fin r) K)⁻¹) * z⁻¹ := by rw [hcomm]
    _ = _ := by group

theorem exists_conj_fieldSp_flag_of_three_le [Finite K] [CharP K 2] (hr : 3 ≤ r)
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {α : MulAut (StatedSp r K)}
    (hα : ∀ x ∈ flagStabilizer r K I, α x ∈ flagStabilizer r K I) :
    ∃ (g : flagStabilizer r K I) (σ : K ≃+* K),
      ∀ x, α x = (g : StatedSp r K) * fieldSp r K σ x * (g : StatedSp r K)⁻¹ := by
  obtain ⟨g, σ, hg⟩ := exists_conj_fieldSp_of_three_le hr α
  have hgQ : g ∈ flagStabilizer r K I := by
    apply mem_flagStabilizer_of_conj_mem hI
    intro q hq
    have h1 : α (fieldSp r K σ⁻¹ q) = g * q * g⁻¹ := by
      rw [hg, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [← h1]
    exact hα _ (fieldSp_mem_flagStabilizer (fun i hi => (hI i hi).2) σ⁻¹ hq)
  exact ⟨⟨g, hgQ⟩, σ, hg⟩

theorem exists_frobenius_two_pow [Finite K] [CharP K 2] (σ : K ≃+* K) :
    ∃ k : ℕ, ∀ a, σ a = a ^ 2 ^ k := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  obtain ⟨k, -, hk⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow Nat.prime_two n.pos
    (by rw [Nat.card_eq_fintype_card]; exact hn) σ
  exact ⟨k, hk⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp
