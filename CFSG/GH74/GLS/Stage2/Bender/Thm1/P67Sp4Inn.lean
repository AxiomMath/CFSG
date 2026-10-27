module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Act
public import CFSG.GH74.GLS.Stage2.OddAut.FixStep
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.Stage2.OddAut CFSG.RankThree.PartTwo.KFacts

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

variable {K : Type} [Field K]

theorem exists_lift_pow_eq_one {p : ℕ} (hp : Odd p) {g : StatedProj (StatedSp 2 K)}
    (hg : g ^ p = 1) :
    ∃ u : StatedSp 2 K, proj 2 K u = g ∧ u ^ p = 1 := by
  obtain ⟨u0, rfl⟩ := QuotientGroup.mk'_surjective (spScalars 2 K) g
  have hs : proj 2 K (u0 ^ p) = 1 := by
    rw [map_pow]
    exact hg
  have hs2 := sq_eq_one_of_proj_eq_one hs
  refine ⟨u0 ^ (p + 1), ?_, ?_⟩
  · show (QuotientGroup.mk' (spScalars 2 K)) (u0 ^ (p + 1)) = _
    rw [map_pow, pow_succ, hg, one_mul]
  · obtain ⟨m, hm⟩ := hp
    rw [← pow_mul, show (p + 1) * p = p * (p + 1) by ring, pow_mul,
      show p + 1 = 2 * (m + 1) by omega,
      pow_mul, hs2, one_pow]

open CFSG.RankThree.PartTwo.KFacts in
noncomputable def fieldPart (hodd : ringChar K ≠ 2) [Finite K]
    (α : MulAut (StatedProj (StatedSp 2 K))) : K ≃+* K :=
  Classical.choose (Classical.choose_spec (psp4_odd_automorphism_normal_form hodd α))

theorem fieldPart_spec (hodd : ringChar K ≠ 2) [Finite K] (α : MulAut (StatedProj (StatedSp 2 K))) :
    ∃ A : gsp 2 K, α = conjAut 2 K A * fieldAut 2 K (fieldPart hodd α) :=
  ⟨Classical.choose (psp4_odd_automorphism_normal_form hodd α),
    Classical.choose_spec (Classical.choose_spec (psp4_odd_automorphism_normal_form hodd α))⟩

theorem fieldPart_unique (hodd : ringChar K ≠ 2) [Finite K] {α : MulAut (StatedProj (StatedSp 2 K))}
    {A : gsp 2 K} {σ : K ≃+* K} (h : α = conjAut 2 K A * fieldAut 2 K σ) :
    fieldPart hodd α = σ := by
  obtain ⟨B, hB⟩ := fieldPart_spec hodd α
  set τ := fieldPart hodd α
  rw [h] at hB
  have h1 : conjAut 2 K (B⁻¹ * A) = fieldAut 2 K τ * (fieldAut 2 K σ)⁻¹ := by
    rw [map_mul, map_inv]
    have h2 : (conjAut 2 K B)⁻¹ * (conjAut 2 K A * fieldAut 2 K σ) = fieldAut 2 K τ := by
      rw [hB]; group
    calc (conjAut 2 K B)⁻¹ * conjAut 2 K A
        = ((conjAut 2 K B)⁻¹ * (conjAut 2 K A * fieldAut 2 K σ)) * (fieldAut 2 K σ)⁻¹ := by group
      _ = _ := by rw [h2]
  have h3 : fieldAut 2 K (τ * σ⁻¹) = conjAut 2 K (B⁻¹ * A) := by
    rw [h1, map_mul, map_inv]
  have h4 := (fieldAut_mem_range_conjAut_iff (r := 2) (K := K) (by norm_num)).mp
    ⟨B⁻¹ * A, h3.symm⟩
  exact mul_inv_eq_one.mp h4


noncomputable def fieldPartHom (hodd : ringChar K ≠ 2) [Finite K] :
    MulAut (StatedProj (StatedSp 2 K)) →* (K ≃+* K) where
  toFun := fieldPart hodd
  map_one' := fieldPart_unique hodd (A := 1) (σ := 1) (by simp)
  map_mul' α β := by
    obtain ⟨A, hA⟩ := fieldPart_spec hodd α
    obtain ⟨B, hB⟩ := fieldPart_spec hodd β
    generalize fieldPart hodd α = σ at hA ⊢
    generalize fieldPart hodd β = τ at hB ⊢
    have hcomm : fieldAut 2 K σ * conjAut 2 K B =
        conjAut 2 K (gspFieldMap σ B) * fieldAut 2 K σ := by
      rw [← fieldAut_mul_conjAut_mul_inv σ B]; group
    have : α * β = conjAut 2 K (A * gspFieldMap σ B) * fieldAut 2 K (σ * τ) := by
      rw [hA, hB, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (fieldAut 2 K σ), hcomm]
      group
    exact fieldPart_unique hodd this

theorem exists_sp_conj_sq [Finite K] (A : gsp 2 K) :
    ∃ x : StatedSp 2 K, conjAut 2 K A ^ 2 = MulAut.conj (proj 2 K x) := by
  set μ : Kˣ := multiplier 2 K A with hμ
  set Sc : gsp 2 K := ⟨GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) μ⁻¹, scalar_mem_gsp μ⁻¹⟩ with hSc
  set B : gsp 2 K := A ^ 2 * Sc with hB
  have hmSc : multiplier 2 K Sc = μ⁻¹ * μ⁻¹ := by
    apply multiplier_eq
    have h : ((Sc : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((μ⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      show mx (GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) μ⁻¹) = _
      simp only [mx, GeneralLinearGroup.coe_scalar]
      rw [smul_one_eq_diagonal]
      rfl
    rw [h, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, Units.val_mul]
  have hmB : multiplier 2 K B = 1 := by
    rw [hB, map_mul, map_pow, hmSc, ← hμ]
    group
  have hBS : (B : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedSp 2 K := by
    have : B ∈ (multiplier 2 K).ker := hmB
    rw [ker_multiplier] at this
    exact this
  refine ⟨⟨B, hBS⟩, ?_⟩
  rw [← conjAut_statedSp]
  have : (⟨(⟨B, hBS⟩ : StatedSp 2 K), statedSp_le_gsp (⟨B, hBS⟩ : StatedSp 2 K).2⟩ : gsp 2 K) = B :=
    Subtype.ext rfl
  rw [this, hB, map_mul, map_pow, hSc, conjAut_scalar_eq_one, mul_one]


theorem exists_conj_of_conjAut_pow [Finite K] {r : ℕ} (hr2 : Odd r) (A : gsp 2 K)
    (hAr : conjAut 2 K A ^ r = 1) :
    ∃ g : StatedProj (StatedSp 2 K), MulAut.conj g = conjAut 2 K A := by
  obtain ⟨x, hx⟩ := exists_sp_conj_sq A
  obtain ⟨m, hm⟩ := hr2
  refine ⟨(proj 2 K x) ^ (m + 1), ?_⟩
  rw [map_pow, ← hx, ← pow_mul, show 2 * (m + 1) = r + 1 by omega, pow_succ, hAr, one_mul]

theorem exists_inn_mem [Finite K] (hodd : ringChar K ≠ 2) {p n : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ n) {r : ℕ} (hr : r.Prime) (hr2 : Odd r)
    {V : Subgroup (MulAut (StatedProj (StatedSp 2 K)))} [IsElementaryAbelian r ↥V]
    (hVc : Nat.card ↥V = r ^ 2) :
    ∃ g : StatedProj (StatedSp 2 K), g ≠ 1 ∧ MulAut.conj g ∈ V := by
  have hcyc : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).2
  obtain ⟨v, hvV, hv1, hvk⟩ := exists_ne_one_mem_ker hr hVc (fieldPartHom hodd)
  obtain ⟨A, hA⟩ := fieldPart_spec hodd v
  have hvk' : fieldPart hodd v = 1 := hvk
  rw [hvk', map_one, mul_one] at hA
  have hvr : v ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian v hvV
  have hAr : conjAut 2 K A ^ r = 1 := by rw [← hA]; exact hvr
  obtain ⟨g, hg⟩ := exists_conj_of_conjAut_pow hr2 A hAr
  refine ⟨g, ?_, ?_⟩
  · intro h
    apply hv1
    rw [hA, ← hg, h, map_one]
  · rw [hg, ← hA]
    exact hvV

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
