module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFU4N
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Graph
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Diag

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.U4

open Matrix CFSG.ClassicalInvolution.Q3.Q3MFOU4 CFSG.ClassicalInvolution.Q3.Q3PP
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

section Gram

theorem gram_entry (col : Fin 4 → (Fin 4 → F9)) (i j : Fin 4) :
    (((Matrix.of fun r c => col c r).map σ9)ᵀ * Matrix.of fun r c => col c r) i j =
      hf (col i) (col j) := by
  simp only [Matrix.mul_apply, transpose_apply, Matrix.map_apply, Matrix.of_apply, hf, vstar,
    dotProduct]

theorem bf_entry (G : Matrix (Fin 4) (Fin 4) F9) (col : Fin 4 → (Fin 4 → F9)) (i j : Fin 4) :
    ((Matrix.of fun r c => col c r)ᵀ * G * Matrix.of fun r c => col c r) i j =
      bf G (col i) (col j) := by
  simp only [Matrix.mul_apply, transpose_apply, Matrix.of_apply, bf, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem exists_unitary_gram {G : Matrix (Fin 4) (Fin 4) F9} (hgu : (G.map σ9)ᵀ * G = 1)
    (halt : Gᵀ = -G) :
    ∃ M : Matrix (Fin 4) (Fin 4) F9, (M.map σ9)ᵀ * M = 1 ∧ Mᵀ * G * M = Gmat 1 1 := by
  classical
  set v₁ : Fin 4 → F9 := Pi.single 0 1 with hv₁
  set v₂ := tau G v₁ with hv₂
  have h11 : hf v₁ v₁ = 1 := hf_single
  have h22 : hf v₂ v₂ = 1 := by rw [hv₂, hf_tau_tau hgu halt, h11]
  have h12 : hf v₁ v₂ = 0 := hf_tau_self halt v₁
  obtain ⟨v₃, h13, h23, h33⟩ := exists_unit_of_orth h11 h22 h12
  set v₄ := tau G v₃ with hv₄
  have h44 : hf v₄ v₄ = 1 := by rw [hv₄, hf_tau_tau hgu halt, h33]
  have h34 : hf v₃ v₄ = 0 := hf_tau_self halt v₃
  have b13 : bf G v₁ v₃ = 0 := by rw [← hf_tau_left halt, ← hv₂, h23]
  have h14 : hf v₁ v₄ = 0 := by rw [hv₄, hf_tau_right, b13, map_zero, neg_zero]
  have b14 : bf G v₁ v₄ = 0 := by
    rw [bf_skew halt, hv₄, bf_tau_left hgu, hf_swap, h13, map_zero, neg_neg]
  have h24 : hf v₂ v₄ = 0 := by rw [hv₂, hf_tau_left halt, b14]
  have b12 : bf G v₁ v₂ = 1 := by rw [hv₂, bf_tau_self hgu halt, h11]
  have b34 : bf G v₃ v₄ = 1 := by rw [hv₄, bf_tau_self hgu halt, h33]
  have b23 : bf G v₂ v₃ = 0 := by rw [hv₂, bf_tau_left hgu, h13, neg_zero]
  have b24 : bf G v₂ v₄ = 0 := by rw [hv₂, bf_tau_left hgu, h14, neg_zero]
  have hs : ∀ x y : Fin 4 → F9, hf x y = 0 → hf y x = 0 := fun x y h => by
    rw [hf_swap, h, map_zero]
  have bs : ∀ x y : Fin 4 → F9, bf G x y = 0 → bf G y x = 0 := fun x y h => by
    rw [bf_skew halt, h, neg_zero]
  have bs1 : ∀ x y : Fin 4 → F9, bf G x y = 1 → bf G y x = -1 := fun x y h => by
    rw [bf_skew halt, h]
  set col : Fin 4 → (Fin 4 → F9) := ![v₁, v₂, v₃, v₄] with hcol
  refine ⟨Matrix.of fun r c => col c r, ?_, ?_⟩
  · ext i j
    rw [gram_entry]
    fin_cases i <;> fin_cases j <;>
      simp [hcol, h11, h22, h33, h44, h12, h13, h14, h23, h24, h34, hs _ _ h12, hs _ _ h13,
        hs _ _ h14, hs _ _ h23, hs _ _ h24, hs _ _ h34]
  · ext i j
    rw [bf_entry]
    fin_cases i <;> fin_cases j <;>
      simp [hcol, Gmat, bf_self halt, b12, b13, b14, b23, b24, b34, bs _ _ b13, bs _ _ b14,
        bs _ _ b23, bs _ _ b24, bs1 _ _ b12, bs1 _ _ b34]

end Gram

section Bar

theorem oddCoreIn_fixed_bar_alt (hSp : CFSG.Open.IsQuasisimple (StatedSp 2 F3))
    (hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F3)))
    (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (α : Su F9 3 1 4 →* Su F9 3 1 4)
    (hρmk : ∀ x : Su F9 3 1 4, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x))
    {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * σ9.mapMatrix (suMat x) * Gi)
    (hgu : (G.map σ9)ᵀ * G = 1) (halt : Gᵀ = -G) : oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  classical
  obtain ⟨M, hMu, hMG⟩ := exists_unitary_gram hgu halt
  have hMu' : M.map σ9 * Mᵀ = 1 := by
    have h := congrArg transpose hMu
    rw [transpose_mul, transpose_transpose, transpose_one] at h
    exact mul_eq_one_comm.mp h
  have hMu'' : Mᵀ * M.map σ9 = 1 := mul_eq_one_comm.mp hMu'
  set U : GL (Fin 4) F9 := ⟨Mᵀ, M.map σ9, hMu'', hMu'⟩ with hU
  have hUc : (U : Matrix (Fin 4) (Fin 4) F9) = Mᵀ := rfl
  have hUi : ((U⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = M.map σ9 := rfl
  have hUu : cT σ9 (U : Matrix (Fin 4) (Fin 4) F9) * 1 * (U : Matrix (Fin 4) (Fin 4) F9) = 1 := by
    rw [hUc, Matrix.mul_one, cT, ← transpose_map, transpose_transpose]
    exact hMu'
  set cU := conjAut (SUid σ9 4) U (mem_normalizer_SUid hUu) with hcU
  have hcUm : ∀ y : Su F9 3 1 4, suMat (cU y) = Mᵀ * suMat y * M.map σ9 := fun y => rfl
  have hcUi : ∀ y : Su F9 3 1 4, suMat (cU⁻¹ y) = M.map σ9 * suMat y * Mᵀ := fun y => rfl
  set α' : Su F9 3 1 4 →* Su F9 3 1 4 :=
    (cU : Su F9 3 1 4 →* Su F9 3 1 4).comp (α.comp (cU⁻¹ : MulAut (Su F9 3 1 4))) with hα'
  have hαG : ∀ x, suMat (α' x) * Gmat 1 1 = Gmat 1 1 * (suMat x).map σ9 := by
    intro x
    have h1 : suMat (α' x) = Mᵀ * (G * (M * (suMat x).map σ9 * (M.map σ9)ᵀ) * Gi) *
        M.map σ9 := by
      show suMat (cU (α (cU⁻¹ x))) = _
      rw [hcUm, hα, hcUi, RingEquiv.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul,
        map_map_σ9, transpose_map]
    rw [h1, ← hMG]
    calc Mᵀ * (G * (M * (suMat x).map σ9 * (M.map σ9)ᵀ) * Gi) * M.map σ9 * (Mᵀ * G * M)
        = Mᵀ * G * M * (suMat x).map σ9 * ((M.map σ9)ᵀ * (Gi * (M.map σ9 * Mᵀ) * G) * M) := by
          simp only [Matrix.mul_assoc]
      _ = Mᵀ * G * M * (suMat x).map σ9 := by
          rw [hMu', Matrix.mul_one, hGiG, Matrix.mul_one, hMu, Matrix.mul_one]
  obtain ⟨ι, hι, hιb⟩ := exists_iota
  obtain ⟨ζ, hζ⟩ := exists_zeta
  have hn1 : σ9 1 * 1 = (1 : F9) := by rw [map_one, one_mul]
  let D : GraphData := ⟨ι, ζ, 1, 1, hι, hιb, hζ, hn1, hn1⟩
  set cbar := autToCentralQuotient (Su F9 3 1 4) cU with hcbar
  set ρ' := cbar * ρ * cbar⁻¹ with hρ'
  have hρ'mk : ∀ x : Su F9 3 1 4, ρ' (QuotientGroup.mk x) = QuotientGroup.mk (α' x) := by
    intro x
    show cbar (ρ (cbar⁻¹ (QuotientGroup.mk x))) = _
    rw [hcbar, ← map_inv, autToCentralQuotient_mk, hρmk, autToCentralQuotient_mk]
    rfl
  have h' := oddCoreIn_fixed_graph_su4 D hSp hSpZ α' hαG ρ' hρ'mk
  have h'' := oddCoreIn_fixed_conj_eq_bot cbar⁻¹ ρ' h'
  have e : cbar⁻¹ * ρ' * cbar⁻¹⁻¹ = ρ := by rw [hρ', inv_inv]; group
  rwa [e] at h''

end Bar

end CFSG.ClassicalInvolution.Q3.TL4.U4
