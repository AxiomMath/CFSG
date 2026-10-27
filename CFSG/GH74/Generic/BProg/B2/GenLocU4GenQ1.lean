module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenPair

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary CFSG.GH74.Generic.BProg.B2.GenLocU4Aux CFSG.GH74.Generic.BProg.B2.GenLocU4Gen Subgroup

namespace GenLocU4Q1

variable {K : Type} [Field K] [Finite K]

theorem q1_in_frame {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (x y : GL (Fin 4) K) (P : GL (Fin 4) K)
    (hP' : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (hxP : ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, -1, 1, 1])
    (hyP : ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0])
    (hX : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * x = x * g → g ∈ Γ)
    (hY : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * y = y * g → g ∈ Γ) : Γ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hge : 1 < p ^ f := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    by_contra hle
    have : p ^ f ≤ 1 := not_lt.mp hle
    nlinarith [Nat.zero_le (p ^ f)]
  have hq3 : 3 ≤ p ^ f := by omega
  have hq2 : p ^ f ≠ 2 := by omega
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hinv := hσ.invol
  obtain ⟨c, s, hc, hs, hcs, hs0⟩ := exists_rot_pair hK hp2 hq3
  obtain ⟨ξ, hξ⟩ := hσ.exists_norm_neg_one
  let Ψ := frameConj (fieldData hK) P hP'
  let Γ₁ : Subgroup (Su K p f 4) := Γ.comap Ψ
  have h0 : ∀ B : Su K p f 2, blockEmb2 K p f 3 0 B ∈ Γ₁ := fun B =>
    hX _ (inBlock_commute P x (-1) 1 hxP 0 (Or.inl rfl) _ (frameBlock_inBlock hK P hP' 0 B))
  have h2 : ∀ B : Su K p f 2, blockEmb2 K p f 3 2 B ∈ Γ₁ := fun B =>
    hX _ (inBlock_commute P x (-1) 1 hxP 2 (Or.inr rfl) _ (frameBlock_inBlock hK P hP' 2 B))
  have hz0 : herm (unitaryInvolution K p f) (![1, ξ, 0, 0] : Fin 4 → K) ![1, ξ, 0, 0] = 0 := by
    rw [herm_def, Fin.sum_univ_four]
    show unitaryInvolution K p f 1 * 1 + unitaryInvolution K p f ξ * ξ + unitaryInvolution K p f 0 * 0 +
      unitaryInvolution K p f 0 * 0 = 0
    rw [map_one, map_zero]
    linear_combination hξ
  have hTz : ∀ (c' : K) (hc' : c' + unitaryInvolution K p f c' = 0), tv hinv hz0 hc' ∈ Γ₁ := by
    intro c' hc'
    refine hX _ (commute_of_frame_commute (P := P) ?_)
    have e1 : P⁻¹ * (Ψ (tv hinv hz0 hc') : GL (Fin 4) K) * P = ((tv hinv hz0 hc' : Su K p f 4) : GL (Fin 4) K) := by
      show P⁻¹ * (P * ((tv hinv hz0 hc' : Su K p f 4) : GL (Fin 4) K) * P⁻¹) * P = _
      group
    rw [e1]
    generalize (P⁻¹ * x * P) = X at hxP ⊢
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hxP]
    show tvMat (unitaryInvolution K p f) _ c' * _ = _ * tvMat (unitaryInvolution K p f) _ c'
    exact tvMat_commute_diag _ _ _ c' (by intro i j; fin_cases i <;> fin_cases j <;> simp)
  have hnorm : unitaryInvolution K p f c * c + unitaryInvolution K p f s * s = 1 := by
    rw [hc, hs]; linear_combination hcs
  have hG : blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) ∈ Γ₁ := by
    refine hY _ (commute_of_frame_commute (P := P) ?_)
    have e1 : P⁻¹ * (Ψ (blockEmb2 K p f 3 1 (su2Of hinv c s hnorm)) : GL (Fin 4) K) * P =
        ((blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) : Su K p f 4) : GL (Fin 4) K) := by
      show P⁻¹ * (P * ((blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) : Su K p f 4) : GL (Fin 4) K) * P⁻¹) * P = _
      group
    rw [e1]
    generalize (P⁻¹ * y * P) = Y at hyP ⊢
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hyP, coe_coe_blockEmb2, su2Of_apply, hs, hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four]
  have hv : herm (unitaryInvolution K p f) (blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) • (![1, ξ, 0, 0] : Fin 4 → K))
      (blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) • (![1, ξ, 0, 0] : Fin 4 → K)) = 0 := by
    rw [herm_smul_smul]; exact hz0
  have hvv : blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) • (![1, ξ, 0, 0] : Fin 4 → K) = ![1, c * ξ, s * ξ, 0] := by
    rw [blockEmb2_smul_one, su2Of_apply, hs, hc]
    funext j
    fin_cases j <;> simp
  have hv01 : unitaryInvolution K p f ((blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) • (![1, ξ, 0, 0] : Fin 4 → K)) 0) *
      (blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) • (![1, ξ, 0, 0] : Fin 4 → K)) 0 +
      unitaryInvolution K p f ((blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) • (![1, ξ, 0, 0] : Fin 4 → K)) 1) *
      (blockEmb2 K p f 3 1 (su2Of hinv c s hnorm) • (![1, ξ, 0, 0] : Fin 4 → K)) 1 ≠ 0 := by
    rw [hvv]
    show unitaryInvolution K p f 1 * 1 + unitaryInvolution K p f (c * ξ) * (c * ξ) ≠ 0
    rw [map_one, map_mul, hc]
    intro h
    apply hs0
    have : s * s = 0 := by linear_combination (-1 : K) * hcs - h + c * c * hξ
    exact mul_self_eq_zero.1 this
  have hT : ∀ (c' : K) (hc' : c' + unitaryInvolution K p f c' = 0), tv hinv hv hc' ∈ Γ₁ := fun c' hc' =>
    tv_conj_mem hinv Γ₁ hG hz0 hTz rfl hv c' hc'
  have hcore := core_link hK hq2 Γ₁ h0 h2 _ hv hv01 hT
  rw [eq_top_iff]
  intro g _
  obtain ⟨x', rfl⟩ := frameConj_surjective (fieldData hK) P hP' g
  have hx' : x' ∈ Γ₁ := by
    rw [hcore]
    trivial
  exact hx'


theorem eq_top_of_centralizers_q1_raw {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (x y : GL (Fin 4) K)
    (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) =
      -((y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K)))
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hyU : ((y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (y : Matrix (Fin 4) (Fin 4) K) = 1)
    (hX : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * x = x * g → g ∈ Γ)
    (hY : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * y = y * g → g ∈ Γ) : Γ = ⊤ := by
  obtain ⟨P, hP, hxP, hyP⟩ := GenLocU4Pair.exists_pair_frame hp hp2 hK x y hxU hyU hx2 hy2 hxy
  exact q1_in_frame hp hp2 hK hq Γ x y P hP hxP hyP hX hY

end GenLocU4Q1

end CFSG.GH74.Generic.BProg.B2
