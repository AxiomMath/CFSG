module

public import CFSG.RankThree.PartOne.K159.KleinModel
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.ClassicalInvolution.PhanDn

open Matrix CFSG.RankThree.PartOne.K159 CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] [CharP K 2] {σ : K ≃+* K}

@[expose] def kleinWedge (u v : Fin 4 → K) : Fin 3 ⊕ Fin 3 → K :=
  Klein.coords (vecMulVec u v + vecMulVec v u)

theorem alt_kleinWedge (u v : Fin 4 → K) :
    Klein.alt (kleinWedge u v) = vecMulVec u v + vecMulVec v u := by
  rw [kleinWedge, Klein.alt_coords]
  · rw [Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec,
      add_comm]
  · intro i
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
    rw [mul_comm (v i) (u i), CharTwo.add_self_eq_zero]

@[simp] theorem kleinWedge_self (u : Fin 4 → K) : kleinWedge u u = 0 := by
  have h : vecMulVec u u + vecMulVec u u = 0 := CharTwo.add_self_eq_zero _
  rw [kleinWedge, h]
  exact map_zero Klein.coordsL

omit [CharP K 2] in
theorem kleinWedge_comm (u v : Fin 4 → K) : kleinWedge u v = kleinWedge v u := by
  rw [kleinWedge, kleinWedge, add_comm]

omit [CharP K 2] in
@[simp] theorem kleinWedge_add_left (u u' v : Fin 4 → K) :
    kleinWedge (u + u') v = kleinWedge u v + kleinWedge u' v := by
  funext s
  rcases s with i | i <;> fin_cases i <;>
    simp [kleinWedge, Klein.coords, Matrix.add_apply, Matrix.vecMulVec_apply] <;> ring

omit [CharP K 2] in
@[simp] theorem kleinWedge_add_right (u v v' : Fin 4 → K) :
    kleinWedge u (v + v') = kleinWedge u v + kleinWedge u v' := by
  rw [kleinWedge_comm, kleinWedge_add_left, kleinWedge_comm u v, kleinWedge_comm u v']

omit [CharP K 2] in
@[simp] theorem kleinWedge_smul_left (c : K) (u v : Fin 4 → K) :
    kleinWedge (c • u) v = c • kleinWedge u v := by
  funext s
  rcases s with i | i <;> fin_cases i <;>
    simp [kleinWedge, Klein.coords, Matrix.vecMulVec_apply, smul_eq_mul] <;> ring

omit [CharP K 2] in
@[simp] theorem kleinWedge_smul_right (c : K) (u v : Fin 4 → K) :
    kleinWedge u (c • v) = c • kleinWedge u v := by
  rw [kleinWedge_comm, kleinWedge_smul_left, kleinWedge_comm v u]

theorem quadPlus_kleinWedge (u v : Fin 4 → K) : quadPlus 3 K (kleinWedge u v) = 0 := by
  rw [Klein.quadPlus_eq_pfS_alt, alt_kleinWedge]
  simp only [CFSG.LocalAnalysis.pfS, Matrix.add_apply, Matrix.vecMulVec_apply]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem polar_kleinWedge_left (u v w : Fin 4 → K) :
    QuadraticMap.polar (quadPlus 3 K) (kleinWedge u v) (kleinWedge u w) = 0 := by
  have h := QuadraticMap.map_add (quadPlus 3 K) (kleinWedge u v) (kleinWedge u w)
  rw [← kleinWedge_add_right, quadPlus_kleinWedge, quadPlus_kleinWedge,
    quadPlus_kleinWedge] at h
  simpa using h.symm

theorem flipHerm_kleinWedge (u v x y : Fin 4 → K) :
    flipHerm σ (kleinWedge u v) (kleinWedge x y) =
      herm σ x u * herm σ y v + herm σ y u * herm σ x v := by
  simp only [flipHerm, polar_quadPlus, herm, kleinWedge, Klein.coords, dFlip_apply_inl,
    dFlip_apply_inr, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.add_apply,
    Matrix.vecMulVec_apply, map_add, map_mul, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring_nf
  simp [CharTwo.two_eq_zero]
  ring

theorem kleinWedge_mulVec (g : Matrix (Fin 4) (Fin 4) K) (u v : Fin 4 → K) :
    kleinWedge (g *ᵥ u) (g *ᵥ v) = Klein.cong g (kleinWedge u v) := by
  rw [Klein.cong_apply, alt_kleinWedge]
  simp only [kleinWedge]
  have h : vecMulVec (g *ᵥ u) (g *ᵥ v) + vecMulVec (g *ᵥ v) (g *ᵥ u) =
      g * (vecMulVec u v + vecMulVec v u) * gᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
      Matrix.vecMul_transpose, add_comm]
  rw [h]

omit [CharP K 2] in
theorem kleinWedge_single_zero (j : Fin 3) :
    kleinWedge (Pi.single 0 1) (Pi.single j.succ 1) = stdE (K := K) j := by
  ext s
  rcases s with i | i <;> fin_cases i <;> fin_cases j <;>
    simp [kleinWedge, Klein.coords, Matrix.add_apply, Matrix.vecMulVec_apply, stdE]

omit [CharP K 2] in
theorem stdF_eq_kleinWedge :
    stdF (K := K) 0 = kleinWedge (Pi.single 2 1) (Pi.single 3 1) ∧
      stdF (K := K) 1 = kleinWedge (Pi.single 1 1) (Pi.single 3 1) ∧
      stdF (K := K) 2 = kleinWedge (Pi.single 1 1) (Pi.single 2 1) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext s <;> rcases s with i | i <;> fin_cases i <;>
      simp [kleinWedge, Klein.coords, Matrix.add_apply, Matrix.vecMulVec_apply, stdF]

theorem alt_dFlip (w : Fin 3 ⊕ Fin 3 → K) :
    Klein.alt (dFlip σ w) = (CFSG.LocalAnalysis.sharp (Klein.alt w)).map σ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Klein.alt, dFlip, CFSG.LocalAnalysis.sharp, CFSG.LocalAnalysis.altMat,
      CFSG.LocalAnalysis.antiMat, CharTwo.neg_eq]

theorem dFlip_cong (g : GL (Fin 4) K) (w : Fin 3 ⊕ Fin 3 → K) :
    dFlip σ (Klein.cong (g : Matrix (Fin 4) (Fin 4) K) w) =
      σ ((g : Matrix (Fin 4) (Fin 4) K).det) •
        Klein.cong ((((g : Matrix (Fin 4) (Fin 4) K).map σ)⁻¹)ᵀ) (dFlip σ w) := by
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K)
  set X : Matrix (Fin 4) (Fin 4) K := Klein.alt w
  have hX : CFSG.LocalAnalysis.IsAltMat X := by
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X, Klein.alt, CFSG.LocalAnalysis.antiMat, CharTwo.neg_eq]
    · intro i
      fin_cases i <;> simp [X, Klein.alt, CFSG.LocalAnalysis.antiMat]
  have hG : CFSG.LocalAnalysis.sharp (G * X * Gᵀ) =
      G.det • ((↑(g⁻¹) : Matrix (Fin 4) (Fin 4) K)ᵀ * CFSG.LocalAnalysis.sharp X *
        (↑(g⁻¹) : Matrix (Fin 4) (Fin 4) K)) :=
    ((CFSG.LocalAnalysis.char_two_alternating_four_Pfaffian_identities (F := K)).2.2.2.2
      g X hX).2.2
  have hGunit : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp ⟨g, rfl⟩
  have hmap_inv : (G⁻¹).map σ = (G.map σ)⁻¹ := by
    have h1 : (G⁻¹).map σ * (G.map σ) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul G hGunit]
      exact Matrix.map_one σ (map_zero σ) (map_one σ)
    exact (Matrix.inv_eq_left_inv h1).symm
  have hinj : Function.Injective (Klein.alt : (Fin 3 ⊕ Fin 3 → K) →
      Matrix (Fin 4) (Fin 4) K) := by
    intro a b h
    rw [← Klein.coords_alt a, ← Klein.coords_alt b, h]
  refine hinj ?_
  rw [alt_dFlip, Klein.alt_cong G w]
  change (CFSG.LocalAnalysis.sharp (G * X * Gᵀ)).map σ =
    Klein.alt (σ G.det • Klein.cong ((((G.map σ)⁻¹)ᵀ)) (dFlip σ w))
  rw [hG, Klein.alt_smul,
    Klein.alt_cong ((((G.map σ)⁻¹)ᵀ)) (dFlip σ w), alt_dFlip]
  rw [Matrix.map_smul' σ G.det _
    (fun a b => map_mul σ a b)]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hGi : (↑(g⁻¹) : Matrix (Fin 4) (Fin 4) K) = G⁻¹ := by
    rw [Matrix.GeneralLinearGroup.coe_inv]
  rw [hGi, hmap_inv, Matrix.transpose_transpose]

theorem dFlip_cong_of_unitary {g : Matrix (Fin 4) (Fin 4) K}
    (hg : conjTr σ g * g = 1) (w : Fin 3 ⊕ Fin 3 → K) :
    dFlip σ (Klein.cong g w) = σ g.det • Klein.cong g (dFlip σ w) := by
  have hdet : g.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hg
  let gu : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero g hdet
  have hgu : (gu : Matrix (Fin 4) (Fin 4) K) = g := rfl
  have hunit : ((g.map σ)⁻¹)ᵀ = g := by
    have hleft : gᵀ * (g.map σ) = 1 := by
      have h := congrArg Matrix.transpose hg
      simpa [conjTr, Matrix.transpose_mul] using h
    have hinv : (g.map σ)⁻¹ = gᵀ := Matrix.inv_eq_left_inv hleft
    rw [hinv, Matrix.transpose_transpose]
  have h := dFlip_cong (σ := σ) gu w
  rw [hgu] at h
  rw [h, hunit]

@[expose] def contract (φ : Fin 4 → K) (X : Fin 3 ⊕ Fin 3 → K) : Fin 4 → K :=
  vecMul φ (Klein.alt X)

theorem contract_kleinWedge (φ u v : Fin 4 → K) :
    contract φ (kleinWedge u v) = (φ ⬝ᵥ u) • v + (φ ⬝ᵥ v) • u := by
  ext j
  rw [contract, alt_kleinWedge, Matrix.vecMul_apply_eq_sum]
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, dotProduct, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  have h1 : (∑ x, φ x * (u x * v j)) = ∑ i, φ i * u i * v j := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ x, φ x * (v x * u j)) = ∑ i, φ i * v i * u j := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1, h2]

end CFSG.ClassicalInvolution.PhanDn

end
