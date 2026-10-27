module

public import CFSG.GH74.Generic.Front.SpNFToH

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup

private abbrev spMat {F : Type} [Field F] (g : ↥(StatedSp 2 F)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

private theorem spMat_mul {F : Type} [Field F] (g h : ↥(StatedSp 2 F)) :
    spMat (g * h) = spMat g * spMat h := rfl

private theorem spMat_inj {F : Type} [Field F] {g h : ↥(StatedSp 2 F)} (hgh : spMat g = spMat h) :
    g = h := Subtype.ext (Units.ext hgh)

private theorem spMat_one {F : Type} [Field F] : spMat (1 : ↥(StatedSp 2 F)) = 1 := rfl

theorem nb_fusion_sp {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (e : K ≃* ↥(StatedSp 2 F)) {w t : K}
    (hw : w ∈ center K) (hw1 : w ≠ 1) (_hw2 : w * w = 1) (ht : t * t = 1) (h1 : t ≠ 1)
    (htw : t ≠ w) : ∃ g : K, g * t * g⁻¹ = w * t := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hF
  have hcZ : e w ∈ Subgroup.center ↥(StatedSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := Subgroup.mem_center_iff.1 hw (e.symm g)
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact hg
  have hc1 : e w ≠ 1 := fun h => hw1 (e.injective (h.trans (map_one e).symm))
  have hcm : spMat (e w) = -1 := by
    rcases center_statedSp2_eq (e w) hcZ with h | h
    · exact absurd (spMat_inj (h.trans spMat_one.symm)) hc1
    · exact h
  have haa : e t * e t = 1 := by rw [← map_mul, ht, map_one]
  have ha1 : e t ≠ 1 := fun h => h1 (e.injective (h.trans (map_one e).symm))
  have hac : e t ≠ e w := fun h => htw (e.injective h)
  have hB : spMat (e w * e t) = -spMat (e t) := by
    rw [spMat_mul, hcm, neg_mul, one_mul]
  have hAA : spMat (e t) * spMat (e t) = 1 := by
    rw [← spMat_mul, haa]; rfl
  have hA1 : spMat (e t) ≠ 1 := fun h => ha1 (spMat_inj (h.trans spMat_one.symm))
  have hAm1 : spMat (e t) ≠ -1 := fun h => hac (spMat_inj (h.trans hcm.symm))
  have hBB : spMat (e w * e t) * spMat (e w * e t) = 1 := by rw [hB, neg_mul_neg, hAA]
  have hB1 : spMat (e w * e t) ≠ 1 := by
    intro h
    apply hAm1
    rw [hB] at h
    exact neg_eq_iff_eq_neg.1 h
  have hBm1 : spMat (e w * e t) ≠ -1 := by
    intro h
    apply hA1
    rw [hB] at h
    exact neg_inj.1 h
  obtain ⟨g₁, hg₁⟩ := exists_symplectic_conj h2 (spMat (e t)) hAA (statedSp_gram (e t)) hA1 hAm1
  obtain ⟨g₂, hg₂⟩ := exists_symplectic_conj h2 (spMat (e w * e t)) hBB
    (statedSp_gram (e w * e t)) hB1 hBm1
  refine ⟨e.symm (g₂ * g₁⁻¹), ?_⟩
  apply e.injective
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  apply spMat_inj
  have hg₁i : spMat g₁⁻¹ * spMat g₁ = 1 := by rw [← spMat_mul, inv_mul_cancel]; rfl
  have hg₂i : spMat g₂ * spMat g₂⁻¹ = 1 := by rw [← spMat_mul, mul_inv_cancel]; rfl
  rw [mul_inv_rev, inv_inv]
  simp only [spMat_mul]
  calc spMat g₂ * spMat g₁⁻¹ * spMat (e t) * (spMat g₁ * spMat g₂⁻¹)
      = spMat g₂ * (spMat g₁⁻¹ * (spMat (e t) * spMat g₁)) * spMat g₂⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = spMat g₂ * (spMat g₁⁻¹ * (spMat g₁ * Matrix.diagonal (Sum.elim ![(-1 : F), 1] ![(-1 : F), 1])))
          * spMat g₂⁻¹ := by rw [hg₁]
    _ = spMat g₂ * Matrix.diagonal (Sum.elim ![(-1 : F), 1] ![(-1 : F), 1]) * spMat g₂⁻¹ := by
        rw [← Matrix.mul_assoc (spMat g₁⁻¹), hg₁i, Matrix.one_mul]
    _ = spMat (e w) * spMat (e t) * spMat g₂ * spMat g₂⁻¹ := by rw [← spMat_mul, ← hg₂]
    _ = spMat (e w) * spMat (e t) := by rw [Matrix.mul_assoc, hg₂i, Matrix.mul_one]

end CFSG.GH74.Generic.S1.Exo
