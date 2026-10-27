module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.Descent
public import CFSG.HardMathSupport.Seitz.Proving.OrderThreeSLConj

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.HardMathSupport.Seitz.Proving

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem rootSL2_mem_adjointGroup (β : Fin Tag.G2.rank → ℤ) (A : SL2 K) :
    rootSL2 .G2 K β A ∈ adjointGroup .G2 K :=
  (exceptional_Lang_root_rank_one_data .G2 K β).2.2.2.2.1 A

theorem exists_rootSL2_of_order_three (β : Fin Tag.G2.rank → ℤ) {y : adjointGroup .G2 K}
    {A : SL2 K} (hA : (y : ModGL .G2 K) = rootSL2 .G2 K β A) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    A ^ 3 = 1 ∧ A ≠ 1 := by
  constructor
  · apply rootSL2_injective_of_field β
    rw [map_pow, map_one, ← hA]
    exact congrArg Subtype.val hy3
  · rintro rfl
    apply hy1
    apply Subtype.ext
    rw [hA, map_one]
    rfl

theorem QPlusModel.exists_conj_std (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (h3 : 3 ∣ Nat.card K + 1)
    {z e : adjointGroup .G2 K} (hz3 : z ^ 3 = 1) (he3 : e ^ 3 = 1) (hz1 : z ≠ 1) (he1 : e ≠ 1)
    (hzv : ∃ C : SL2 K₂, twistEmb (K := K) M.g z = rootSL2 .G2 K₂ g2v C)
    (hea : ∃ C : SL2 K₂, twistEmb (K := K) M.g e = rootSL2 .G2 K₂ g2a C) :
    ∃ x : adjointGroup .G2 K, x * z * x⁻¹ = zStd K ∧ x * e * x⁻¹ = eStd K := by
  obtain ⟨C, hC⟩ := hzv
  obtain ⟨C', hC'⟩ := hea
  obtain ⟨Az, hAz⟩ := exists_rootSL2_of_baseChange hdeg hσ (M.baseChange_eq_of_twist_v hC)
  obtain ⟨Ae, hAe⟩ := exists_rootSL2_of_baseChange hdeg hσ (M.baseChange_eq_of_twist_a hC')
  obtain ⟨hAz3, hAz1⟩ := exists_rootSL2_of_order_three g2v hAz hz3 hz1
  obtain ⟨hAe3, hAe1⟩ := exists_rootSL2_of_order_three g2a hAe he3 he1
  obtain ⟨Sz, hSz⟩ := exists_conj_eq_orderThreeSL h3 hAz3 hAz1
  obtain ⟨Se, hSe⟩ := exists_conj_eq_orderThreeSL h3 hAe3 hAe1
  refine ⟨⟨rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz,
    mul_mem (rootSL2_mem_adjointGroup _ _) (rootSL2_mem_adjointGroup _ _)⟩,
    Subtype.ext ?_, Subtype.ext ?_⟩
  · show rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz * (z : ModGL .G2 K) *
      (rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz)⁻¹ = rootSL2 .G2 K g2v (orderThreeSL K)
    have : rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz * rootSL2 .G2 K g2v Az *
        (rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz)⁻¹ =
        rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v (Sz * Az * Sz⁻¹) *
          (rootSL2 .G2 K g2a Se)⁻¹ := by
      simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]
    rw [hAz, this, hSz]
    exact rootSL2_a_conj_v K _ _
  · show rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz * (e : ModGL .G2 K) *
      (rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz)⁻¹ = rootSL2 .G2 K g2a (orderThreeSL K)
    have h1 : rootSL2 .G2 K g2v Sz * rootSL2 .G2 K g2a Ae * (rootSL2 .G2 K g2v Sz)⁻¹ =
        rootSL2 .G2 K g2a Ae := rootSL2_v_conj_a K _ _
    have : rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz * rootSL2 .G2 K g2a Ae *
        (rootSL2 .G2 K g2a Se * rootSL2 .G2 K g2v Sz)⁻¹ =
        rootSL2 .G2 K g2a Se * (rootSL2 .G2 K g2v Sz * rootSL2 .G2 K g2a Ae *
          (rootSL2 .G2 K g2v Sz)⁻¹) * (rootSL2 .G2 K g2a Se)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [hAe, this, h1]
    simp only [← map_inv, ← map_mul]
    rw [hSe]

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
