module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFStd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddLev

public section

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

theorem fh_simFamO_neg_one_one : FHSimFamO (-1) 1 := by
  intro a hsim ha2 β hodd hβ
  have hK : Nat.card 𝔽₃ = 3 :=
    CFSG.ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have haa : a * a = 1 := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, ha2, one_smul]
    rfl
  obtain ⟨θ, hθO, hθ⟩ := exists_standardizing_n h2 (nondegenerate_polarBilin_quadPlus 4 𝔽₃) haa
    (fun v => by rw [hsim, neg_one_mul])
  refine fh_smul_of_conj hodd hβ hθO ?_ (Levi.embSL_mul_a₀ _) (Levi.embSL_mul_a₀ _)
  calc a = a * θ * θ⁻¹ := by group
    _ = θ * Levi.a₀ 𝔽₃ 4 * θ⁻¹ := by rw [hθ]

end CFSG.OddStandard.SmallF3.Omega
