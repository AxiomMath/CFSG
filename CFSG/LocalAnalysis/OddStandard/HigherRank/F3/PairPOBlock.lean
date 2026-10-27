module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPODefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBPlus

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open

theorem pomegaBlock_statedOmega_quadPlus_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) : POmegaBlock ↥(StatedOmega (StatedQuadPlus 4 K)) := by
  have := Fintype.ofFinite K
  refine ⟨LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus (by omega), ?_, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    obtain ⟨c, hc⟩ : ∃ c : Kˣ,
        Matrix.GeneralLinearGroup.scalar (Fin 4 ⊕ Fin 4) c = g.1.1 := by
      have hg := (Subgroup.ext_iff.mp
        (LieType.Universal.Spin.center_statedOmega_quadPlus (K := K) (n := 4) (by omega))
        g.1).mp g.2
      exact MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hg)
    have hc2 : c * c = 1 := by
      apply Units.ext
      have h := FiniteField.pow_card_sub_one_eq_one (c : K) c.ne_zero
      rw [← Nat.card_eq_fintype_card, hK] at h
      simpa [pow_two] using h
    apply Subtype.ext
    apply Subtype.ext
    rw [pow_one, pow_two]
    show g.1.1 * g.1.1 = 1
    rw [← hc, ← map_mul, hc2, map_one]
  · exact ⟨4, Or.inl rfl, Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, le_rfl⟩, K, inferInstance,
      inferInstance, by rw [pow_one]; exact hK, ⟨QuotientGroup.quotientMulEquivOfEq
        (LieType.Universal.Spin.center_statedOmega_quadPlus (by omega))⟩⟩⟩

theorem neg_one_mem_statedOmega_quadPlus_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) : (-1 : GL (Fin 4 ⊕ Fin 4) K) ∈ StatedOmega (StatedQuadPlus 4 K) := by
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  exact (ComponentClassification.HarrisLit.T1.P54.DB.neg_one_mem_statedOmega_quadPlus_iff h2
    (by omega)).mpr ⟨1, by norm_num⟩

end CFSG.OddStandard.HigherRank.F3
