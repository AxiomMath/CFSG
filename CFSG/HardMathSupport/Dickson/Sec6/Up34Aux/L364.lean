module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.L364Ord
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.L364Core
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Narrow

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
  CFSG.RankThree.PartTwo.KFacts

theorem up34L364NotInnDiag_holds : Up34L364NotInnDiag := by
  intro Q _ _ hq hcat β hpump hinn
  obtain ⟨K₀, _, _, h64, ⟨e₀⟩⟩ := exists_model_of_catalogL364 hcat
  rcases hinn with ⟨K, _, _, θ, φ, hconj, hθφ⟩ | ⟨K, _, _, q, θ, φ, hKq, hconj, hθφ⟩
  · have hK64 : Nat.card K = 64 :=
      Up34Ord.card_eq_sixtyFour_of_equiv h64 (θ.symm.trans e₀)
    have hK : Nat.card K % 3 = 1 := by rw [hK64]
    let π : Q →* StatedProj (StatedSL 3 K) :=
      θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
    have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker ≤ Subgroup.center Q := by
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      have h1 : (QuotientGroup.mk' (Subgroup.center Q)) y = 1 :=
        θ.injective (by rw [map_one]; exact hy)
      exact (QuotientGroup.eq_one_iff y).1 h1
    have hαψ : ∀ y, π (β y) = φ (π y) := hθφ
    obtain ⟨hβ3, hβ1, J, hJ, hJ34⟩ := hpump
    obtain ⟨A, hA, hA34⟩ := isLThreeFour_barOf_of_central π hπ hker β φ hαψ hJ hJ34
    have hφ3 : φ ^ 3 = 1 := by
      refine MulEquiv.ext fun p => ?_
      obtain ⟨y, rfl⟩ := hπ p
      rw [← Up34L364.pow_apply_intertwine π β φ hαψ 3 y, hβ3, MulAut.one_apply,
        MulAut.one_apply]
    have hφ1 : φ ≠ 1 := by
      intro h1
      apply hβ1
      apply eq_one_of_centerDescend_eq_one hq
      refine MulEquiv.ext fun s => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      rw [centerDescend_mk, MulAut.one_apply]
      apply θ.injective
      have h2 := hθφ y
      rw [h1, MulAut.one_apply] at h2
      exact h2
    exact Up34L364.l364_core hK φ hconj hφ3 hφ1 hA hA34
  · exact Up34Ord.card_psu3_ne h64 hKq (Nat.card_congr (θ.symm.trans e₀).toEquiv)

end CFSG.HardMathSupport.Dickson.Sec6
