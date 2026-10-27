module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.CharThree
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint

noncomputable def centralizerEquivOfMulEquiv {G H : Type*} [Group G] [Group H] (ψ : G ≃* H)
    (d : G) :
    Subgroup.centralizer ({d} : Set G) ≃* Subgroup.centralizer ({ψ d} : Set H) :=
  (ψ.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ψ x * ψ d = ψ d * ψ x
      rw [← map_mul, ← map_mul]
      exact congrArg ψ hx
    · intro hy
      refine ⟨ψ.symm y, ?_, ψ.apply_symm_apply y⟩
      apply ψ.injective
      rw [map_mul, map_mul, ψ.apply_symm_apply]
      exact hy))

theorem census424_of_mcl
    {X : Type} [Group X] [Finite X] (φ : X ≃* NativeSporadic.Carrier .McL) : Census424 X := by
  have eM : NativeSporadic.Carrier .McL ≃* CFSG.Sporadic.Schreier.mclP :=
    CFSG.Sporadic.Schreier.mclPermEquiv
  set ψ : X ≃* CFSG.Sporadic.Schreier.mclP := φ.trans eM with hψ
  refine census424_of_charThree fun c hc => ?_
  have hψc : orderOf (ψ c) = 3 := by rw [MulEquiv.orderOf_eq]; exact hc
  exact RankThree.PartTwo.Sec14.isCharacteristicP_of_mulEquiv'
    (centralizerEquivOfMulEquiv ψ c).symm
    (RankThree.PartTwo.Sec6.ThreeLocalSporProof.centCharThree_mclP (ψ c) hψc)

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
