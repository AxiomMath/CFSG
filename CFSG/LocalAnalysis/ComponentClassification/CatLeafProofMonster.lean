module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.Monster.SteinbergBQInvolutionComponentsTwoPart

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup

private theorem map_centralizer_singleton {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (d : X) : (centralizer ({d} : Set X)).map φ.toMonoidHom = centralizer ({φ d} : Set Y) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg φ h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  · intro h
    apply φ.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h

private def centralizerMulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (d : X) :
    centralizer ({d} : Set X) ≃* centralizer ({φ d} : Set Y) :=
  (φ.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton φ d))

private theorem nonempty_mulEquiv_gmat
    {S : Type} [Group S] (hS : IsSimpleGroup S) (hM : Nonempty (S ≃* Blueprint.NativeSporadic.M)) :
    Nonempty (S ≃* CFSG.Monster.Generated.Gmat) := by
  obtain ⟨θ⟩ := hM
  exact RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple θ

theorem monsterInnerInput
    : CatLeaf.MonsterInnerInput := by
  intro S _ _ hS hM α
  obtain ⟨e⟩ := nonempty_mulEquiv_gmat hS hM
  obtain ⟨g, hg⟩ := BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_Gmat α
  exact MonoidHom.mem_range.mpr ⟨g, hg.symm⟩

theorem monsterLocalComponentsInput
    : CatLeaf.MonsterLocalComponentsInput := by
  intro S _ _ hS hM t ht B hB
  obtain ⟨e⟩ := nonempty_mulEquiv_gmat hS hM
  have h2 : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨m, hm, hcard⟩ := Monster.Existence.SteinbergBQ.two_part_of_mulEquiv
    (centralizerMulEquiv e t)
    (Monster.Existence.native_M_involution_local_components_two_part (e t) h2) B hB
  rw [hcard]
  refine ⟨dvd_mul_right _ _, fun h => ?_⟩
  rw [show 2 ^ 42 = 2 ^ 41 * 2 by norm_num] at h
  have h2m : 2 ∣ m := (Nat.mul_dvd_mul_iff_left (by positivity)).mp h
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2m)

end CFSG.ComponentClassification.CatLeafProof
