module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.Permutation.FiveTransitive.CyclicTwoAutomorphismKernel

public noncomputable section

namespace CFSG.GorensteinWalter

universe u

theorem dihedral_subgroup_automorphism_isTwoGroup
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (U : Subgroup G) (hUS : U ≤ (S : Subgroup G))
    (hU : ¬ IsKleinFour U) : IsPGroup 2 (MulAut U) := by
  let U' : Subgroup (DihedralGroup (2 ^ m)) :=
    (U.subgroupOf (S : Subgroup G)).map e.toMonoidHom
  let eU : U ≃* U' :=
    (Subgroup.subgroupOfEquivOfLe hUS).symm.trans
      ((U.subgroupOf (S : Subgroup G)).equivMapOfInjective
        e.toMonoidHom e.injective)
  rcases subgroups_dihedral_twoGroup_cyclic_or_dihedral hm U' with
    hcyclic | ⟨k, hk, ⟨f⟩⟩
  · let : IsCyclic U := eU.isCyclic.mpr hcyclic
    exact FiveTransitive.CyclicTwoAutomorphismKernel.automorphism_two_group
      (IsPGroup.to_le S.isPGroup' hUS)
  · have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      subst k
      let f' : U ≃* DihedralGroup 2 := eU.trans f
      apply hU
      refine ⟨?_, ?_⟩
      · exact (Nat.card_congr f'.toEquiv).trans
          (IsKleinFour.card_four (G := DihedralGroup 2))
      · exact (Monoid.exponent_eq_of_mulEquiv f').trans
          (IsKleinFour.exponent_two (G := DihedralGroup 2))
    exact (dihedral_mulAut_is_twoGroup hk2).of_equiv
      (MulAut.congr (eU.trans f)).symm

end CFSG.GorensteinWalter
