module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.GH74.KGroups.U33

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1

theorem tabIdentFor_u33
    : TabIdentFor @Ident.FamU33 := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨-, hmodel⟩ := hX
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (K := ↥X) (Or.inl ⟨by decide, hmodel⟩)
  have hα2 : (hs.conjAut : MulAut ↥X) ^ 2 = 1 := by
    rw [pow_two]
    apply MulEquiv.ext
    intro y
    exact hs.conjAut_conjAut y
  have hα1 : (hs.conjAut : MulAut ↥X) ≠ 1 := by
    intro h
    refine hs.false_of_comm_central fun y => ?_
    have hy : hs.conjAut y = y := congrArg (fun f : MulAut ↥X => f y) h
    rw [hy, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hsolv : Group.IsSolvable ↥(K.subgroupOf X) :=
    CFSG.GH74.KGroups.U33.fixed_solvable e hs.conjAut hα2 hα1 (K.subgroupOf X) fun x hx =>
      hs.conjAut_of_mem_K hx
  have hsolvK : Group.IsSolvable ↥K := by
    have eK := Subgroup.subgroupOfEquivOfLe hs.K_le
    exact Group.isSolvable_of_isSolvable_injective (f := eK.symm.toMonoidHom) eK.symm.injective
  obtain ⟨hsimple, a, b, hab⟩ := isKType_simple hs.ktype
  have := hsimple
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolvK a b)

end CFSG.QuasithinUnique.Id2519
