module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6D8
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem isPGroup_mulAut_of_card_eight {N : Type*} [Group N]
    (e : N ≃* alternatingGroup (Fin 6)) {P : Subgroup N} (hP : Nat.card P = 8) :
    IsPGroup 2 (MulAut ↥P) := by
  have hcard : Nat.card (P.map e.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hP
  obtain ⟨f⟩ := CFSG.QuasithinUnique.DoubleA3.nonempty_dihedral_of_card_eight
    (P.map e.toMonoidHom) hcard
  let g : ↥P ≃* DihedralGroup 4 := (P.equivMapOfInjective e.toMonoidHom e.injective).trans f
  have h2 : IsPGroup 2 (MulAut (DihedralGroup (2 ^ 2))) :=
    CFSG.GorensteinWalter.dihedral_mulAut_is_twoGroup (by norm_num)
  exact h2.of_equiv (MulAut.congr g).symm

end CFSG.EvenSporadicStandard.Fin76b
