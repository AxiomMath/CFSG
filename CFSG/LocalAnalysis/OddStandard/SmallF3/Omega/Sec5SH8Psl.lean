module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)

theorem sec5sh8_psl {X : Type} [Group X] (P : Sylow 2 X) {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : X ≃* PSL2 F) :
    Sec5SH8Linear P F ⊤ := by
  refine ⟨hF, h5, ?_, ⟨Subgroup.topEquiv.trans e⟩, ?_, Or.inl rfl, ?_⟩
  · infer_instance
  · rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_center_eq_bot F)
  · intro z _ _ _
    exact Subgroup.mem_top z

end CFSG.OddStandard.SmallF3.Omega
