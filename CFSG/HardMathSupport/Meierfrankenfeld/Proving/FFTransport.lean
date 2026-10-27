module

public import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.FFTransport

variable {X : Type*} [Group X] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem isFFStarOffender_map_iff {ρ : Representation (ZMod 2) X W} (hρ : Function.Injective ρ)
    {A : Subgroup X} {Y : Subgroup (MulAut (Multiplicative W))}
    (hY : A.map (CFSG.Quasithin.FFModel.repMulAut ρ) ≤ Y) :
    CFSG.Quasithin.IsFFStarOffender Y (A.map (CFSG.Quasithin.FFModel.repMulAut ρ)) ↔
      A ≠ ⊥ ∧ CFSG.RankThree.FFModules.IsElemBestOffender ρ A :=
  CFSG.RankThree.FFModules.isFFStarOffender_map_iff hρ hY

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.FFTransport

end
