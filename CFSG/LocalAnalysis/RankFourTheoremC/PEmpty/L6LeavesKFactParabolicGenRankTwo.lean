module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenCore
public import CFSG.Quasithin.Background.SmithC27RLieBasic
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNGen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.GH74.BNPair CFSG.QuasithinUnique CFSG.Quasithin.SmithC27

theorem hasParGen_of_rankTwoSystem {X : Type} [Group X] [Finite X] {n : ℕ}
    (R : RankTwoSystem X n) (hU : IsSylowTwoOf R.U ⊤) : HasParGen X := by
  obtain ⟨W, hW⟩ := exists_sylow_two_coe_eq hU
  have F : ParFam X Bool :=
    { W := W
      P := fun i => CFSG.Quasithin.H13.F431.BN.P R i
      Q := fun i => CFSG.Quasithin.H13.F431.BN.Uplus R i
      nonempty := ⟨true⟩
      normalizer_le := fun i => by
        rw [hW, CFSG.Quasithin.H13.F431.BN.normalizer_U_eq_B]
        exact CFSG.Quasithin.H13.F431.BN.B_le_P R i
      gen := by
        rw [iSup_bool_eq]
        exact CFSG.Quasithin.H13.F431.BN.P₁_sup_P₂ R
      isPGroup := fun i => hU.2.1.to_le (CFSG.Quasithin.H13.F431.BN.Uplus_le_U R i)
      le := fun i => CFSG.Quasithin.H13.F431.BN.Uplus_le_P R i
      normalizes := fun i => CFSG.Quasithin.H13.F431.BN.P_le_normalizer_Uplus R i
      ne_bot := fun i => CFSG.Quasithin.H13.F431.BN.Uplus_ne_bot R i }
  exact F.hasParGen

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
