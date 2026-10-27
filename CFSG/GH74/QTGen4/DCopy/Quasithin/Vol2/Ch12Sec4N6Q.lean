module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4N6MS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise commutatorElement

@[expose] def BlockQ1246SL27_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ E : Subgroup G, E ≤ V → Nat.card E = 4 → T ≤ Subgroup.normalizer (E : Set G) →
    ¬ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G) →
    ⁅pCoreOf 2 (L ⊔ T), L⁆ = V → pCoreOf 2 L ≠ V →
      pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G))

namespace N1246

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem Q_eq_F4 (hSL : BlockQ1246SL27_F4) (hMS : C134L32Corr_F4)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
  have hcomm := c.commutator_Q_eq_F4 hMS hN
  by_cases hO2 : pCoreOf 2 L = V
  · exact c.Q_eq_of_pCore hcomm hO2
  · exact hSL G T L V c.cx c.q3 E c.EV c.E4 c.TE hN hcomm hO2

end Ctx

end N1246

end CFSG.Quasithin.H13
