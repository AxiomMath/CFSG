module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21N08
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Z04
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Res

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson


@[expose] def C21_14_Y_conn_W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      u ∈ W → alphaOf (Subgroup.closure {u, z}) = ⊥ → dComp Ω K ≠ dstarComp Ω K →
        Q3T8.Asc77.SectionConnected Ω u →
          ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K ∨
            ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({t * z} : Set G)

theorem c21_14_Y_ne_W_of_conn_W (hC3 : Q3T8.Asc77.C21_3) (hZT : Q3T8.Asc77.C21_14_ZT)
    (hc : C21_14_Y_conn_W) : Q3T8.Asc77.C21_14_Y_ne_W := by
  intro G _ _ _ Ω K K' z u J t W h huW hα hne
  by_cases hconn : Q3T8.Asc77.SectionConnected Ω u
  · exact hc G Ω K K' z u J t W h huW hα hne hconn
  · exact ((c21_14_Y_disc_of_zt hC3 hZT) G Ω K K' z u J t W h hconn).2 hα

theorem c21_normCent_of_conn_W (hC3 : Q3T8.Asc77.C21_3) (hZT : Q3T8.Asc77.C21_14_ZT)
    (hc : C21_14_Y_conn_W) : Q3T8.Asc77.C21_NormCent :=
  c21_normCent_of_Y_ne hC3 (c21_14_Y_ne_W_of_conn_W hC3 hZT hc)

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8

namespace CFSG.ClassicalInvolution.Q3.Q3T7W21

open CFSG.ClassicalInvolution.Q3.Q3T7 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77


theorem c21_2Three_of_conn_W (hE : Q3T7E.ThmEWithSylow3) (hHt : TwinFrameHyp51t)
    (hHu : TwinFrameHyp51u) (hc : C21_14_Y_conn_W) : C21_2Three :=
  c21_2Three_of_residuals hE hHt hHu c21_14_zt_proved
    (c21_normCent_of_conn_W (c21_3_of (twinFrameHyp51_of_cases twinFrameHyp51z_proved hHt hHu))
      c21_14_zt_proved hc)

end CFSG.ClassicalInvolution.Q3.Q3T7W21
