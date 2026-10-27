module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Quasithin.H13.A7Nat1233FourInputs

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup

@[expose] def Insp1233KLin_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V),
    Setting1233Four hyp → ∀ z : G, z ∈ V → z ≠ 1 → z ∈ quasithinOmegaOneCenter T →
      HypC28 (hyp.Gv z) hyp.Q (hyp.Mv z) (Kv hyp z) V →
      ∀ K : Subgroup G, K ∈ cComp (hyp.Gv z) → Kv hyp z < K → T ≤ normalizer (K : Set G) →
        ¬ K ≤ hyp.Mv z → V ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ T)), K⁆ →
        pCoreOf 2 (Kv hyp z ⊔ T) ≤ centralizer (V : Set G) →
        C41Case4 (hyp.Gv z) hyp.Q (hyp.Mv z) (Kv hyp z) V K → False

end CFSG.Quasithin.H13.A7
