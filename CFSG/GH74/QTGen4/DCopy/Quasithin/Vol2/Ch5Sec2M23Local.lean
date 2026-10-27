module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Local

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Stmt5_2_15_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (M2 : Subgroup G)
    (π : ↥M2 →* Equiv.Perm (Fin 7)), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfTypeM23 M L H B D T → IsM23Setting T H M2 π →
      ∀ X : Subgroup G, CFSG.Quasithin.IsSylowIn 3 X (M ⊓ centralizerModO2 L) →
        Subgroup.normalizer (X : Set G) ≤ M ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
          Nonempty (↥(M ⊓ Subgroup.normalizer (X : Set G)) ≃* ↥(GammaL2 K))

end CFSG.Quasithin.H13
