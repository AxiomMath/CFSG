module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec8Gamma (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B : Subgroup G) (γ : G) (K U : Subgroup G) : Prop where
  ctx : Sec8Ctx G t L S z g B
  mem : γ ∈ S
  inv : orderOf γ = 2
  outer : InducesOutsideGStar L 6 (-1) γ
  gen : S = zpowers t ⊔ zpowers γ ⊔ (S ⊓ L)
  comp : IsComponentIn K (centralizer ({γ} : Set G))
  inFStar : InFStar K
  layer_le : layerCent L γ ≤ K
  normal : (K.subgroupOf (centralizer ({γ} : Set G))).Normal
  U_e16 : IsElemAb2 U 4
  U_le : U ≤ K
  t_norm : t ∈ normalizer (U : Set G)

@[expose] def Asc82Step84End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G)
    (γ : G) (K U : Subgroup G), Sec8Gamma G t L S z g B γ K U → False

end CFSG.OddStandard.SmallF3.Omega
