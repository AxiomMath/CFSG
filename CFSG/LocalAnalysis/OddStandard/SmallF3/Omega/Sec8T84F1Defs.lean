module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Sec8T84OuterSwaps : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L → ∀ s : G,
    s ∈ normalizer (L : Set G) → InducesOutsideGStar L 6 (-1) s →
      ∀ U : Subgroup G, U ≤ L → IsElemAb2 U 4 → s ∉ normalizer (U : Set G)

structure Sec8T84PMod (G : Type) [Group G] [Finite G] (V P F : Subgroup G) : Prop where
  card : Nat.card P = 2 ^ 7
  V_le : V ≤ P
  F_le : F ≤ P
  V_e16 : IsElemAb2 V 4
  F_e16 : IsElemAb2 F 4
  F_ne : F ≠ V
  V_norm : (V.subgroupOf P).Normal
  F_norm : (F.subgroupOf P).Normal
  only : ∀ F' : Subgroup G, F' ≤ P → IsElemAb2 F' 4 → F' = V ∨ F' = F
  no32 : ∀ F' : Subgroup G, F' ≤ P → ¬ IsElemAb2 F' 5
  J_card : Nat.card ↥(V ⊔ F) = 64
  EF_card : Nat.card ↥(V ⊓ F) = 4
  cent_V : P ⊓ centralizer (V : Set G) = V
  cent_F : P ⊓ centralizer (F : Set G) = F
  gen : ∃ s ∈ P, s ∉ V ⊔ F ∧ orderOf s = 2 ∧ P = zpowers s ⊔ (V ⊔ F)

structure Sec8T84TData (G : Type) [Group G] [Finite G] (t : G)
    (E T T1 T2 V1 V2 F1 F2 : Subgroup G) : Prop where
  t_sq : t * t = 1
  T_eq : T = zpowers t ⊔ (T1 ⊔ T2)
  t_not : t ∉ T1 ⊔ T2
  comm : ∀ a ∈ T1, ∀ b ∈ T2, a * b = b * a
  inf : T1 ⊓ T2 = ⊥
  swap1 : ∀ a ∈ T1, t * a * t⁻¹ ∈ T2
  swap2 : ∀ a ∈ T2, t * a * t⁻¹ ∈ T1
  E_eq : E = V1 ⊔ V2
  V2_eq : V2 = V1.map (MulAut.conj t).toMonoidHom
  F2_eq : F2 = F1.map (MulAut.conj t).toMonoidHom
  mod1 : Sec8T84PMod G V1 T1 F1
  rank8 : ∀ s ∈ T1 ⊔ T2, s * s = 1 → s ≠ 1 →
    ∃ R : Subgroup G, R ≤ centralizer ({s} : Set G) ∧ IsElemAb2 R 8

end CFSG.OddStandard.SmallF3.Omega
