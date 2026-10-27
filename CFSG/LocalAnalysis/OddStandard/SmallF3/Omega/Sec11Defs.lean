module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec11Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
    (K1 K2 T R : Subgroup G) : Prop extends Sec10Ctx G t L S z K1 K2 where
  hyp : Hyp111 t S L
  sylowT : IsSylow2Of T (secM t S L)
  S_le : S ≤ T
  sylowR : IsSylow2Of R (normalizer (secQ K1 K2 : Set G))
  T_le : T ≤ R

@[expose] def secCTQ (K1 K2 T : Subgroup G) : Subgroup G :=
  centralizer (secQ K1 K2 : Set G) ⊓ T

@[expose] def secD (K1 K2 R : Subgroup G) : Subgroup G :=
  centralizer (secQ K1 K2 : Set G) ⊓ R

@[expose] def secKD (D : Subgroup G) : Subgroup G :=
  oTwoRes (centralizer (D : Set G))

@[expose] def secKiD (t z : G) (Ki D : Subgroup G) : Subgroup G :=
  (Ki ⊔ oddCoreIn (secK0 t z)) ⊓ centralizer (D : Set G)

structure Sec11Ax (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
    (K1 K2 T R : Subgroup G) (a x : G) : Prop extends Sec11Ctx G t L S z K1 K2 T R where
  a_mem : a ∈ secA t S L
  a_not_Q : a ∉ secQ K1 K2
  swap : CFSG.conjugate K1 a = K2
  x_mem : x ∈ T
  x_inv : orderOf x = 2
  x_out1 : IsOuterOn x (K1 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))
  x_out2 : IsOuterOn x (K2 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))
  a_comm : ∀ c ∈ secCTQ K1 K2 T, a * c = c * a
  x_comm : secCTQ K1 K2 T ≠ zpowers t ⊔ zpowers z → ∀ c ∈ secCTQ K1 K2 T, x * c = c * x
  gen : T = Subgroup.closure
    ((secCTQ K1 K2 T : Set G) ∪ (secQ K1 K2 : Set G) ∪ ({a, x} : Set G))

end CFSG.OddStandard.SmallF3.Omega
