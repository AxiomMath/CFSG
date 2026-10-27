module

public import CFSG.CGT.T75M23.M23Pres
public import CFSG.Sporadic.Mathieu.M23
public import Certificates.Certificate271015

public section

namespace CFSG.CGT.T75M23

open CFSG.Blueprint

theorem m23Facts_holds : M23Facts :=
  Certificates.certificate271015

theorem card_native_m23 :
    Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem exists_mulEquiv_m23_of_relations_of_certificate
    {G : Type*} [Group G] (e : Fin 7 → G)
    (hp : ∀ r ∈ m23Rels, FreeGroup.lift e (FreeGroup.mk r) = 1)
    (hK : Subgroup.closure (Set.range e) ≠ ⊥) :
    Nonempty (Subgroup.closure (Set.range e) ≃* NativeSporadic.M23) :=
  exists_mulEquiv_m23_of_relations card_native_m23
    (CFSG.Sporadic.Mathieu.fam_m23_simplicity).2.2 e m23Facts_holds hp hK

end CFSG.CGT.T75M23
