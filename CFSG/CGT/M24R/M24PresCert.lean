module

public import CFSG.CGT.M24R.M24Pres
public import CFSG.CGT.M24R.Interfaces
public import Certificates.Certificate21190
public import Certificates.Certificate21191

public section

namespace CFSG.CGT.M24R

open CFSG.Blueprint CFSG.CosetTable

theorem m24Enum_eq_true :
    n8Sub.FiniteIndex ∧ n8Sub.index ≤ 759 :=
  Certificates.certificate21190

theorem m24TabCheck_eq_true : m24TabCheck = true :=
  Certificates.certificate21191

theorem exists_mulEquiv_m24_of_relations_of_certificate
    (hN8 : N8Bound) {G : Type*}
    [Group G] (e : Fin 11 → G) (hp : ∀ r ∈ m24Rels, FreeGroup.lift e (FreeGroup.mk r) = 1)
    (hK : Subgroup.closure (Set.range e) ≠ ⊥) :
    Nonempty (Subgroup.closure (Set.range e) ≃* NativeSporadic.M24) :=
  exists_mulEquiv_m24_of_relations m24Enum_eq_true m24TabCheck_eq_true hN8 e hp hK

theorem r24Statement_of_certificate
    (hN8 : N8Bound) :
    R24Statement :=
  fun _ _ e hp hK => exists_mulEquiv_m24_of_relations_of_certificate hN8 e hp hK

theorem r24Statement_of_card_le
    (h : Finite (PG 10 relsN8Ten) ∧ Nat.card (PG 10 relsN8Ten) ≤ 322560) : R24Statement :=
  have := h.1
  r24Statement_of_certificate (n8Bound_of_relsN8Ten h.2)

end CFSG.CGT.M24R
