module

public import CFSG.CGT.T75M23.N7Main
public import Certificates.Certificate271010

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.CGT.T75JM

theorem exists_mulEquiv_normalizer7_of_certificate
    {G : Type*} [Group G] {T : Subgroup G}
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hsq : ∀ a ∈ T, a ^ 2 = 1)
    (h16 : Nat.card T = 16) (hC : Subgroup.centralizer (T : Set G) = T)
    (φ : NQ T ≃* alternatingGroup (Fin 7)) :
    ∃ Ψ : PG 6 rels7 ≃* Subgroup.normalizer (T : Set G),
      Subgroup.map Ψ.toMonoidHom (Subgroup.closure (Set.range tGen7)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
  obtain ⟨h1, h2, h3⟩ := Certificates.certificate271010
  exact exists_mulEquiv_normalizer7 hcomm hsq h16 hC φ h1 h2 h3

end CFSG.CGT.T75M23
