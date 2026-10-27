module

public import CFSG.CGT.T75JM.N6Main
public import Certificates.Certificate14984

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable

theorem exists_mulEquiv_normalizer_of_certificate {G : Type*}
    [Group G] {T : Subgroup G} (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hsq : ∀ a ∈ T, a ^ 2 = 1) (h16 : Nat.card T = 16)
    (hC : Subgroup.centralizer (T : Set G) = T) (φ : NQ T ≃* alternatingGroup (Fin 6)) :
    ∃ Ψ : PG 6 rels6 ≃* Subgroup.normalizer (T : Set G),
      Subgroup.map Ψ.toMonoidHom (Subgroup.closure (Set.range tGen)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
  obtain ⟨h1, h2, h3, -⟩ := Certificates.certificate14984
  exact exists_mulEquiv_normalizer hcomm hsq h16 hC φ h1 h2 h3

end CFSG.CGT.T75JM
