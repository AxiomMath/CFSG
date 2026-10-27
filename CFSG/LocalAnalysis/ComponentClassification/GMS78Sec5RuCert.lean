module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCode
public import Certificates.Certificate15081

public section

namespace CFSG.ComponentClassification.GMS78

theorem ruSpan_check : CFSG.GMS78Ru.c1Check = true :=
  Certificates.certificate15081.1

theorem ruVLike_check : CFSG.GMS78Ru.c2Check = true :=
  Certificates.certificate15081.2.1

theorem ruIso_check : CFSG.GMS78Ru.c3Check = true :=
  Certificates.certificate15081.2.2

namespace VLike

local notation "GF" => GaloisField 2 (2 * 1 + 1)

theorem closure_sqMap_perp_eq_top_of_card_four
    {Λ : AddSubgroup GF} (hΛ : Nat.card Λ = 4) {c e : GF} (hc : c ≠ 0) {x : GF × GF × GF}
    (hx : x.2.2 ∈ Λ) (hu : x.1 ≠ 0) (hr : x.2.1 ≠ 0) (hQ : sqMap 1 c e x = 0) :
    AddSubgroup.closure (sqMap 1 c e '' perp 1 c Λ x) = ⊤ :=
  RuCode.closure_eq_top_of_c1 ruSpan_check hΛ hc hx hu hr hQ

theorem Hyp.special_of_card_four [Fintype GF]
    {Λ : AddSubgroup GF} (hΛ : Nat.card Λ = 4) {c e : GF} {E : AddSubgroup (GF × GF × GF)}
    (h : Hyp 1 c e Λ E) :
    ∃ c' e' p q : Fin 8, RuCode.toGF c' = c ∧ RuCode.toGF e' = e ∧
      CFSG.GMS78Ru.canon p q = true ∧
      (∀ t, RuCode.toGF t ∈ Λ ↔ t ∈ CFSG.GMS78Ru.lamList p q) ∧
      (c', e', p, q) ∈ CFSG.GMS78Ru.specialList :=
  RuCode.special_of_c2 ruVLike_check hΛ h

theorem eq_self_of_card_four {Λ : AddSubgroup GF}
    (hΛ : Nat.card Λ = 4) (c e : GF) (M : GF × GF × GF → GF × GF × GF)
    (hmem : ∀ x : GF × GF × GF, x.2.2 ∈ Λ → (M x).2.2 ∈ Λ)
    (hadd : ∀ x y : GF × GF × GF, x.2.2 ∈ Λ → y.2.2 ∈ Λ → M (x + y) = M x + M y)
    (hQ : ∀ x : GF × GF × GF, x.2.2 ∈ Λ → sqMap 1 c e (M x) = sqMap 1 c e x) :
    ∀ x : GF × GF × GF, x.2.2 ∈ Λ → M x = x :=
  RuCode.eq_self_of_c3 ruIso_check hΛ c e M hmem hadd hQ

end VLike

end CFSG.ComponentClassification.GMS78
