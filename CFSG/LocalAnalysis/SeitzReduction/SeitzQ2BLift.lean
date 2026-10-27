module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLift

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

variable {G : Type} [Group G]

theorem forall_odd_mem_of_two {L : Subgroup G} (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X D : Subgroup G} (hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  rintro c ⟨⟨hcX, hct⟩, hcD⟩ hco
  exact hXD ⟨⟨mem_of_odd_of_mem_centralizer hOut htC ht htL hCN hK hct hco, hcX⟩, hcD⟩

theorem inf_centralizer_le_of_le_sup {L X D : Subgroup G}
    (hLX : L ⊓ centralizer (X : Set G) ≤ X ⊔ D) (hXD : X ≤ centralizer (D : Set G))
    (hZD : center D = ⊥) : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X := by
  rintro c ⟨hcLX, hcD⟩
  have hc : c ∈ ((X ⊔ D : Subgroup G) : Set G) := hLX hcLX
  rw [coe_mul_of_left_le_normalizer_right _ _ (hXD.trans (centralizer_le_normalizer _))] at hc
  obtain ⟨x, hx, d, hd, rfl⟩ := Set.mem_mul.1 hc
  have hxD : x ∈ centralizer (D : Set G) := hXD hx
  have hdD : d ∈ centralizer (D : Set G) := by
    have h := mul_mem (inv_mem hxD) hcD
    rwa [inv_mul_cancel_left] at h
  have hdZ : (⟨d, hd⟩ : D) ∈ center D :=
    mem_center_iff.2 fun e => Subtype.ext (mem_centralizer_iff.1 hdD e e.2)
  rw [hZD, mem_bot] at hdZ
  have hd1 : d = 1 := congrArg Subtype.val hdZ
  rw [hd1, mul_one]
  exact hx

variable [Finite G]

theorem hasBLift_of_isPGroup_outer {L : Subgroup G} (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X)
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E :=
  LinearPilot.hasBLift_of_forall_odd_mem htC ht hCN htX hD hDq
    (forall_odd_mem_of_two hOut htC ht htL hCN hK hXD) hE htE hEt

theorem isComponent_oddCoreLift_of_isPGroup_outer {L : Subgroup G}
    (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X)
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : CFSG.IsComponent E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (htE' : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) :
    HasBLift E ∧ CFSG.IsComponent (oddCoreLift E) ∧
      (oddCoreLift E).map (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = E ∧
      (oddCore (centralizer (X : Set G))).subgroupOf (oddCoreLift E) ≤ center (oddCoreLift E) :=
  LinearPilot.isComponent_oddCoreLift_of_forall_odd_mem htC ht hCN htX hD hDq
    (forall_odd_mem_of_two hOut htC ht htL hCN hK hXD) hE htE htE'

end CFSG.SeitzReduction.SeitzQ2
