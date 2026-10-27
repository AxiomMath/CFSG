module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDHR7
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]


variable {G : Type*} [Group G] {L : Subgroup G}

theorem neighbour_standard_E6_nonsplit [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K)
    {A : Subgroup (adjointGroup .E6 K)}
    (hAJ : A ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hKc
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E6 hAJ hA hcyc
  have hodd : Odd (Nat.card A) := by
    rw [hA, hKc]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact neighbour_standard_E6_of_centralizer_eq_sup hL htC ht hK hf hKc e hcent hAD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) hodd hX htX hDe

end CFSG.SeitzReduction.E6Pilot
