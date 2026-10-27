module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem p_component_normal_p_centralizer {L : Subgroup G} (hL : IsPComponent p L)
    {P : Subgroup G} (hPn : P.Normal) (hP : IsPGroup p P) : ⁅L, P⁆ = ⊥ := by
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  have hPq : (P.map (QuotientGroup.mk' (pPrimeCore p G))).Normal :=
    hPn.map _ (QuotientGroup.mk'_surjective _)
  have hsolv : Group.IsSolvable (P.map (QuotientGroup.mk' (pPrimeCore p G))) := by
    have : IsPGroup p (P.map (QuotientGroup.mk' (pPrimeCore p G))) :=
      hP.of_surjective _ ((QuotientGroup.mk' (pPrimeCore p G)).subgroupMap_surjective P)
    have : Group.IsNilpotent (P.map (QuotientGroup.mk' (pPrimeCore p G))) := this.isNilpotent
    infer_instance
  have h1 : ⁅K, P.map (QuotientGroup.mk' (pPrimeCore p G))⁆ = ⊥ :=
    (component_solvable_centralizer hsolv hPq.isSubnormal).1 K hK
  have h2 : ⁅L, P⁆ ≤ pPrimeCore p G := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore p G), ← Subgroup.map_eq_bot_iff,
      Subgroup.map_commutator, hLK, h1]
  have h3 : ⁅L, P⁆ ≤ P := by
    have := hPn
    exact Subgroup.commutator_le_right L P
  have h4 : P ⊓ pPrimeCore p G = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
    have hd1 : Nat.card (P ⊓ pPrimeCore p G : Subgroup G) ∣ p ^ k :=
      hk ▸ Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card (P ⊓ pPrimeCore p G : Subgroup G) ∣ Nat.card (pPrimeCore p G) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (p ^ k) (Nat.card (pPrimeCore p G)) :=
      Nat.Coprime.pow_left k pPrimeCore_coprime_card
    exact Subgroup.card_eq_one.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  exact le_bot_iff.1 (h4 ▸ le_inf h3 h2)

theorem p_component_normalizer_centralizes {S : Subgroup G} (hS : IsPGroup p S)
    {L : Subgroup (Subgroup.normalizer (S : Set G))} (hL : IsPComponent p L) :
    ⁅L.map (Subgroup.normalizer (S : Set G)).subtype, S⁆ = ⊥ := by
  have hSp : IsPGroup p (S.subgroupOf (Subgroup.normalizer (S : Set G))) :=
    hS.comap_of_injective _ (Subgroup.normalizer (S : Set G)).subtype_injective
  have h := p_component_normal_p_centralizer hL Subgroup.normal_in_normalizer hSp
  have hmap := congrArg (Subgroup.map (Subgroup.normalizer (S : Set G)).subtype) h
  rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left Subgroup.le_normalizer, Subgroup.map_bot] at hmap

theorem p_component_core_centrality_criterion {L : Subgroup G} (hL : IsPComponent p L) :
    (IsQuasisimple L ↔ pPrimeCore p L ≤ Subgroup.center L) ∧
      (pPrimeCore p L ≤ Subgroup.center L ↔ ⁅(⊤ : Subgroup L), pPrimeCore p L⁆ = ⊥) := by
  have hq := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple p L hL
  have hperf := CatalogueBHeldSmallCore.pComponent_perfect p L hL
  refine ⟨⟨fun hLq => ?_, fun hc => ?_⟩, ?_⟩
  · rcases quasisimple_normal_subgroups hLq (pPrimeCore_normal (p := p) (G := L)) with
      htop | hc
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hq
      have hsub : Subsingleton (L ⧸ pPrimeCore p L) := by
        rw [QuotientGroup.subsingleton_iff]
        exact htop
      apply hab
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim a' b']
    · exact hc
  · have := pPrimeCore_normal (p := p) (G := L)
    refine (isQuasisimple_iff_of_surjective hperf (QuotientGroup.mk' (pPrimeCore p L))
      (QuotientGroup.mk'_surjective _) ?_).2 hq
    rw [QuotientGroup.ker_mk']
    exact hc
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.coe_top, Subgroup.centralizer_univ]

@[expose] def badTwoComponentSubgroup (X : Type*) [Group X] : Subgroup X :=
  sSup {L : Subgroup X | IsPComponent 2 L ∧ ¬ IsQuasisimple L}

theorem badTwoComponentSubgroup_eq_closure (X : Type*) [Group X] :
    badTwoComponentSubgroup X = Subgroup.closure
      (⋃ L ∈ {L : Subgroup X | IsPComponent 2 L ∧ ¬ IsQuasisimple L}, (L : Set X)) := by
  apply le_antisymm
  · refine sSup_le fun L hL x hx => Subgroup.subset_closure ?_
    exact Set.mem_biUnion hL hx
  · rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨L, hL, hxL⟩ := Set.mem_iUnion₂.1 hx
    exact le_sSup (s := {L : Subgroup X | IsPComponent 2 L ∧ ¬ IsQuasisimple L}) hL hxL

end CFSG.ComponentClassification.CatalogueBPrimeJoin
