module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDTwo
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDHR7
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]


variable {G : Type*} [Group G] {L : Subgroup G}

theorem eq_one_of_fix_map_a5Levi_of_le_highRootSL2 {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {X D : Subgroup G}
    (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype)
    {Y : Subgroup (adjointGroup .E6 K)}
    (hXJ : (X.subgroupOf L).map e.toMonoidHom ≤
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E6 K)) :
      Set (adjointGroup .E6 K)) ≤ Y ⊔ a5Levi K)
    (hY : Y ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut L) (hβX : ∀ a : L, (a : G) ∈ X → β a = a) (hβD : ∀ a : L, (a : G) ∈ D → β a = a)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_fix_a5Levi_of_le_highRootSL2 hf hK hXJ hXc hY hYodd _ (fun x hx => ?_)
      (fun x hx => ?_) n ?_
    · obtain ⟨a, ha, rfl⟩ := hx
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hβX a (mem_subgroupOf.1 ha)]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      have hmem : ((e.symm x : L) : G) ∈ D := by
        rw [hDe]
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hβD _ hmem, MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβn, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem neighbour_standard_E6_of_le_highRootSL2 [Finite G] (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 1 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    (hXJ : (X.subgroupOf L).map e.toMonoidHom ≤
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    {Y : Subgroup (adjointGroup .E6 K)}
    (hYD : Y ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K))) (hYodd : Odd (Nat.card Y))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E6 K)) :
      Set (adjointGroup .E6 K)) ≤ Y ⊔ a5Levi K)
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
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
  have hDq : CFSG.Open.IsQuasisimple D := hDe ▸ isQuasisimple_open_map_a5Levi e
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD hDq
    (eq_one_of_fix_map_a5Levi_of_le_highRootSL2 hf hKc e hDe hXJ hXc hYD hYodd)

theorem neighbour_standard_E6_nonsplit_of_one_le [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 1 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K)
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
  have hXA : (X.subgroupOf L).map e.toMonoidHom = A := by
    rw [hX, F4Pilot.map_subgroupOf_map_symm]
  refine neighbour_standard_E6_of_le_highRootSL2 hL htC ht hK hf hKc e htX (hXA ▸ hAJ) hAD hodd
    (by rw [hXA, hcent]) hDe ?_
  rw [hX, F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcent hAD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) isQuasisimple_a5Levi, hDe]

end CFSG.SeitzReduction.E6Pilot
