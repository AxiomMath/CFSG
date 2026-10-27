module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutD

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]


variable {G : Type*} [Group G] {L : Subgroup G}

theorem eq_one_of_fix_map_a5Levi {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {X D : Subgroup G}
    (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype)
    {Y : Subgroup (adjointGroup .E6 K)}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E6 K)) :
      Set (adjointGroup .E6 K)) ≤ Y ⊔ a5Levi K)
    (hY : Y ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut L) (hβX : ∀ a : L, (a : G) ∈ X → β a = a) (hβD : ∀ a : L, (a : G) ∈ D → β a = a)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_fix_a5Levi hf hK hXc hY hYodd _ (fun x hx => ?_) (fun x hx => ?_) n ?_
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

theorem isQuasisimple_map_a5Levi [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E6 K) :
    CFSG.IsQuasisimple (((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((a5Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((a5Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective))
    (isQuasisimple_a5Levi (K := K))

theorem isQuasisimple_open_map_a5Levi [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E6 K) :
    CFSG.Open.IsQuasisimple (((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_a5Levi e).1.commutator_eq_top, (isQuasisimple_map_a5Levi e).2.1⟩

theorem neighbour_standard_E6 [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
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
    (eq_one_of_fix_map_a5Levi hf hKc e hDe hXc hYD hYodd)

theorem neighbour_standard_E6_of_centralizer_eq_sup [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K)
    {A Y : Subgroup (adjointGroup .E6 K)}
    (hA : centralizer (A : Set (adjointGroup .E6 K)) = Y ⊔ a5Levi K)
    (hYD : Y ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K)))
    (hYc : Y ≤ centralizer (Y : Set (adjointGroup .E6 K))) (hYodd : Odd (Nat.card Y))
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
  refine neighbour_standard_E6 hL htC ht hK hf hKc e htX hYD hYodd ?_ hDe ?_
  · rw [hX, F4Pilot.map_subgroupOf_map_symm, hA]
  · rw [hX, F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hA hYD hYc isQuasisimple_a5Levi,
      hDe]

end CFSG.SeitzReduction.E6Pilot
