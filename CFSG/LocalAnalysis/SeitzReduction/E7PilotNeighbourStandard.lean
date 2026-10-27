module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutD

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K]


theorem exists_eq_conj_of_fix_perpLevi_E7 [Finite K] [CharP K 2]
    (β : MulAut (adjointGroup .E7 K)) (hβ : ∀ x ∈ perpLevi .E7 K, β x = x) :
    ∃ g : adjointGroup .E7 K, β = MulAut.conj g ∧
      g ∈ centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K)) :=
  E8Pilot.exists_eq_conj_of_fix_perpLevi (Or.inl rfl) β hβ

theorem exists_eq_conj_mem_highRootSL2_of_fix_perpLevi_E7 [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (β : MulAut (adjointGroup .E7 K))
    (hβ : ∀ x ∈ perpLevi .E7 K, β x = x) :
    ∃ g : adjointGroup .E7 K, β = MulAut.conj g ∧
      g ∈ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) := by
  obtain ⟨g, hg, hgD⟩ := exists_eq_conj_of_fix_perpLevi_E7 β hβ
  refine ⟨g, hg, ?_⟩
  rw [← centralizer_perpLevi_subgroupOf (Or.inr (Or.inl rfl)) hq]
  exact hgD

theorem eq_one_of_fix_perpLevi_E7 [Finite K] [CharP K 2] {X Y : Subgroup (adjointGroup .E7 K)}
    (hXc : centralizer (X : Set (adjointGroup .E7 K)) ≤ Y ⊔ perpLevi .E7 K)
    (hY : Y ≤ centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut (adjointGroup .E7 K)) (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ perpLevi .E7 K, β d = d) (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 :=
  E8Pilot.eq_one_of_fix_perpLevi_of_center_eq_bot (Or.inl rfl) center_perpLevi_E7_eq_bot hXc hY
    hYodd β hβX hβD n hβn

variable {G : Type*} [Group G] {L : Subgroup G}

theorem eq_one_of_fix_map_perpLevi_E7 [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E7 K)
    {X D : Subgroup G} (hDe : D = ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    {Y : Subgroup (adjointGroup .E7 K)}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E7 K)) :
      Set (adjointGroup .E7 K)) ≤ Y ⊔ perpLevi .E7 K)
    (hY : Y ≤ centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut L) (hβX : ∀ a : L, (a : G) ∈ X → β a = a) (hβD : ∀ a : L, (a : G) ∈ D → β a = a)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_fix_perpLevi_E7 hXc hY hYodd _ (fun x hx => ?_) (fun x hx => ?_) n ?_
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

theorem isQuasisimple_map_perpLevi_E7 [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E7 K) :
    CFSG.IsQuasisimple (((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((perpLevi .E7 K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((perpLevi .E7 K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective))
    (isQuasisimple_perpLevi_E7 (K := K))

theorem isQuasisimple_open_map_perpLevi_E7 [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E7 K) :
    CFSG.Open.IsQuasisimple (((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_perpLevi_E7 e).1.commutator_eq_top, (isQuasisimple_map_perpLevi_E7 e).2.1⟩

theorem neighbour_standard_E7 [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    {Y : Subgroup (adjointGroup .E7 K)}
    (hYD : Y ≤ centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K))) (hYodd : Odd (Nat.card Y))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E7 K)) :
      Set (adjointGroup .E7 K)) ≤ Y ⊔ perpLevi .E7 K)
    {D : Subgroup G} (hDe : D = ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
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
  have hDq : CFSG.Open.IsQuasisimple D := hDe ▸ isQuasisimple_open_map_perpLevi_E7 e
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD hDq
    (eq_one_of_fix_map_perpLevi_E7 e hDe hXc hYD hYodd)

theorem neighbour_standard_E7_of_centralizer_eq_sup [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
    {A Y : Subgroup (adjointGroup .E7 K)}
    (hA : centralizer (A : Set (adjointGroup .E7 K)) = Y ⊔ perpLevi .E7 K)
    (hYD : Y ≤ centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K)))
    (hYc : Y ≤ centralizer (Y : Set (adjointGroup .E7 K))) (hYodd : Odd (Nat.card Y))
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
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
  refine neighbour_standard_E7 hL htC ht hK hKc e htX hYD hYodd ?_ hDe ?_
  · rw [hX, F4Pilot.map_subgroupOf_map_symm, hA]
  · rw [hX, F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hA hYD hYc
      isQuasisimple_perpLevi_E7, hDe]

theorem neighbour_standard_E7_nonsplit [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E7 K)
    {A : Subgroup (adjointGroup .E7 K)}
    (hAJ : A ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
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
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hKc
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E7 hq hAJ hA hcyc
  have hodd : Odd (Nat.card A) := by
    rw [hA, hKc]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact neighbour_standard_E7_of_centralizer_eq_sup hL htC ht hK hKc e hcent hAD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) hodd hX htX hDe

theorem neighbour_standard_E7_of_le_highTorusLine [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {c : Kˣ}
    (hc : 3 ≤ orderOf c) {A : Subgroup (adjointGroup .E7 K)}
    (hAT : A ≤ (highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K))
    (hcA : (⟨rootDiagUnit .E7 (highDiag .E7 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inl rfl)) c⟩ :
        adjointGroup .E7 K) ∈ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
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
  exact neighbour_standard_E7_of_centralizer_eq_sup hL htC ht hK hKc e
    (centralizer_split_E7 hc hAT hcA) highTorusLine_le_centralizer_perpLevi_E7
    E6Pilot.highTorusLine_subgroupOf_le_centralizer_self (odd_card_highTorusLine_E7 hKc) hX htX
    hDe

theorem neighbour_standard_E7_highTorusLine [Finite G] (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E7 K)
    {X : Subgroup G} (hX : X = (((highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
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
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact neighbour_standard_E7_of_le_highTorusLine hL htC ht hK hKc e hc le_rfl
    (mem_subgroupOf.2 (rootDiagUnit_highDiag_mem_highTorusLine c)) hX htX hDe

theorem neighbour_standard_E7_highRootSL2 [Finite G] (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E7 K)
    {X : Subgroup G} (hX : X = (((highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
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
  refine neighbour_standard_E7_of_centralizer_eq_sup hL htC ht hK hKc e (Y := ⊥) ?_ bot_le bot_le
    ?_ hX htX hDe
  · rw [bot_sup_eq]
    exact centralizer_highRootSL2_subgroupOf (Or.inr (Or.inl rfl)) hq
  · rw [card_bot]
    exact odd_one

theorem neighbour_standard_E7_of_highDiag_mem [Finite G] (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {c : Kˣ}
    (hc : 3 ≤ orderOf c) {X : Subgroup G}
    (hcX : ((e.symm ⟨rootDiagUnit .E7 (highDiag .E7 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inl rfl)) c⟩ : L) : G) ∈ X)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
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
  refine neighbour_standard_E7 hL htC ht hK hKc e htX highTorusLine_le_centralizer_perpLevi_E7
    (odd_card_highTorusLine_E7 hKc)
    (E6Pilot.centralizer_le_highTorusLine_sup (Or.inr (Or.inl rfl)) hc ?_) hDe hD
  refine ⟨e.symm ⟨rootDiagUnit .E7 (highDiag .E7 c),
    E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inl rfl)) c⟩,
    mem_subgroupOf.2 hcX, ?_⟩
  simp

end CFSG.SeitzReduction.E7Pilot
