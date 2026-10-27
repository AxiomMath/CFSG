module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutD
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviNonsplit

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K]

variable {G : Type*} [Group G] {L : Subgroup G}

theorem eq_one_of_fix_map_e7Levi [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E8 K)
    {X D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    {Y : Subgroup (adjointGroup .E8 K)}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) ≤ Y ⊔ e7Levi K)
    (hY : Y ≤ centralizer (e7Levi K : Set (adjointGroup .E8 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut L) (hβX : ∀ a : L, (a : G) ∈ X → β a = a) (hβD : ∀ a : L, (a : G) ∈ D → β a = a)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_fix_e7Levi hXc hY hYodd _ (fun x hx => ?_) (fun x hx => ?_) n ?_
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

theorem isQuasisimple_map_e7Levi [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E8 K) :
    CFSG.IsQuasisimple (((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((e7Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((e7Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective))
    (isQuasisimple_e7Levi (K := K))

theorem isQuasisimple_open_map_e7Levi [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E8 K) :
    CFSG.Open.IsQuasisimple (((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_e7Levi e).1.commutator_eq_top, (isQuasisimple_map_e7Levi e).2.1⟩

theorem neighbour_standard_E8 [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    {Y : Subgroup (adjointGroup .E8 K)}
    (hYD : Y ≤ centralizer (e7Levi K : Set (adjointGroup .E8 K))) (hYodd : Odd (Nat.card Y))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) ≤ Y ⊔ e7Levi K)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
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
  have hDq : CFSG.Open.IsQuasisimple D := hDe ▸ isQuasisimple_open_map_e7Levi e
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD hDq
    (eq_one_of_fix_map_e7Levi e hDe hXc hYD hYodd)

theorem neighbour_standard_E8_of_centralizer_eq_sup [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K)
    {A Y : Subgroup (adjointGroup .E8 K)}
    (hA : centralizer (A : Set (adjointGroup .E8 K)) = Y ⊔ e7Levi K)
    (hYD : Y ≤ centralizer (e7Levi K : Set (adjointGroup .E8 K)))
    (hYc : Y ≤ centralizer (Y : Set (adjointGroup .E8 K))) (hYodd : Odd (Nat.card Y))
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
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
  refine neighbour_standard_E8 hL htC ht hK hKc e htX hYD hYodd ?_ hDe ?_
  · rw [hX, F4Pilot.map_subgroupOf_map_symm, hA]
  · rw [hX, F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hA hYD hYc isQuasisimple_e7Levi,
      hDe]

theorem centralizer_highRootSL2_subgroupOf_E8 [Finite K] [CharP K 2] :
    centralizer ((EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K) :
      Set (adjointGroup .E8 K)) = e7Levi K := by
  obtain ⟨A, hAJ, hcyc, hA⟩ :=
    E6Pilot.exists_nonsplit_le_subgroupOf_highRootSL2 (τ := .E8) (K := K)
  obtain ⟨hcen, -, hAD⟩ := centralizer_nonsplit_E8 hAJ hA hcyc
  have hDJ : e7Levi K ≤ centralizer ((EPilot.highRootSL2 .E8 K).subgroupOf
      (adjointGroup .E8 K) : Set (adjointGroup .E8 K)) := by
    intro d hd
    refine mem_centralizer_iff.2 fun j hj => Subtype.ext ?_
    exact (mem_centralizer_iff.1 (EPilot.highRootSL2_le_centralizer_perpLevi
      (Or.inr (Or.inr rfl)) (mem_subgroupOf.1 hj)) _ (mem_e7Levi_iff.1 hd)).symm
  refine le_antisymm (fun g hg => ?_) hDJ
  have hgA : g ∈ centralizer (A : Set (adjointGroup .E8 K)) := Subgroup.centralizer_le hAJ hg
  rw [hcen] at hgA
  have hAN : A ≤ normalizer (e7Levi K : Set (adjointGroup .E8 K)) :=
    hAD.trans (Subgroup.centralizer_le_normalizer _)
  have hg' : g ∈ ((A ⊔ e7Levi K : Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) :=
    hgA
  rw [coe_mul_of_left_le_normalizer_right _ _ hAN] at hg'
  obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hg'
  have haJ : a ∈ centralizer ((EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K) :
      Set (adjointGroup .E8 K)) := by
    have := mul_mem hg (inv_mem (hDJ hd))
    rwa [mul_inv_cancel_right] at this
  have haJ' : (a : ModGL .E8 K) ∈ EPilot.highRootSL2 .E8 K := mem_subgroupOf.1 (hAJ ha)
  rw [← E6Pilot.range_rootSL2_highRoot] at haJ'
  obtain ⟨B, hB⟩ := haJ'
  have hBc : B ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [mem_center_iff]
    intro B'
    apply E6Pilot.rootSL2_highRoot_injective (τ := .E8)
    have h := mem_centralizer_iff.1 haJ
      ⟨_, E6Pilot.rootSL2_highRoot_mem_adjointGroup (τ := .E8) B'⟩
      (mem_subgroupOf.2 (E6Pilot.rootSL2_highRoot_mem_highRootSL2 B'))
    have h' := congrArg (fun x : adjointGroup .E8 K => (x : ModGL .E8 K)) h
    simp only [Subgroup.coe_mul] at h'
    rw [map_mul, map_mul, hB]
    exact h'
  have ha1 : a = 1 := by
    apply Subtype.ext
    rw [← hB, E6Pilot.eq_one_of_mem_center_SL2 hBc, map_one]
    rfl
  rw [ha1, one_mul]
  exact hd

theorem neighbour_standard_E8_nonsplit [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K)
    {A : Subgroup (adjointGroup .E8 K)}
    (hAJ : A ≤ (EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K))
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
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
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E8 hAJ hA hcyc
  have hodd : Odd (Nat.card A) := by
    rw [hA, hKc]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact neighbour_standard_E8_of_centralizer_eq_sup hL htC ht hK hKc e hcent hAD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) hodd hX htX hDe

theorem neighbour_standard_E8_of_le_highTorusLine [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {c : Kˣ}
    (hc : 3 ≤ orderOf c) {A : Subgroup (adjointGroup .E8 K)}
    (hAT : A ≤ (EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K))
    (hcA : (⟨rootDiagUnit .E8 (EPilot.highDiag .E8 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inr rfl)) c⟩ :
        adjointGroup .E8 K) ∈ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
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
  refine neighbour_standard_E8_of_centralizer_eq_sup hL htC ht hK hKc e
    (E6Pilot.centralizer_eq_highTorusLine_sup_of_le (Or.inr (Or.inr rfl)) hc hAT hcA)
    E6Pilot.highTorusLine_subgroupOf_le_centralizer_perpLevi
    E6Pilot.highTorusLine_subgroupOf_le_centralizer_self ?_ hX htX hDe
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (E6Pilot.highTorusLine_le_adjointGroup (Or.inr (Or.inr rfl)))).toEquiv]
  exact E6Pilot.odd_card_highTorusLine (F4Pilot.one_le_of_natCard_eq_two_pow hKc) hKc

theorem neighbour_standard_E8_highTorusLine [Finite G] (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K)
    {X : Subgroup G} (hX : X = (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
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
  have hq : 4 ≤ Nat.card K := by
    rw [hKc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact neighbour_standard_E8_of_le_highTorusLine hL htC ht hK hKc e hc le_rfl
    (mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c)) hX htX hDe

end CFSG.SeitzReduction.E8Pilot
