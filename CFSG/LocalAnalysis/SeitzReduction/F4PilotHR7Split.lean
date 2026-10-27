module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section F4

variable {K : Type} [Field K]

theorem odd_card_torusLineR {f : ℕ} (hf : 1 ≤ f) (hKc : Nat.card K = 2 ^ f) :
    Odd (Nat.card (torusLineR K)) := by
  have h : Nat.card (torusLineR K) ∣ Nat.card Kˣ := card_range_dvd _
  rw [Nat.card_units, hKc] at h
  refine Odd.of_dvd_nat (Nat.Even.sub_odd Nat.one_le_two_pow ?_ odd_one) h
  exact (Nat.even_pow' (by omega)).2 even_two

theorem torusLineR_subgroupOf_le_centralizer_self :
    (torusLineR K).subgroupOf (adjointGroup .F4 K) ≤
      centralizer ((torusLineR K).subgroupOf (adjointGroup .F4 K) : Set (adjointGroup .F4 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 (mem_subgroupOf.1 hx)
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 (mem_subgroupOf.1 hy)
  apply Subtype.ext
  rw [coe_mul, coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm]


private theorem C3Set_eq_c3LeviRoots : C3Set = c3LeviRoots := by
  ext γ
  rw [mem_C3Set_iff, mem_c3LeviRoots]
  rfl

private theorem rootSpan_C3Set_subgroupOf_eq :
    (rootSpan .F4 K C3Set).subgroupOf (adjointGroup .F4 K) = C3Levi K := by
  rw [C3Set_eq_c3LeviRoots]
  rfl

theorem torusLineR_le_adjointGroup : torusLineR K ≤ adjointGroup .F4 K := by
  rintro _ ⟨c, rfl⟩
  exact f4RootDiagUnit_mem_adjointGroup _


theorem centralizer_rootSL2R_eq_C3Levi [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    centralizer ((rootSL2R K).subgroupOf (adjointGroup .F4 K) : Set (adjointGroup .F4 K)) =
      C3Levi K := by
  rw [centralizer_rootSL2R_subgroupOf (ringChar.eq K 2) hq, rootSpan_C3Set_subgroupOf_eq]

theorem torusLineR_subgroupOf_le_centralizer :
    (torusLineR K).subgroupOf (adjointGroup .F4 K) ≤
      centralizer (C3Levi K : Set (adjointGroup .F4 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : (y : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
    rw [C3Set_eq_c3LeviRoots]
    exact mem_C3Levi_iff.1 hy
  exact Subtype.ext (commute_of_mem_torusLineR_of_mem_rootSpan (mem_subgroupOf.1 hx) hy').eq.symm

theorem centralizer_le_torusLineR_sup [Finite K] [CharP K 2] {c : Kˣ} (hc : 3 ≤ orderOf c)
    {X : Subgroup (adjointGroup .F4 K)}
    (hcX : (⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :
      adjointGroup .F4 K) ∈ X) :
    centralizer (X : Set (adjointGroup .F4 K)) ≤
      (torusLineR K).subgroupOf (adjointGroup .F4 K) ⊔ C3Levi K := by
  intro g hg
  have hg' := centralizer_le (Set.singleton_subset_iff.2 hcX) hg
  rwa [centralizer_rDiag_eq_subgroupOf (ringChar.eq K 2) hc,
    subgroupOf_sup torusLineR_le_adjointGroup (rootSpan_le_adjointGroup K C3Set),
    rootSpan_C3Set_subgroupOf_eq] at hg'

theorem centralizer_eq_torusLineR_sup_of_le [Finite K] [CharP K 2] {c : Kˣ} (hc : 3 ≤ orderOf c)
    {A : Subgroup (adjointGroup .F4 K)} (hAT : A ≤ (torusLineR K).subgroupOf (adjointGroup .F4 K))
    (hcA : (⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :
      adjointGroup .F4 K) ∈ A) :
    centralizer (A : Set (adjointGroup .F4 K)) =
      (torusLineR K).subgroupOf (adjointGroup .F4 K) ⊔ C3Levi K := by
  refine le_antisymm (centralizer_le_torusLineR_sup hc hcA) (sup_le (fun x hx => ?_) ?_)
  · exact mem_centralizer_iff.2 fun a ha =>
      mem_centralizer_iff.1 (torusLineR_subgroupOf_le_centralizer_self hx) a (hAT ha)
  · rw [← le_centralizer_iff]
    exact hAT.trans torusLineR_subgroupOf_le_centralizer

theorem centralizer_torusLineR_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    centralizer ((torusLineR K).subgroupOf (adjointGroup .F4 K) : Set (adjointGroup .F4 K)) =
      (torusLineR K).subgroupOf (adjointGroup .F4 K) ⊔ C3Levi K := by
  obtain ⟨c, hc⟩ := exists_three_le_orderOf hq
  exact centralizer_eq_torusLineR_sup_of_le hc le_rfl (mem_subgroupOf.2 ⟨c, rfl⟩)

variable {G : Type*} [Group G] {L : Subgroup G}

theorem neighbour_standard_rootSL2R [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {X : Subgroup G} (hX : X = (((rootSL2R K).subgroupOf (adjointGroup .F4 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
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
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := by
    rw [hKc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine neighbour_standard_of_centralizer_eq_sup hL htC ht hK hKc e (Y := ⊥) ?_ bot_le bot_le
    ?_ hX htX hDe
  · rw [centralizer_rootSL2R_eq_C3Levi hq, bot_sup_eq]
  · rw [card_bot]
    exact odd_one

theorem neighbour_standard_of_rDiag_mem [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {c : Kˣ}
    (hc : 3 ≤ orderOf c) {X : Subgroup G}
    (hcX : ((e.symm ⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ : L) : G) ∈ X)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
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
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  have hf := one_le_of_natCard_eq_two_pow hKc
  refine neighbour_standard hL htC ht hK hKc e htX torusLineR_subgroupOf_le_centralizer ?_
    (centralizer_le_torusLineR_sup hc ?_) hDe hD
  · rw [Nat.card_congr (subgroupOfEquivOfLe torusLineR_le_adjointGroup).toEquiv]
    exact odd_card_torusLineR hf hKc
  · refine ⟨e.symm ⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩,
      mem_subgroupOf.2 hcX, ?_⟩
    simp

theorem neighbour_standard_of_le_torusLineR [Finite G] (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {c : Kˣ}
    (hc : 3 ≤ orderOf c) {A : Subgroup (adjointGroup .F4 K)}
    (hAT : A ≤ (torusLineR K).subgroupOf (adjointGroup .F4 K))
    (hcA : (⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :
      adjointGroup .F4 K) ∈ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
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
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  refine neighbour_standard_of_centralizer_eq_sup hL htC ht hK hKc e
    (centralizer_eq_torusLineR_sup_of_le hc hAT hcA) torusLineR_subgroupOf_le_centralizer
    torusLineR_subgroupOf_le_centralizer_self ?_ hX htX hDe
  rw [Nat.card_congr (subgroupOfEquivOfLe torusLineR_le_adjointGroup).toEquiv]
  exact odd_card_torusLineR (one_le_of_natCard_eq_two_pow hKc) hKc

theorem neighbour_standard_torusLineR [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {X : Subgroup G} (hX : X = (((torusLineR K).subgroupOf (adjointGroup .F4 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
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
  have := finite_of_natCard_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := by
    rw [hKc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := exists_three_le_orderOf hq
  exact neighbour_standard_of_le_torusLineR hL htC ht hK hKc e hc le_rfl
    (mem_subgroupOf.2 ⟨c, rfl⟩) hX htX hDe

end F4

end CFSG.SeitzReduction.F4Pilot
