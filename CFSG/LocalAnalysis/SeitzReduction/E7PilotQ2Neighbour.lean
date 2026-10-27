module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourStandard
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitRankOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley


section Centralizer

variable {τ : Tag} {K : Type} [Field K]

theorem isRoot_and_height_neg_rootReflection_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ parabolicRadicalRoots τ (perpNodes τ)) :
    IsRoot τ (rootReflection (highRoot τ) • β) ∧
      height (rootReflection (highRoot τ) • β) < 0 := by
  obtain ⟨hr, hpos⟩ := mem_parabolicRadicalRoots_perpNodes.1 hβ
  have hr' : IsRoot τ (rootReflection (highRoot τ) • β) := IsRoot.smul hr _
  have hcoef : (rootReflection (highRoot τ) • β) (highNode τ) = -β (highNode τ) := by
    rw [rootReflection_smul (isRoot_highRoot τ), Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      corootPair_highRoot hτ, highRoot_highNode hτ]
    ring
  refine ⟨hr', ?_⟩
  rcases IsRoot.height_pos_or_neg hr' with h | h
  · have := (IsRoot.height_pos_iff hr').1 h (highNode τ)
    rw [hcoef] at this
    omega
  · exact h

theorem adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    adjointGroup τ K ⊓ centralizer (highRootSL2 τ K : Set (ModGL τ K)) =
      rootSpan τ K (perpRoots τ) := by
  refine le_antisymm (fun g hg => ?_)
    (le_inf (rootSpan_le_adjointGroup' _) (rootSpan_perpRoots_le_centralizer_highRootSL2 hτ))
  obtain ⟨hgC, hgJ⟩ := Subgroup.mem_inf.1 hg
  have hxJ : pinnedX τ K (highRoot τ) 1 ∈ highRootSL2 τ K :=
    rootSubgroup_highRoot_le_highRootSL2 (Subgroup.subset_closure ⟨1, rfl⟩)
  have hg1 : g ∈ centralizer ({pinnedX τ K (highRoot τ) 1} : Set (ModGL τ K)) ⊓
      adjointGroup τ K := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 ?_, hgC⟩
    rintro _ rfl
    exact (Subgroup.mem_centralizer_iff.1 hgJ _ hxJ)
  rw [centralizer_pinnedX_highRoot_inf_eq hτ one_ne_zero, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _
      rootSpan_perpRoots_le_normalizer_parabolicRadical] at hg1
  obtain ⟨u, hu, d, hd, rfl⟩ := Set.mem_mul.1 hg1
  have hdJ := rootSpan_perpRoots_le_centralizer_highRootSL2 hτ hd
  have huJ : u ∈ centralizer (highRootSL2 τ K : Set (ModGL τ K)) := by
    have h := mul_mem hgJ (inv_mem hdJ)
    rwa [mul_inv_cancel_right] at h
  obtain ⟨-, -, -, -, hn, -⟩ := even_Chevalley_pinned_root_SL2_maps τ K (isRoot_highRoot τ)
  obtain ⟨-, -, hnmon, hnw⟩ := hn 1
  have hnJ : rootWeylSL2 τ K (highRoot τ) 1 ∈ highRootSL2 τ K :=
    E6Pilot.rootSL2_highRoot_mem_highRootSL2 _
  have hun : rootWeylSL2 τ K (highRoot τ) 1 * u * (rootWeylSL2 τ K (highRoot τ) 1)⁻¹ = u := by
    rw [Subgroup.mem_centralizer_iff.1 huJ _ hnJ, mul_inv_cancel_right]
  have huneg : u ∈ negUnipotent τ K := by
    have hmem : rootWeylSL2 τ K (highRoot τ) 1 * u * (rootWeylSL2 τ K (highRoot τ) 1)⁻¹ ∈
        (parabolicRadical τ K (perpNodes τ)).map
          (MulAut.conj (rootWeylSL2 τ K (highRoot τ) 1)).toMonoidHom := ⟨u, hu, rfl⟩
    rw [parabolicRadical, map_conj_rootSpan_of_mem_monomialSubgroup hnmon
      (fun α hα => hα.1.1), hnw, hun] at hmem
    refine rootSpan_le_negUnipotent ?_ hmem
    rintro _ ⟨β, hβ, rfl⟩
    exact isRoot_and_height_neg_rootReflection_highRoot hτ hβ
  have hu1 : u = 1 := by
    have h := Subgroup.mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ hu, huneg⟩
    rwa [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h
  rw [hu1, one_mul]
  exact hd

theorem centralizer_highRootSL2_subgroupOf_of_charTwo [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    centralizer ((highRootSL2 τ K).subgroupOf (adjointGroup τ K) : Set (adjointGroup τ K)) =
      (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  ext g
  rw [Subgroup.mem_subgroupOf, ← adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo hτ,
    Subgroup.mem_inf]
  refine ⟨fun h => ⟨g.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩,
    fun h => Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  · have := Subgroup.mem_centralizer_iff.1 h ⟨y, highRootSL2_le_adjointGroup hy⟩
      (Subgroup.mem_subgroupOf.2 hy)
    exact congrArg Subtype.val this
  · exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h.2 y (Subgroup.mem_subgroupOf.1 hy))

end Centralizer

section E7

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem centralizer_highRootSL2_subgroupOf_E7_of_charTwo :
    centralizer ((highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) : Set (adjointGroup .E7 K)) =
      perpLevi .E7 K :=
  centralizer_highRootSL2_subgroupOf_of_charTwo (Or.inr (Or.inl rfl))

theorem perpLevi_le_centralizer_highRootSL2_E7_of_charTwo :
    perpLevi .E7 K ≤ centralizer ((highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) :
      Set (adjointGroup .E7 K)) :=
  centralizer_highRootSL2_subgroupOf_E7_of_charTwo.symm.le

theorem perpLeviFrobDescent_E7_of_finite : E6Pilot.PerpLeviFrobDescent .E7 K := by
  intro d hd hσd
  set ι := algebraMap K (FiniteField.Extension K 2 2) with hι
  obtain ⟨g₀, hg₀, hg₀d⟩ :=
    E8Pilot.exists_baseChangeGL_eq_of_frob_fixed_E7 (rootSpan_le_adjointGroup' _ hd) hσd
  refine ⟨g₀, ?_, hg₀d⟩
  rw [← adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo (Or.inr (Or.inl rfl))]
  refine Subgroup.mem_inf.2 ⟨hg₀, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
  have hjJ := baseChangeGL_mem_highRootSL2_E7 ι hj
  have hdJ := Subgroup.mem_centralizer_iff.1
    (rootSpan_perpRoots_le_centralizer_highRootSL2 (K := FiniteField.Extension K 2 2)
      (Or.inr (Or.inl rfl)) hd) _ hjJ
  apply baseChangeGL_injective ι
  rw [map_mul, map_mul, hg₀d]
  exact hdJ

theorem centralizer_nonsplit_E7_of_finite {X : Subgroup (adjointGroup .E7 K)}
    (hXJ : X ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    centralizer (X : Set (adjointGroup .E7 K)) = X ⊔ perpLevi .E7 K ∧
      Disjoint X (perpLevi .E7 K) ∧
      X ≤ centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K)) :=
  E6Pilot.centralizer_nonsplit_of_descent (Or.inr (Or.inl rfl)) perpLeviFrobDescent_E7_of_finite
    hXJ hcyc hX

theorem exists_mul_of_mem_centralizer_nonsplit_E7_of_finite {X : Subgroup (adjointGroup .E7 K)}
    (hXJ : X ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) {c : adjointGroup .E7 K}
    (hc : c ∈ centralizer (X : Set (adjointGroup .E7 K))) :
    ∃ y ∈ X, ∃ d ∈ perpLevi .E7 K, c = y * d :=
  E6Pilot.exists_mul_of_mem_centralizer_nonsplit_of_descent (Or.inr (Or.inl rfl))
    perpLeviFrobDescent_E7_of_finite hXJ hcyc hX hc

theorem inSubgroup_layer_inf_centralizer_nonsplit_E7_of_finite {G : Type} [Group G]
    {L : Subgroup G} (e : L ≃* adjointGroup .E7 K) {X : Subgroup (adjointGroup .E7 K)}
    (hXJ : X ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    inSubgroup layer
        (L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨hcen, -, hXD⟩ := centralizer_nonsplit_E7_of_finite hXJ hX hcyc
  exact F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcen hXD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) isQuasisimple_perpLevi_E7

theorem inf_centralizer_nonsplit_E7_of_finite {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E7 K) {X : Subgroup (adjointGroup .E7 K)}
    (hXJ : X ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) =
      (X.map e.symm.toMonoidHom).map L.subtype ⊔
        ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := by
  rw [F4Pilot.inf_centralizer_map_symm, (centralizer_nonsplit_E7_of_finite hXJ hX hcyc).1,
    Subgroup.map_sup, Subgroup.map_sup]

theorem map_perpLevi_le_centralizer_E7_of_charTwo {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E7 K) {X : Subgroup G}
    (hXJ : X ≤ (((highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).map
      e.symm.toMonoidHom).map L.subtype) :
    ((perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G) :=
  (F4Pilot.map_le_centralizer_map L.subtype
    (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom
      perpLevi_le_centralizer_highRootSL2_E7_of_charTwo)).trans (centralizer_le hXJ)

end E7

section HR7

open CFSG.Open

variable {K : Type} [Field K] {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_standard_E7_nonsplit_of_finite (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
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
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E7_of_finite hAJ hA hcyc
  have hodd : Odd (Nat.card A) := by
    rw [hA, hKc]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact neighbour_standard_E7_of_centralizer_eq_sup hL htC ht hK hKc e hcent hAD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) hodd hX htX hDe

theorem neighbour_standard_E7_nonsplit_two (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hKc : Nat.card K = 2) (e : L ≃* adjointGroup .E7 K)
    {A : Subgroup (adjointGroup .E7 K)}
    (hAJ : A ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)) (hA : Nat.card A = 3)
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
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact neighbour_standard_E7_nonsplit_of_finite hL htC ht hK (f := 1)
    (by rw [pow_one]; exact hKc) e hAJ (by rw [hA, hKc]) (isCyclic_of_prime_card hA) hX htX hDe

end HR7

end CFSG.SeitzReduction.E7Pilot
