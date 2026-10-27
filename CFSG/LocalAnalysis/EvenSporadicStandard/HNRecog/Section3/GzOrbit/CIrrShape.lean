module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private abbrev ci5_a5g : Type := alternatingGroup (Fin 5)

private theorem ci5_isThreeCycle_swap :
    Equiv.Perm.IsThreeCycle (Equiv.swap (1 : Fin 5) 0 * Equiv.swap (1 : Fin 5) 2) :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (1 : Fin 5)) (b := (0 : Fin 5))
    (c := (2 : Fin 5)) (by decide) (by decide) (by decide)

private def ci5_threeCycleD5 : ci5_a5g :=
  ⟨Equiv.swap (1 : Fin 5) 0 * Equiv.swap (1 : Fin 5) 2, ci5_isThreeCycle_swap.mem_alternatingGroup⟩

private lemma ci5_threeCycleD5_ne_one : ci5_threeCycleD5 ≠ 1 := by
  intro hc
  refine ci5_isThreeCycle_swap.ne_one ?_
  have := congrArg (Subtype.val) hc
  simpa [ci5_threeCycleD5] using this

private lemma ci5_orderOf_threeCycleD5 : orderOf ci5_threeCycleD5 = 3 := by
  rw [ci5_threeCycleD5, Subgroup.orderOf_mk]
  exact ci5_isThreeCycle_swap.orderOf

private theorem ci5_not_isPGroup_two_a5g : ¬ IsPGroup 2 ci5_a5g := by
  intro h
  have hdvd : 2 ∣ orderOf ci5_threeCycleD5 := h.dvd_orderOf ci5_threeCycleD5_ne_one
  rw [ci5_orderOf_threeCycleD5] at hdvd
  norm_num at hdvd

private lemma ci5_natCard_Elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]

private theorem ci5_perm5_normal (M : Subgroup (Equiv.Perm (Fin 5))) [M.Normal] :
    M = ⊥ ∨ alternatingGroup (Fin 5) ≤ M := by
  by_cases h : M = ⊥
  · exact Or.inl h
  · exact Or.inr (Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((Subgroup.nontrivial_iff_ne_bot M).2 h))

private theorem ci5_eq_bot_of_normal_isPGroup_perm5 (M : Subgroup (Equiv.Perm (Fin 5)))
    [M.Normal] (hM : IsPGroup 2 M) : M = ⊥ := by
  rcases ci5_perm5_normal M with h | h
  · exact h
  · exact absurd (IsPGroup.of_injective hM (Subgroup.inclusion h)
      (Subgroup.inclusion_injective h)) ci5_not_isPGroup_two_a5g

private lemma ci5_pCore_le_of_normal_quotient_perm5 {X : Type*} [Group X] {N : Subgroup X}
    [N.Normal] (hq : Nonempty (X ⧸ N ≃* Equiv.Perm (Fin 5))) : CFSG.pCore 2 X ≤ N := by
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  obtain ⟨e⟩ := hq
  have hmap : (CFSG.pCore 2 X).map π = ⊥ := by
    haveI : ((CFSG.pCore 2 X).map π).Normal :=
      Subgroup.Normal.map (inferInstance : (CFSG.pCore 2 X).Normal) π
        (QuotientGroup.mk'_surjective N)
    have hsub : ((CFSG.pCore 2 X).map π).map e.toMonoidHom = ⊥ := by
      haveI : (((CFSG.pCore 2 X).map π).map e.toMonoidHom).Normal :=
        Subgroup.Normal.map ‹((CFSG.pCore 2 X).map π).Normal› e.toMonoidHom e.surjective
      exact ci5_eq_bot_of_normal_isPGroup_perm5 _
        (((CFSG.pCore_isPGroup (p := 2) (G := X)).map π).map e.toMonoidHom)
    rwa [Subgroup.map_eq_bot_iff_of_injective (H := (CFSG.pCore 2 X).map π) e.injective] at hsub
  rw [Subgroup.map_eq_bot_iff] at hmap
  rwa [QuotientGroup.ker_mk'] at hmap

theorem exists_mulEquiv_map_centralizer_perm5 {C : Type} [Group C] [Finite C] {Q : Subgroup C}
    [Q.Normal] (hQ : IsExtraspecialPlusByA5WrTwoWith C Q) (e : C ⧸ Q ≃* A5WrTwo) {q : C}
    (hqQ : q ∈ Q) (hq : q ∉ centerOf Q)
    (hsh : IsShapeTwoTwoSixS5 ↥(Subgroup.centralizer ({q} : Set C))) :
    Nonempty (↥((Subgroup.centralizer ({q} : Set C)).map
      ((e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q))) ≃* Equiv.Perm (Fin 5)) := by
  let X : Subgroup C := Subgroup.centralizer ({q} : Set C)
  let π : C →* A5WrTwo := (e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q)
  have hsh' : IsShapeTwoTwoSixS5 ↥X := hsh
  change Nonempty (↥(X.map π) ≃* Equiv.Perm (Fin 5))
  obtain ⟨V, N, hVnorm, hNnorm, hVN, hVshape, hNVshape, hXshape⟩ := hsh'
  haveI : N.Normal := hNnorm
  have hNcard : Nat.card N = 2 ^ 8 := by
    have hVcard : Nat.card V = 2 ^ 2 := by
      obtain ⟨eV⟩ := hVshape
      rw [Nat.card_congr eV.toEquiv, ci5_natCard_Elem2]
    have hNVcard : Nat.card (N ⧸ V.subgroupOf N) = 2 ^ 6 := by
      obtain ⟨eNV⟩ := hNVshape
      rw [Nat.card_congr eNV.toEquiv, ci5_natCard_Elem2]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf N)
    have hVsub : Nat.card (V.subgroupOf N) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
    rw [h1, hNVcard, hVsub, hVcard]
    norm_num
  have hQsub_pg : IsPGroup 2 ↥(Q.subgroupOf X) :=
    (hQ.plus.1.isPGroup).comap_of_injective X.subtype Subtype.coe_injective
  have hpCoreN : CFSG.pCore 2 ↥X ≤ N := ci5_pCore_le_of_normal_quotient_perm5 hXshape
  have hQsub_le : Q.subgroupOf X ≤ N := by
    refine le_trans ?_ hpCoreN
    rw [CFSG.pCore]
    exact le_sSup ⟨inferInstance, hQsub_pg⟩
  have hQsub_card : Nat.card ↥(Q.subgroupOf X) = 2 ^ 8 := by
    have hmap := Nat.card_congr (Subgroup.equivMapOfInjective (Q.subgroupOf X) X.subtype
      Subtype.coe_injective).toEquiv
    rw [Subgroup.subgroupOf_map_subtype] at hmap
    rw [hmap]
    exact card_inf_centralizer_of_isPlusExtraspecial hQ.plus hqQ hq
  have hQsub_eq_N : Q.subgroupOf X = N := by
    have hcards : Nat.card N = Nat.card ↥(Q.subgroupOf X) := by rw [hNcard, hQsub_card]
    exact Subgroup.eq_of_le_of_card_ge hQsub_le hcards.le
  let ρ : ↥X →* A5WrTwo := π.comp X.subtype
  have hker_pi : π.ker = Q := by
    show ((e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q)).ker = Q
    have heker : (e : C ⧸ Q →* A5WrTwo).ker = ⊥ :=
      MonoidHom.ker_eq_bot (e : C ⧸ Q →* A5WrTwo) e.injective
    rw [← MonoidHom.comap_ker, heker, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hker : ρ.ker = Q.subgroupOf X := by
    show (π.comp X.subtype).ker = Q.subgroupOf X
    rw [← MonoidHom.comap_ker, hker_pi]
    rfl
  have hrange : ρ.range = X.map π := by
    show (π.comp X.subtype).range = X.map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e5⟩ := hXshape
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange ρ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hker.trans hQsub_eq_N)).trans e5))⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
