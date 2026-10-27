module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaQuotientCriterion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneIndependence

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def ThetaPlaneCondition {G : Type u} [Group G] (prime : ℕ) (actor : Subgroup G) : Prop :=
  ∀ plane : Subgroup G, plane ≤ actor → Nat.card plane = prime ^ 2 →
    ∀ element ∈ plane, element ≠ 1 →
      ⁅thetaCoreOf prime (Subgroup.centralizer (plane : Set G)), actor⁆ ≤
        thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))

theorem centralizer_join_zpowers {G : Type u} [Group G] (first second : G) :
    Subgroup.centralizer ((Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup G) : Set G) =
      Subgroup.centralizer ({first} : Set G) ⊓ Subgroup.centralizer ({second} : Set G) := by
  apply le_antisymm
  · exact le_inf
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers first))))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers second))))
  · intro element helement
    apply Subgroup.mem_centralizer_iff.mpr
    have hfirst : Subgroup.zpowers first ≤ Subgroup.centralizer ({element} : Set G) := by
      apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp helement.1).symm
    have hsecond : Subgroup.zpowers second ≤ Subgroup.centralizer ({element} : Set G) := by
      apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp helement.2).symm
    intro member hmember
    exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hfirst hsecond) hmember)

theorem theta_internal_element_commutator_le_local_alpha
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane larger : Subgroup G) (hle : plane ≤ larger)
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    ⁅thetaCoreOf prime (larger ⊓ Subgroup.centralizer ({element} : Set G)), plane⁆ ≤
      (thetaPlaneAlpha prime (plane.subgroupOf larger)).map larger.subtype := by
  have helement : element ∈ larger := hle hmem
  have hmap :
      (⁅thetaCoreOf prime (Subgroup.centralizer ({⟨element, helement⟩} : Set larger)),
        plane.subgroupOf larger⁆).map larger.subtype =
      ⁅thetaCoreOf prime (larger ⊓ Subgroup.centralizer ({element} : Set G)), plane⁆ := by
    rw [Subgroup.map_commutator, thetaCoreOf_element_centralizer_subtype_map prime hprime,
      Subgroup.map_subgroupOf_eq_of_le hle]
  rw [← hmap]
  apply Subgroup.map_mono
  apply le_sup_of_le_left
  exact le_iSup_of_le (⟨element, helement⟩ : larger) (le_iSup_of_le hmem
    (le_iSup_of_le (fun heq => hne (congrArg Subtype.val heq)) le_rfl))

theorem thetaPlaneCondition_of_rank_three_local_planes
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3)
    (hlocal : ∀ element ∈ actor, element ≠ 1 → ∀ plane : Subgroup G,
      plane ≤ actor → Nat.card plane = prime ^ 2 →
        thetaPlaneAlpha prime (plane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
          solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime) :
    ThetaPlaneCondition prime actor := by
  intro plane hplaneLe hplaneCard element helement hne
  have hlineLe : Subgroup.zpowers element ≤ plane := Subgroup.zpowers_le_of_mem helement
  have hlineCard := elementary_line_card prime hprime actor hab element (hplaneLe helement) hne
  have hlineLt : Subgroup.zpowers element < plane := by
    apply lt_of_le_of_ne hlineLe
    intro heq
    have hcard := congrArg (fun subgroup : Subgroup G => Nat.card subgroup) heq
    rw [hlineCard, hplaneCard] at hcard
    nlinarith [hprime.two_le]
  obtain ⟨other, hother, houtside⟩ := IsConcreteLE.exists_of_lt hlineLt
  have hotherNe : other ≠ 1 := fun heq => houtside (heq ▸ (Subgroup.zpowers element).one_mem)
  have hotherCard := elementary_line_card prime hprime actor hab other (hplaneLe hother) hotherNe
  have helementOutside : element ∉ Subgroup.zpowers other := by
    intro hmem
    have hlineEq : Subgroup.zpowers element = Subgroup.zpowers other :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hmem)
        (by rw [hlineCard, hotherCard])
    exact houtside (hlineEq.symm ▸ Subgroup.mem_zpowers other)
  have hplaneEq : plane = Subgroup.zpowers element ⊔ Subgroup.zpowers other := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge (sup_le hlineLe (Subgroup.zpowers_le_of_mem hother))
    rw [independent_elementary_pair_plane_card prime hprime actor hab element other
      (hplaneLe helement) (hplaneLe hother) hne houtside, hplaneCard]
  obtain ⟨complement, hcomplementLe, hotherComplement, hcomplementCard, hactorEq⟩ :=
    rank_three_actor_complementary_plane prime hprime actor hab hactorCard other element
      (hplaneLe hother) (hplaneLe helement) hotherNe helementOutside
  have hcomplementCentralizer := hcomplementLe.trans
    (commutative_plane_le_element_centralizer actor hab.1 element (hplaneLe helement))
  have hlineNormalizes : Subgroup.zpowers element ≤ Subgroup.normalizer (complement : Set G) :=
    (Subgroup.zpowers_le_of_mem (hplaneLe helement)).trans
      (commutative_actor_normalizes_plane actor complement hab.1 hcomplementLe)
  have hlineFixed : Subgroup.zpowers element ≤
      Subgroup.centralizer (thetaCoreOf prime (Subgroup.centralizer (plane : Set G)) : Set G) := by
    apply Subgroup.zpowers_le.mpr
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    exact (Subgroup.mem_centralizer_iff.mp (thetaCoreOf_le prime _ hmember) element helement).symm
  have hlocalAlpha := theta_internal_element_commutator_le_local_alpha prime hprime complement
    (Subgroup.centralizer ({element} : Set G)) hcomplementCentralizer other hotherComplement hotherNe
  rw [hactorEq, Subgroup.commutator_comm,
    normalized_sup_commutator_eq_of_fixed complement (Subgroup.zpowers element) _
      hlineNormalizes hlineFixed, Subgroup.commutator_comm]
  rw [hplaneEq, centralizer_join_zpowers]
  exact hlocalAlpha.trans (Subgroup.map_mono
    (f := (Subgroup.centralizer ({element} : Set G)).subtype)
      (hlocal element (hplaneLe helement) hne complement hcomplementLe hcomplementCard))

theorem ThetaPlaneCondition.mixed_balance
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hcondition : ThetaPlaneCondition prime actor)
    (first second : G) (hfirst : first ∈ actor) (hsecond : second ∈ actor)
    (hfirstNe : first ≠ 1) (hsecondNe : second ≠ 1) :
    ⁅Subgroup.centralizer ({second} : Set G) ⊓
      thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
        thetaCoreOf prime (Subgroup.centralizer ({second} : Set G)) := by
  by_cases hsameLine : second ∈ Subgroup.zpowers first
  · have hfirstCard := elementary_line_card prime hprime actor hab first hfirst hfirstNe
    have hsecondCard := elementary_line_card prime hprime actor hab second hsecond hsecondNe
    have hlineEq : Subgroup.zpowers second = Subgroup.zpowers first :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hsameLine)
        (by rw [hfirstCard, hsecondCard])
    have hcentralizerEq : Subgroup.centralizer ({second} : Set G) =
        Subgroup.centralizer ({first} : Set G) := by
      rw [← Subgroup.centralizer_closure ({second} : Set G),
        ← Subgroup.centralizer_closure ({first} : Set G),
        ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, hlineEq]
    rw [hcentralizerEq, inf_eq_right.mpr (thetaCoreOf_le prime _)]
    exact thetaPlaneCommutator_le_element_theta prime hprime actor hab.1 first hfirst
  · let plane := Subgroup.zpowers second ⊔ Subgroup.zpowers first
    have hplaneLe : plane ≤ actor :=
      sup_le (Subgroup.zpowers_le_of_mem hsecond) (Subgroup.zpowers_le_of_mem hfirst)
    have hplaneCard : Nat.card plane = prime ^ 2 := by
      rw [show plane = Subgroup.zpowers first ⊔ Subgroup.zpowers second from sup_comm _ _]
      exact independent_elementary_pair_plane_card prime hprime actor hab first second
        hfirst hsecond hfirstNe hsameLine
    have hthetaLe := theta_element_centralizer_intersection_le prime hprime
      (Subgroup.centralizer ({second} : Set G)) first
    have hcentralizerEq : Subgroup.centralizer (plane : Set G) =
        Subgroup.centralizer ({second} : Set G) ⊓ Subgroup.centralizer ({first} : Set G) :=
      centralizer_join_zpowers second first
    rw [← hcentralizerEq] at hthetaLe
    exact (Subgroup.commutator_mono hthetaLe le_rfl).trans
      (hcondition plane hplaneLe hplaneCard second (Subgroup.mem_sup_left
        (Subgroup.mem_zpowers second)) hsecondNe)

theorem ThetaPlaneCondition.solvable_signalizer
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hcondition : ThetaPlaneCondition prime actor) :
    IsSolvableSignalizerFunctor prime actor (thetaActorSignalizer prime actor) := by
  apply thetaActorSignalizer_isSolvableSignalizerFunctor prime hprime actor hab.1
    (isElemAbelian_isPGroup prime actor hab)
  intro first hfirst hfirstNe second hsecond hsecondNe
  exact ThetaPlaneCondition.mixed_balance prime hprime actor hab hcondition first second
    hfirst hsecond hfirstNe hsecondNe

theorem CentralLineThetaCriterion.plane_condition
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3) (hcriterion : CentralLineThetaCriterion prime actor) :
    ThetaPlaneCondition prime actor := by
  exact thetaPlaneCondition_of_rank_three_local_planes prime hprime actor hab hactorCard
    (CentralLineThetaCriterion.raw_plane_containment prime hprime actor hab hactorCard hcriterion)

end CFSG.RankThreeEvenClassification.Helpers
