module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaMixedBalance
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSignalizer

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem card_join_of_commuting_disjoint {G : Type u} [Group G]
    (first second : Subgroup G)
    (hcommute : ∀ left ∈ first, ∀ right ∈ second, Commute left right)
    (hdisjoint : Disjoint first second) :
    Nat.card (first ⊔ second : Subgroup G) = Nat.card first * Nat.card second := by
  let productHom := first.subtype.noncommCoprod second.subtype
    (fun left right => hcommute left left.property right right.property)
  have hrange : productHom.range = first ⊔ second := by
    apply le_antisymm
    · rintro element ⟨⟨left, right⟩, rfl⟩
      exact Subgroup.mul_mem_sup left.property right.property
    · apply sup_le
      · intro element helement
        refine ⟨(⟨element, helement⟩, 1), ?_⟩
        change element * (1 : G) = element
        exact mul_one element
      · intro element helement
        refine ⟨(1, ⟨element, helement⟩), ?_⟩
        change (1 : G) * element = element
        exact one_mul element
  have hinjective : Function.Injective productHom := by
    apply (MonoidHom.ker_eq_bot_iff productHom).mp
    apply bot_unique
    rintro ⟨left, right⟩ hmem
    have heq : (left : G) * (right : G) = 1 := MonoidHom.mem_ker.mp hmem
    obtain ⟨hleft, hright⟩ := Subgroup.disjoint_iff_mul_eq_one.mp hdisjoint
      left.property right.property heq
    exact Subgroup.mem_bot.mpr (Prod.ext (Subtype.ext hleft) (Subtype.ext hright))
  have hrestrictionInjective : Function.Injective productHom.rangeRestrict := by
    intro firstPair secondPair heq
    exact hinjective (congrArg Subtype.val heq)
  have hcard := Nat.card_congr (MulEquiv.ofBijective productHom.rangeRestrict
    ⟨hrestrictionInjective, productHom.rangeRestrict_surjective⟩).toEquiv
  rw [hrange, Nat.card_prod] at hcard
  exact hcard.symm

theorem elementary_line_card {G : Type u} [Group G] (prime : ℕ) (hprime : prime.Prime)
    (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    Nat.card (Subgroup.zpowers element) = prime := by
  have : Fact prime.Prime := ⟨hprime⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (hab.2 element hmem) hne

theorem commuting_of_elementary_members {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (first second : G) (hfirst : first ∈ actor) (hsecond : second ∈ actor) :
    Commute first second := by
  exact congrArg (fun value : actor => (value : G))
    (isMulCommutative_iff.mp hab.1 ⟨first, hfirst⟩ ⟨second, hsecond⟩)

theorem independent_elementary_pair_plane_card {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (first second : G) (hfirst : first ∈ actor) (hsecond : second ∈ actor)
    (hfirstNe : first ≠ 1) (hsecondOutside : second ∉ Subgroup.zpowers first) :
    Nat.card (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup G) = prime ^ 2 := by
  have hsecondNe : second ≠ 1 := by
    intro heq
    exact hsecondOutside (heq ▸ (Subgroup.zpowers first).one_mem)
  have hfirstCard := elementary_line_card prime hprime actor hab first hfirst hfirstNe
  have hsecondCard := elementary_line_card prime hprime actor hab second hsecond hsecondNe
  have hdisjoint : Disjoint (Subgroup.zpowers first) (Subgroup.zpowers second) := by
    rcases prime_order_subgroup_le_or_disjoint prime hprime (Subgroup.zpowers first)
      (Subgroup.zpowers second) hsecondCard with hle | hdisjoint
    · exact False.elim (hsecondOutside (hle (Subgroup.mem_zpowers second)))
    · exact hdisjoint
  rw [card_join_of_commuting_disjoint _ _ (fun left hleft right hright =>
    commuting_of_elementary_members prime actor hab left right
      (Subgroup.zpowers_le_of_mem hfirst hleft) (Subgroup.zpowers_le_of_mem hsecond hright)) hdisjoint,
    hfirstCard, hsecondCard, pow_two]

theorem rank_three_actor_complementary_plane {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3) (first second : G)
    (hfirst : first ∈ actor) (hsecond : second ∈ actor) (hfirstNe : first ≠ 1)
    (hsecondOutside : second ∉ Subgroup.zpowers first) :
    ∃ plane : Subgroup G, plane ≤ actor ∧ first ∈ plane ∧ Nat.card plane = prime ^ 2 ∧
      actor = plane ⊔ Subgroup.zpowers second := by
  let pairPlane := Subgroup.zpowers first ⊔ Subgroup.zpowers second
  have hpairLe : pairPlane ≤ actor := sup_le (Subgroup.zpowers_le_of_mem hfirst)
    (Subgroup.zpowers_le_of_mem hsecond)
  have hpairCard : Nat.card pairPlane = prime ^ 2 :=
    independent_elementary_pair_plane_card prime hprime actor hab first second hfirst hsecond
      hfirstNe hsecondOutside
  have hpairNe : pairPlane ≠ actor := by
    intro heq
    have hcard := congrArg (fun subgroup : Subgroup G => Nat.card subgroup) heq
    rw [hpairCard, hactorCard] at hcard
    have hlarge : prime ^ 2 < prime ^ 3 := by
      have hpositive : 0 < prime ^ 2 := Nat.pow_pos hprime.pos
      nlinarith [hprime.two_le]
    omega
  obtain ⟨third, hthird, hthirdOutside⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hpairLe hpairNe)
  have hthirdOutsideFirst : third ∉ Subgroup.zpowers first :=
    fun hmem => hthirdOutside (Subgroup.mem_sup_left hmem)
  let plane := Subgroup.zpowers first ⊔ Subgroup.zpowers third
  have hplaneLe : plane ≤ actor := sup_le (Subgroup.zpowers_le_of_mem hfirst)
    (Subgroup.zpowers_le_of_mem hthird)
  have hplaneCard : Nat.card plane = prime ^ 2 :=
    independent_elementary_pair_plane_card prime hprime actor hab first third hfirst hthird
      hfirstNe hthirdOutsideFirst
  have hthirdNe : third ≠ 1 := fun heq => hthirdOutside (heq ▸ pairPlane.one_mem)
  have hthirdCard := elementary_line_card prime hprime actor hab third hthird hthirdNe
  have hdisjoint : Disjoint pairPlane (Subgroup.zpowers third) := by
    rcases prime_order_subgroup_le_or_disjoint prime hprime pairPlane (Subgroup.zpowers third)
      hthirdCard with hle | hdisjoint
    · exact False.elim (hthirdOutside (hle (Subgroup.mem_zpowers third)))
    · exact hdisjoint
  have hjoinCard : Nat.card (pairPlane ⊔ Subgroup.zpowers third : Subgroup G) = prime ^ 3 := by
    rw [card_join_of_commuting_disjoint _ _ (fun left hleft right hright =>
      commuting_of_elementary_members prime actor hab left right (hpairLe hleft)
        (Subgroup.zpowers_le_of_mem hthird hright)) hdisjoint, hpairCard, hthirdCard]
    ring
  have hjoinEq : pairPlane ⊔ Subgroup.zpowers third = actor :=
    Subgroup.eq_of_le_of_card_ge (sup_le hpairLe (Subgroup.zpowers_le_of_mem hthird))
      (by rw [hjoinCard, hactorCard])
  refine ⟨plane, hplaneLe, Subgroup.mem_sup_left (Subgroup.mem_zpowers first), hplaneCard, ?_⟩
  rw [← hjoinEq]
  change (Subgroup.zpowers first ⊔ Subgroup.zpowers second) ⊔ Subgroup.zpowers third =
    (Subgroup.zpowers first ⊔ Subgroup.zpowers third) ⊔ Subgroup.zpowers second
  exact sup_right_comm _ _ _

theorem theta_mixed_balance_of_rank_three_local_planes {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3)
    (hlocal : ∀ element ∈ actor, element ≠ 1 → ∀ plane : Subgroup G,
      plane ≤ actor → Nat.card plane = prime ^ 2 →
        thetaPlaneAlpha prime (plane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
          solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime)
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
  · obtain ⟨plane, hplaneLe, hfirstPlane, hplaneCard, hgenerate⟩ :=
      rank_three_actor_complementary_plane prime hprime actor hab hactorCard first second
        hfirst hsecond hfirstNe hsameLine
    let intersection := Subgroup.centralizer ({second} : Set G) ⊓
      thetaCoreOf prime (Subgroup.centralizer ({first} : Set G))
    have hlocalLe := theta_mixed_commutator_le_local_alpha prime hprime plane
      (Subgroup.centralizer ({second} : Set G))
      (hplaneLe.trans (commutative_plane_le_element_centralizer actor hab.1 second hsecond))
      first hfirstPlane hfirstNe
    have hlocalTheta := hlocal second hsecond hsecondNe plane hplaneLe hplaneCard
    have hcommutatorLe : ⁅intersection, plane⁆ ≤
        thetaCoreOf prime (Subgroup.centralizer ({second} : Set G)) :=
      hlocalLe.trans (Subgroup.map_mono
        (f := (Subgroup.centralizer ({second} : Set G)).subtype) hlocalTheta)
    have hlineCentralizes : Subgroup.zpowers second ≤ Subgroup.centralizer (intersection : Set G) := by
      apply Subgroup.zpowers_le.mpr
      apply Subgroup.mem_centralizer_iff.mpr
      intro element helement
      exact Subgroup.mem_centralizer_singleton_iff.mp helement.1
    have hlineNormalizes : Subgroup.zpowers second ≤ Subgroup.normalizer (plane : Set G) :=
      (Subgroup.zpowers_le_of_mem hsecond).trans
        (((Subgroup.le_centralizer_iff_isMulCommutative.mpr hab.1).trans
          (Subgroup.centralizer_le hplaneLe)).trans (Subgroup.centralizer_le_normalizer _))
    change ⁅intersection, actor⁆ ≤ _
    rw [hgenerate, Subgroup.commutator_comm intersection,
      normalized_sup_commutator_eq_of_fixed plane (Subgroup.zpowers second) intersection
        hlineNormalizes hlineCentralizes, Subgroup.commutator_comm]
    exact hcommutatorLe

theorem thetaActorSignalizer_of_rank_three_local_planes {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3)
    (hlocal : ∀ element ∈ actor, element ≠ 1 → ∀ plane : Subgroup G,
      plane ≤ actor → Nat.card plane = prime ^ 2 →
        thetaPlaneAlpha prime (plane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
          solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime) :
    CFSG.Open.IsSolvableSignalizerFunctor prime actor
      (thetaActorSignalizer prime actor) := by
  apply thetaActorSignalizer_isSolvableSignalizerFunctor prime hprime actor hab.1
    (isElemAbelian_isPGroup prime actor hab)
  intro first hfirst hfirstNe second hsecond hsecondNe
  exact theta_mixed_balance_of_rank_three_local_planes prime hprime actor hab hactorCard hlocal
    first second hfirst hsecond hfirstNe hsecondNe

end CFSG.RankThreeEvenClassification.Helpers
