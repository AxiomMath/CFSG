module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.UnipotentRank
public import CFSG.LocalAnalysis.PreuniquenessRankFour.PrimeCritical
public import CFSG.LocalAnalysis.PreuniquenessRankFour.NormalChain

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem class_two_product_power
    {source : Type u} [Group source]
    (hcommutator : commutator source ≤ Subgroup.center source)
    (first second : source) (exponent : ℕ) :
    (first * second) ^ exponent =
      first ^ exponent * second ^ exponent * ⁅second, first⁆ ^ (exponent.choose 2) := by
  have hcentral : ⁅second, first⁆ ∈ Subgroup.center source :=
    hcommutator (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top second) (Subgroup.mem_top first))
  have hcommute : ∀ member : source, Commute ⁅second, first⁆ member := by
    intro member
    exact (Subgroup.mem_center_iff.mp hcentral member).symm
  induction exponent with
  | zero => simp
  | succ exponent hinduction =>
    have hswap : second ^ exponent * first =
        first * second ^ exponent * ⁅second, first⁆ ^ exponent := by
      have hequal := class_two_commutator_pow_left hcommutator second first exponent
      have hraw : second ^ exponent * first = ⁅second, first⁆ ^ exponent * first * second ^ exponent := by
        rw [← hequal]
        simp only [commutatorElement_def]
        group
      rw [hraw, (hcommute first).pow_left exponent]
      rw [mul_assoc, (hcommute (second ^ exponent)).pow_left exponent, ← mul_assoc]
    have hmove : ⁅second, first⁆ ^ (exponent.choose 2) * (first * second) =
        (first * second) * ⁅second, first⁆ ^ (exponent.choose 2) :=
      ((hcommute (first * second)).pow_left _).eq
    rw [pow_succ, hinduction, mul_assoc, hmove]
    calc
      _ =
          first ^ exponent * (second ^ exponent * first) * second *
            ⁅second, first⁆ ^ (exponent.choose 2) := by simp only [mul_assoc]
      _ = first ^ exponent * first * second ^ exponent *
          (⁅second, first⁆ ^ exponent * second) * ⁅second, first⁆ ^ (exponent.choose 2) := by
        rw [hswap]
        simp only [mul_assoc]
      _ = first ^ (exponent + 1) * second ^ (exponent + 1) *
          ⁅second, first⁆ ^ (exponent + exponent.choose 2) := by
        rw [((hcommute second).pow_left exponent).eq]
        simp only [pow_succ, mul_assoc]
        rw [← pow_add]
      _ = _ := by rw [Nat.choose_succ_succ, Nat.choose_one_right]

theorem odd_prime_class_two_product_prime_power_eq_one
    {source : Type u} [Group source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hcommutator : commutator source ≤ Subgroup.center source)
    (first second : source) (hfirst : first ^ prime = 1) (hsecond : second ^ prime = 1) :
    (first * second) ^ prime = 1 := by
  have hlarge : 2 < prime := by
    have hlower := (Fact.out : prime.Prime).two_le
    omega
  obtain ⟨correction, hcorrection⟩ := (Fact.out : prime.Prime).dvd_choose_self (by omega) hlarge
  have hcommutatorPower : ⁅second, first⁆ ^ prime = 1 := by
    rw [← class_two_commutator_pow_left hcommutator, hsecond]
    simp
  rw [class_two_product_power hcommutator, hfirst, hsecond, hcorrection,
    pow_mul, hcommutatorPower, one_pow, one_mul, one_mul]

theorem normal_prime_subgroup_is_central
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hcard : Nat.card normal = prime) :
    normal ≤ Subgroup.center source := by
  have hnontrivial : normal ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Fact.out : prime.Prime).ne_one hcard.symm
  obtain ⟨line, hline, hcentral, hlineCard, _⟩ :=
    normal_pSubgroup_has_central_prime_line prime hsource normal hnontrivial
  have hequal : line = normal := Subgroup.eq_of_le_of_card_ge hline (by omega)
  exact hequal ▸ hcentral

theorem normal_rank_two_with_central_line_has_central_quotient_image
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (normal line : Subgroup source) [normal.Normal] [line.Normal]
    (hline : line ≤ normal) (hnormalCard : Nat.card normal = prime ^ 2)
    (hlineCard : Nat.card line = prime) :
    normal.map (QuotientGroup.mk' line) ≤ Subgroup.center (source ⧸ line) := by
  let image := normal.map (QuotientGroup.mk' line)
  let : image.Normal := Subgroup.Normal.map (inferInstance : normal.Normal)
    (QuotientGroup.mk' line) (QuotientGroup.mk'_surjective line)
  have himageCard : Nat.card image = prime := by
    have hpreimage : image.comap (QuotientGroup.mk' line) = normal := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hline]
    have hcard := surjective_hom_preimage_card
      (QuotientGroup.mk' line) (QuotientGroup.mk'_surjective line) image
    rw [hpreimage, QuotientGroup.ker_mk', hlineCard, hnormalCard, pow_two] at hcard
    exact Nat.mul_right_cancel (Fact.out : prime.Prime).pos hcard.symm
  exact normal_prime_subgroup_is_central prime (hsource.to_quotient line) image himageCard

theorem nonnormal_maximal_elementary_rank_two_normal_rank_two_contains_central_line
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (elementary : Subgroup source) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup source, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary)
    (hnonnormal : ¬ elementary.Normal)
    (normal : Subgroup source) [normal.Normal] (hnormalCard : Nat.card normal = prime ^ 2) :
    centralPrimeTorsion prime source ≤ normal := by
  obtain ⟨_, hlineCard⟩ := nonnormal_maximal_elementary_rank_two_has_central_prime_line
    prime hsource elementary helementary hcard hmaximal hnonnormal
  have hnontrivial : normal ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hnormalCard
    have hlarge : 1 < prime ^ 2 := one_lt_pow₀ (Fact.out : prime.Prime).one_lt (by omega)
    omega
  have hintersection := pGroup_normal_subgroup_meets_centralPrimeTorsion
    prime hsource normal hnontrivial
  have hdivides : Nat.card (normal ⊓ centralPrimeTorsion prime source : Subgroup source) ∣ prime :=
    (Subgroup.card_dvd_of_le
      (inf_le_right : normal ⊓ centralPrimeTorsion prime source ≤ centralPrimeTorsion prime source)).trans
        (dvd_of_eq hlineCard)
  have hintersectionCard : Nat.card (normal ⊓ centralPrimeTorsion prime source : Subgroup source) = prime :=
    ((Fact.out : prime.Prime).eq_one_or_self_of_dvd _ hdivides).resolve_left
      (fun hone => hintersection (Subgroup.card_eq_one.mp hone))
  have hequal : normal ⊓ centralPrimeTorsion prime source = centralPrimeTorsion prime source :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
  exact hequal ▸ (show normal ⊓ centralPrimeTorsion prime source ≤ normal from inf_le_left)

theorem class_two_elementary_fixed_subgroup_bound
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (normalized line : Subgroup source) [line.Normal]
    (hlineCard : Nat.card line = prime)
    (hcommutator : ⁅(⊤ : Subgroup source), normalized⁆ ≤ line)
    (scalar : source) :
    Nat.card normalized ≤
      Nat.card (normalized ⊓ Subgroup.centralizer ({scalar} : Set source) : Subgroup source) * prime := by
  have hlineCentral : ∀ member ∈ line, ∀ other : normalized, member * (other : source) =
      (other : source) * member := by
    intro member hmember other
    exact (Subgroup.mem_center_iff.mp
      (normal_prime_subgroup_is_central prime hsource line hlineCard hmember) other).symm
  let displacement : normalized →* source :=
    { toFun := fun member => ⁅scalar, (member : source)⁆
      map_one' := commutatorElement_one_right scalar
      map_mul' := fun first second => by
        have hcorrection := hcommutator (Subgroup.commutator_mem_commutator
          (Subgroup.mem_top scalar) second.property)
        have hconjugate : (first : source) * ⁅scalar, (second : source)⁆ * (first : source)⁻¹ =
            ⁅scalar, (second : source)⁆ := by
          rw [← hlineCentral _ hcorrection first, mul_inv_cancel_right]
        change ⁅scalar, (first : source) * (second : source)⁆ = _
        rw [commutatorElement_mul_right_eq_mul_conj]
        simpa only [mul_assoc] using congrArg
          (fun value : source => ⁅scalar, (first : source)⁆ * value) hconjugate }
  have hrange : displacement.range ≤ line := by
    rintro member ⟨lift, rfl⟩
    exact hcommutator (Subgroup.commutator_mem_commutator (Subgroup.mem_top scalar) lift.property)
  have hkernel : displacement.ker.map normalized.subtype =
      normalized ⊓ Subgroup.centralizer ({scalar} : Set source) := by
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      refine ⟨lift.property, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro other hother
      have hequal : other = scalar := Set.mem_singleton_iff.mp hother
      rw [hequal]
      exact commutatorElement_eq_one_iff_mul_comm.mp hlift
    · intro hmember
      refine ⟨⟨member, hmember.1⟩, ?_, rfl⟩
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hmember.2 scalar (Set.mem_singleton scalar))
  have hkernelCard : Nat.card displacement.ker =
      Nat.card (normalized ⊓ Subgroup.centralizer ({scalar} : Set source) : Subgroup source) := by
    rw [← hkernel, Subgroup.card_map_of_injective Subtype.val_injective]
  have hsourceCard : Nat.card normalized = Nat.card displacement.ker * Nat.card displacement.range := by
    rw [displacement.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange displacement).toEquiv]
    exact Nat.mul_comm _ _
  rw [hsourceCard, hkernelCard]
  exact Nat.mul_le_mul_left _ (hlineCard ▸ Subgroup.card_le_of_le hrange)

theorem nonnormal_maximal_elementary_rank_two_normal_rank_two_unique
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (elementary : Subgroup source) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup source, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary)
    (hnonnormal : ¬ elementary.Normal)
    (first second : Subgroup source) [first.Normal] [second.Normal]
    (hfirst : IsElemAbelian prime first) (hsecond : IsElemAbelian prime second)
    (hfirstCard : Nat.card first = prime ^ 2) (hsecondCard : Nat.card second = prime ^ 2) :
    first = second := by
  let line := centralPrimeTorsion prime source
  let : line.Characteristic := centralPrimeTorsion_characteristic prime
  obtain ⟨hlineElementary, hlineCard⟩ := nonnormal_maximal_elementary_rank_two_has_central_prime_line
    prime hsource elementary helementary hcard hmaximal hnonnormal
  have hlineFirst : line ≤ first :=
    nonnormal_maximal_elementary_rank_two_normal_rank_two_contains_central_line
      prime hsource elementary helementary hcard hmaximal hnonnormal first hfirstCard
  have hlineSecond : line ≤ second :=
    nonnormal_maximal_elementary_rank_two_normal_rank_two_contains_central_line
      prime hsource elementary helementary hcard hmaximal hnonnormal second hsecondCard
  let joined := first ⊔ second
  have hjoinedCommutator : ⁅(⊤ : Subgroup source), joined⁆ ≤ line := by
    apply subgroup_commutator_le_of_quotient_map_le_center
    rw [Subgroup.map_sup]
    exact sup_le
      (normal_rank_two_with_central_line_has_central_quotient_image
        prime hsource first line hlineFirst hfirstCard hlineCard)
      (normal_rank_two_with_central_line_has_central_quotient_image
        prime hsource second line hlineSecond hsecondCard hlineCard)
  have hlineCentral : line ≤ Subgroup.center source := by
    intro member hmember
    exact ((mem_centralPrimeTorsion prime member).mp hmember).1
  have hjoinedClassTwo : commutator joined ≤ Subgroup.center joined := by
    apply Subgroup.commutator_le.mpr
    intro firstMember _ secondMember _
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    have hcentral := hlineCentral (hjoinedCommutator
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top (firstMember : source))
        secondMember.property))
    exact Subgroup.mem_center_iff.mp hcentral (other : source)
  have hjoinedExponent : ∀ member ∈ joined, member ^ prime = 1 := by
    intro member hmember
    obtain ⟨firstLift, hfirstLift, secondLift, hsecondLift, hequal⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hmember
    let firstJoined : joined := ⟨firstLift, (le_sup_left : first ≤ joined) hfirstLift⟩
    let secondJoined : joined := ⟨secondLift, (le_sup_right : second ≤ joined) hsecondLift⟩
    have hfirstPower : firstJoined ^ prime = 1 :=
      Subtype.ext (hfirst.2 firstLift hfirstLift)
    have hsecondPower : secondJoined ^ prime = 1 :=
      Subtype.ext (hsecond.2 secondLift hsecondLift)
    have hpower := odd_prime_class_two_product_prime_power_eq_one
      prime hodd hjoinedClassTwo firstJoined secondJoined hfirstPower hsecondPower
    have hvalues := congrArg (fun value : joined => (value : source)) hpower
    change (firstLift * secondLift) ^ prime = 1 at hvalues
    exact hequal ▸ hvalues
  have hnotContained : ¬ elementary ≤ joined := by
    intro hcontained
    apply hnonnormal
    refine ⟨?_⟩
    intro member hmember scalar
    have hcorrection := hjoinedCommutator (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top scalar) (hcontained hmember))
    have hproduct : scalar * member * scalar⁻¹ = ⁅scalar, member⁆ * member := by
      simp only [commutatorElement_def]
      group
    rw [hproduct]
    exact elementary.mul_mem (hlineElementary hcorrection) hmember
  obtain ⟨scalar, hscalar, hgeneration⟩ := rank_two_elementary_central_line_has_complement_generator
    prime helementary hcard hlineElementary hlineCard
  let fixed := joined ⊓ Subgroup.centralizer ({scalar} : Set source)
  have hfixedContained : fixed ≤ joined ⊓ elementary := by
    intro member hmember
    refine ⟨hmember.1, ?_⟩
    apply elementary_rank_two_maximal_centralizer_is_self prime helementary le_top
      (fun extension hextension _ hextensionElementary => hmaximal extension hextension hextensionElementary)
      member (Subgroup.mem_top member) (hjoinedExponent member hmember.1)
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    have hcentralized : elementary ≤ Subgroup.centralizer ({member} : Set source) := by
      rw [hgeneration]
      apply sup_le
      · intro centralMember hcentralMember
        apply Subgroup.mem_centralizer_iff.mpr
        intro value hvalue
        rw [Set.mem_singleton_iff.mp hvalue]
        exact Subgroup.mem_center_iff.mp (hlineCentral hcentralMember) member
      · apply Subgroup.zpowers_le.mpr
        apply Subgroup.mem_centralizer_iff.mpr
        intro value hvalue
        rw [Set.mem_singleton_iff.mp hvalue]
        exact (Subgroup.mem_centralizer_iff.mp hmember.2 scalar (Set.mem_singleton scalar)).symm
    exact (Subgroup.mem_centralizer_iff.mp (hcentralized hother) member (Set.mem_singleton member)).symm
  have hintersectionSmall : Nat.card (joined ⊓ elementary : Subgroup source) < prime ^ 2 := by
    by_contra hnotSmall
    have hequal : joined ⊓ elementary = elementary :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    exact hnotContained (hequal ▸ (show joined ⊓ elementary ≤ joined from inf_le_left))
  obtain ⟨intersectionRank, hintersectionCard⟩ :=
    (hsource.to_subgroup (joined ⊓ elementary)).exists_card_eq
  have hintersectionRank : intersectionRank ≤ 1 := by
    have hbound : prime ^ intersectionRank < prime ^ 2 := by omega
    have hrank := (Nat.pow_lt_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hbound
    omega
  have hfixedCard : Nat.card fixed ≤ prime := by
    apply (Subgroup.card_le_of_le hfixedContained).trans
    rw [hintersectionCard]
    simpa only [pow_one] using Nat.pow_le_pow_right (Fact.out : prime.Prime).pos hintersectionRank
  have hjoinedBound : Nat.card joined ≤ prime ^ 2 := by
    have hbound := class_two_elementary_fixed_subgroup_bound
      prime hsource joined line hlineCard hjoinedCommutator scalar
    exact hbound.trans (by simpa only [pow_two] using Nat.mul_le_mul_right prime hfixedCard)
  have hjoinedFirst : first = joined := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  exact (Subgroup.eq_of_le_of_card_ge (hjoinedFirst ▸ (le_sup_right : second ≤ joined))
    (by omega)).symm

theorem nonnormal_maximal_elementary_rank_two_existing_normal_is_characteristic
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (elementary : Subgroup source) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup source, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary)
    (hnonnormal : ¬ elementary.Normal)
    (normal : Subgroup source) [normal.Normal]
    (hnormal : IsElemAbelian prime normal) (hnormalCard : Nat.card normal = prime ^ 2) :
    normal.Characteristic := by
  apply Subgroup.characteristic_iff_le_map.mpr
  intro automorphism
  let image := normal.map automorphism.toMonoidHom
  let : image.Normal := Subgroup.Normal.map (inferInstance : normal.Normal)
    automorphism.toMonoidHom automorphism.surjective
  have hequal : normal = image :=
    nonnormal_maximal_elementary_rank_two_normal_rank_two_unique
      prime hodd hsource elementary helementary hcard hmaximal hnonnormal normal image
        hnormal (elementary_abelian_map prime hnormal automorphism.toMonoidHom) hnormalCard
          (by rw [Subgroup.card_map_of_injective automorphism.injective]; exact hnormalCard)
  exact hequal.le

theorem normal_elementary_contains_ambient_normal_elementary_of_each_rank
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hnormal : IsElemAbelian prime normal)
    (rank : ℕ) (hcard : Nat.card normal = prime ^ rank) (width : ℕ) (hwidth : width ≤ rank) :
    ∃ elementary : Subgroup source, elementary ≤ normal ∧ elementary.Normal ∧
      IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ width := by
  obtain ⟨elementary, hcontained, helementaryNormal, helementaryCard⟩ :=
    normal_pSubgroup_has_ambient_normal_subgroup_of_each_order
      prime rank hsource normal (inferInstance : normal.Normal) hcard width hwidth
  have helementary : IsElemAbelian prime elementary := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro first second
      apply Subtype.ext
      let : IsMulCommutative normal := hnormal.1
      let : CommGroup normal := IsMulCommutative.instCommGroup
      exact congrArg (fun member : normal => (member : source))
        (mul_comm (⟨first, hcontained first.property⟩ : normal)
          (⟨second, hcontained second.property⟩ : normal))
    · intro member hmember
      exact hnormal.2 member (hcontained hmember)
  exact ⟨elementary, hcontained, helementaryNormal, helementary, helementaryCard⟩

theorem nonnormal_maximal_elementary_rank_two_has_characteristic_if_normal_elementary_exists
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (elementary : Subgroup source) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup source, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary)
    (hnonnormal : ¬ elementary.Normal)
    (normal : Subgroup source) [normal.Normal]
    (hnormal : IsElemAbelian prime normal) (hnormalRank : 2 ≤ pRank prime normal) :
    ∃ characteristic : Subgroup source, characteristic.Characteristic ∧
      IsElemAbelian prime characteristic ∧ Nat.card characteristic = prime ^ 2 := by
  obtain ⟨rank, hnormalCard⟩ := (hsource.to_subgroup normal).exists_card_eq
  have hnormalRankBound : pRank prime normal ≤ rank := by
    obtain ⟨witness, hcontained, _, hwitnessCard⟩ :=
      pRank_attained prime (Fact.out : prime.Prime) normal
    apply (Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp
    rw [← hwitnessCard, ← hnormalCard]
    exact Subgroup.card_le_of_le hcontained
  obtain ⟨small, _, hsmallNormal, hsmallElementary, hsmallCard⟩ :=
    normal_elementary_contains_ambient_normal_elementary_of_each_rank
      prime hsource normal hnormal rank hnormalCard 2 (hnormalRank.trans hnormalRankBound)
  let : small.Normal := hsmallNormal
  exact ⟨small, nonnormal_maximal_elementary_rank_two_existing_normal_is_characteristic
    prime hodd hsource elementary helementary hcard hmaximal hnonnormal
      small hsmallElementary hsmallCard, hsmallElementary, hsmallCard⟩

theorem no_normal_elementary_rank_two_forces_normal_abelian_cyclic
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (hnormalElementary : ∀ elementary : Subgroup source, elementary.Normal →
      IsElemAbelian prime elementary → Nat.card elementary ≠ prime ^ 2)
    (abelian : Subgroup source) [abelian.Normal] (habelian : IsMulCommutative abelian) :
    IsCyclic abelian := by
  by_contra hnoncyclic
  let : IsMulCommutative abelian := habelian
  let : CommGroup abelian := IsMulCommutative.instCommGroup
  let torsion := centralPrimeTorsion prime abelian
  let : torsion.Characteristic := centralPrimeTorsion_characteristic prime
  let image := torsion.map abelian.subtype
  let : image.Normal := inferInstance
  have himageElementary := elementary_abelian_map prime (centralPrimeTorsion_elementary prime) abelian.subtype
  have hlarge : 2 ≤ pRank prime image := by
    rw [pRank_map_of_injective prime (Fact.out : prime.Prime) abelian.subtype Subtype.val_injective,
      centralPrimeTorsion_rank_eq_center_rank prime (Fact.out : prime.Prime), Subgroup.center_eq_top]
    exact noncyclic_commutative_pGroup_rank_at_least_two
      prime (Fact.out : prime.Prime) (hsource.to_subgroup abelian) hnoncyclic
  obtain ⟨rank, himageCard⟩ := (hsource.to_subgroup image).exists_card_eq
  have hrank : 2 ≤ rank := by
    obtain ⟨witness, hcontained, _, hwitnessCard⟩ :=
      pRank_attained prime (Fact.out : prime.Prime) image
    have hcardBound := Subgroup.card_le_of_le hcontained
    rw [hwitnessCard, himageCard] at hcardBound
    exact hlarge.trans ((Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hcardBound)
  obtain ⟨small, _, hsmallNormal, hsmallElementary, hsmallCard⟩ :=
    normal_elementary_contains_ambient_normal_elementary_of_each_rank
      prime hsource image himageElementary rank himageCard 2 hrank
  exact hnormalElementary small hsmallNormal hsmallElementary hsmallCard

theorem odd_prime_class_two_power_monoidHom
    {source : Type u} [Group source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hpowers : ∀ member : source, member ^ prime ∈ Subgroup.center source) :
    ∃ hom : source →* source, ∀ member : source, hom member = member ^ prime := by
  refine ⟨{ toFun := fun member => member ^ prime, map_one' := one_pow _, map_mul' := ?_ }, fun _ => rfl⟩
  intro first second
  have hlarge : 2 < prime := by
    have hlower := (Fact.out : prime.Prime).two_le
    omega
  obtain ⟨correction, hcorrection⟩ := (Fact.out : prime.Prime).dvd_choose_self (by omega) hlarge
  have hcommutatorPower := commutator_pow_prime_eq_one_of_powers_central
    prime hcommutator hpowers second first
  rw [class_two_product_power hcommutator, hcorrection, pow_mul,
    hcommutatorPower, one_pow, mul_one]

theorem power_monoidHom_kernel_characteristic
    {source : Type u} [Group source] (exponent : ℕ) (hom : source →* source)
    (hhom : ∀ member : source, hom member = member ^ exponent) : hom.ker.Characteristic := by
  apply Subgroup.characteristic_iff_comap_eq.mpr
  intro automorphism
  ext member
  simp only [Subgroup.mem_comap, MonoidHom.mem_ker, hhom, ← map_pow]
  exact automorphism.map_eq_one_iff

theorem normal_prime_cube_elementary_central_extension_has_normal_elementary_rank_two
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (normal line : Subgroup source) [normal.Normal] [line.Normal]
    (hnormalCard : Nat.card normal = prime ^ 3) (hlineCard : Nat.card line = prime)
    (hcommutator : ⁅normal, normal⁆ ≤ line)
    (hpowers : ∀ member ∈ normal, member ^ prime ∈ line) :
    ∃ elementary : Subgroup source, elementary ≤ normal ∧ elementary.Normal ∧
      IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 := by
  have hlineCentral := normal_prime_subgroup_is_central prime hsource line hlineCard
  have hclassTwo : commutator normal ≤ Subgroup.center normal := by
    apply Subgroup.commutator_le.mpr
    intro first _ second _
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (hlineCentral (hcommutator (Subgroup.commutator_mem_commutator
        first.property second.property))) (other : source)
  have hpowersLocal : ∀ member : normal, member ^ prime ∈ Subgroup.center normal := by
    intro member
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hlineCentral (hpowers member member.property)) (other : source)
  obtain ⟨hom, hhom⟩ := odd_prime_class_two_power_monoidHom prime hodd hclassTwo hpowersLocal
  let : hom.ker.Characteristic := power_monoidHom_kernel_characteristic prime hom hhom
  let image := hom.ker.map normal.subtype
  let : image.Normal := inferInstance
  have hrange : hom.range.map normal.subtype ≤ line := by
    rintro member ⟨lift, ⟨preimage, hpreimage⟩, rfl⟩
    rw [← hpreimage, hhom]
    exact hpowers preimage preimage.property
  have hrangeCard : Nat.card hom.range ≤ prime := by
    have hbound := Subgroup.card_le_of_le hrange
    rwa [Subgroup.card_map_of_injective Subtype.val_injective, hlineCard] at hbound
  obtain ⟨kernelRank, hkernelCard⟩ := ((hsource.to_subgroup normal).to_subgroup hom.ker).exists_card_eq
  have hkernelRank : 2 ≤ kernelRank := by
    have hsourceCard : Nat.card normal = Nat.card hom.range * Nat.card hom.ker := by
      rw [hom.ker.card_eq_card_quotient_mul_card_subgroup,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange hom).toEquiv]
    have hbound : prime ^ 3 ≤ prime * prime ^ kernelRank := by
      rw [← hnormalCard, hsourceCard, ← hkernelCard]
      exact Nat.mul_le_mul_right _ hrangeCard
    rw [← pow_succ'] at hbound
    have hrankBound := (Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hbound
    omega
  have himageCard : Nat.card image = prime ^ kernelRank := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hkernelCard]
  obtain ⟨elementary, hcontained, helementaryNormal, helementaryCard⟩ :=
    normal_pSubgroup_has_ambient_normal_subgroup_of_each_order
      prime kernelRank hsource image (inferInstance : image.Normal) himageCard 2 hkernelRank
  refine ⟨elementary, hcontained.trans (Subgroup.map_subtype_le _), helementaryNormal,
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq helementaryCard, ?_⟩, helementaryCard⟩
  intro member hmember
  obtain ⟨lift, hlift, rfl⟩ := hcontained hmember
  have hpower : lift ^ prime = 1 := (hhom lift).symm.trans hlift
  exact congrArg (fun value : normal => (value : source)) hpower

theorem odd_pGroup_noncyclic_has_normal_elementary_rank_two
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (cardinality : ℕ) :
    ∀ {source : Type u} [Group source] [Finite source], Nat.card source = cardinality →
      IsPGroup prime source → ¬ IsCyclic source →
        ∃ elementary : Subgroup source, elementary.Normal ∧
          IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 := by
  induction cardinality using Nat.strong_induction_on with
  | h cardinality hinduction =>
    intro source _ _ hcardinality hsource hnoncyclic
    classical
    by_contra hnone
    have hnoNormal : ∀ elementary : Subgroup source, elementary.Normal →
        IsElemAbelian prime elementary → Nat.card elementary ≠ prime ^ 2 := by
      intro elementary hnormal helementary hcard
      exact hnone ⟨elementary, hnormal, helementary, hcard⟩
    let : Nontrivial source := not_subsingleton_iff_nontrivial.mp (by
      intro htrivial
      let : Subsingleton source := htrivial
      exact hnoncyclic inferInstance)
    obtain ⟨line, _, hlineCentral, hlineCard, hlineNormal⟩ :=
      normal_pSubgroup_has_central_prime_line prime hsource (⊤ : Subgroup source) top_ne_bot
    let : line.Normal := hlineNormal
    let quotientMap := QuotientGroup.mk' line
    have hquotientSmall : Nat.card (source ⧸ line) < cardinality := by
      have hproduct := line.card_eq_card_quotient_mul_card_subgroup
      rw [hlineCard, hcardinality] at hproduct
      have hpositive : 0 < Nat.card (source ⧸ line) := Nat.card_pos
      have hprime := (Fact.out : prime.Prime).one_lt
      nlinarith
    by_cases hquotientCyclic : IsCyclic (source ⧸ line)
    · let : IsCyclic (source ⧸ line) := hquotientCyclic
      let : IsMulCommutative source := quotientMap.isMulCommutative_of_isCyclic_of_ker_le_center
        (by rw [QuotientGroup.ker_mk']; exact hlineCentral)
      let : IsCyclic (⊤ : Subgroup source) := no_normal_elementary_rank_two_forces_normal_abelian_cyclic
        prime hsource hnoNormal (⊤ : Subgroup source) inferInstance
      exact hnoncyclic (isCyclic_of_surjective (⊤ : Subgroup source).subtype (by
        intro member
        exact ⟨⟨member, Subgroup.mem_top member⟩, rfl⟩))
    · obtain ⟨quotientElementary, hquotientNormal, hquotientElementary, hquotientCard⟩ :=
        hinduction _ hquotientSmall rfl (hsource.to_quotient line) hquotientCyclic
      let : quotientElementary.Normal := hquotientNormal
      let preimage := quotientElementary.comap quotientMap
      let : preimage.Normal := inferInstance
      have hpreimageCard : Nat.card preimage = prime ^ 3 := by
        rw [surjective_hom_preimage_card quotientMap (QuotientGroup.mk'_surjective line),
          QuotientGroup.ker_mk', hlineCard, hquotientCard]
        simp only [pow_succ]
      have hcommutatorImage : ⁅preimage, preimage⁆ ≤ line := by
        apply Subgroup.commutator_le.mpr
        intro first hfirst second hsecond
        apply (QuotientGroup.eq_one_iff _).mp
        change quotientMap ⁅first, second⁆ = 1
        rw [map_commutatorElement]
        apply commutatorElement_eq_one_iff_mul_comm.mpr
        let : IsMulCommutative quotientElementary := hquotientElementary.1
        let : CommGroup quotientElementary := IsMulCommutative.instCommGroup
        exact congrArg (fun value : quotientElementary => (value : source ⧸ line))
          (mul_comm (⟨quotientMap first, hfirst⟩ : quotientElementary)
            (⟨quotientMap second, hsecond⟩ : quotientElementary))
      obtain ⟨elementary, _, helementaryNormal, helementary, helementaryCard⟩ :=
        normal_prime_cube_elementary_central_extension_has_normal_elementary_rank_two
          prime hodd hsource preimage line hpreimageCard hlineCard hcommutatorImage (by
            intro member hmember
            apply (QuotientGroup.eq_one_iff _).mp
            change quotientMap (member ^ prime) = 1
            rw [map_pow]
            exact hquotientElementary.2 _ hmember)
      exact hnoNormal elementary helementaryNormal helementary helementaryCard

theorem odd_pGroup_rank_two_has_normal_elementary_rank_two
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (hrank : 2 ≤ pRank prime (⊤ : Subgroup source)) :
    ∃ elementary : Subgroup source, elementary.Normal ∧
      IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 := by
  apply odd_pGroup_noncyclic_has_normal_elementary_rank_two prime hodd (Nat.card source) rfl hsource
  intro hcyclic
  let : IsCyclic source := hcyclic
  obtain ⟨elementary, _, helementary, hcard⟩ :=
    pRank_attained prime (Fact.out : prime.Prime) (⊤ : Subgroup source)
  have hsmall := cyclic_group_of_prime_exponent_card_eq_one_or_prime prime
    (fun member : elementary => Subtype.ext (helementary.2 member member.property))
  have hcardBound : Nat.card elementary ≤ prime := by
    rcases hsmall with hone | hprime
    · rw [hone]
      exact (Fact.out : prime.Prime).one_le
    · rw [hprime]
  rw [hcard] at hcardBound
  have hsmallRank := (Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp
    (show prime ^ pRank prime (⊤ : Subgroup source) ≤ prime ^ 1 from by simpa using hcardBound)
  omega

theorem odd_pGroup_nonnormal_maximal_elementary_rank_two_has_characteristic_rank_two
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hsource : IsPGroup prime source)
    (elementary : Subgroup source) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup source, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary)
    (hnonnormal : ¬ elementary.Normal) :
    ∃ characteristic : Subgroup source, characteristic.Characteristic ∧
      IsElemAbelian prime characteristic ∧ Nat.card characteristic = prime ^ 2 ∧
        ∀ normal : Subgroup source, normal.Normal → IsElemAbelian prime normal →
          Nat.card normal = prime ^ 2 → normal = characteristic := by
  have hrank : 2 ≤ pRank prime (⊤ : Subgroup source) :=
    le_csSup (pRank_bddAbove prime (Fact.out : prime.Prime) _)
      ⟨elementary, le_top, helementary, hcard⟩
  obtain ⟨normal, hnormal, hnormalElementary, hnormalCard⟩ :=
    odd_pGroup_rank_two_has_normal_elementary_rank_two prime hodd hsource hrank
  let : normal.Normal := hnormal
  refine ⟨normal, nonnormal_maximal_elementary_rank_two_existing_normal_is_characteristic
    prime hodd hsource elementary helementary hcard hmaximal hnonnormal
      normal hnormalElementary hnormalCard, hnormalElementary, hnormalCard, ?_⟩
  intro other hotherNormal hotherElementary hotherCard
  let : other.Normal := hotherNormal
  exact nonnormal_maximal_elementary_rank_two_normal_rank_two_unique
    prime hodd hsource elementary helementary hcard hmaximal hnonnormal
      other normal hotherElementary hnormalElementary hotherCard hnormalCard

theorem escaping_maximal_elementary_rank_two_sylow_has_characteristic_rank_two
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) (sylow : Sylow prime ambient)
    {overgroup elementary : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hsylowRank : 3 ≤ pRank prime (sylow : Subgroup ambient))
    (helementary : IsElemAbelian prime elementary) (hcard : Nat.card elementary = prime ^ 2)
    (hcontained : elementary ≤ sylow)
    (hmaximal : ∀ extension : Subgroup ambient, elementary ≤ extension → extension ≤ sylow →
      IsElemAbelian prime extension → extension = elementary)
    (hescape : ¬ Subgroup.normalizer (elementary : Set ambient) ≤ overgroup) :
    ∃ characteristic : Subgroup (sylow : Subgroup ambient), characteristic.Characteristic ∧
      IsElemAbelian prime characteristic ∧ Nat.card characteristic = prime ^ 2 ∧
        Subgroup.normalizer (characteristic.map (sylow : Subgroup ambient).subtype : Set ambient) ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsMulCommutative elementary := helementary.1
  let localElementary := elementary.subgroupOf (sylow : Subgroup ambient)
  have hlocalElementary : IsElemAbelian prime localElementary := by
    refine ⟨Subgroup.comap_injective_isMulCommutative elementary Subtype.val_injective, ?_⟩
    intro member hmember
    exact Subtype.ext (helementary.2 member hmember)
  have hlocalCard : Nat.card localElementary = prime ^ 2 :=
    (Nat.card_congr (elementary.subgroupOfEquivOfLe hcontained).toEquiv).trans hcard
  have hlocalMaximal : ∀ extension : Subgroup (sylow : Subgroup ambient),
      localElementary ≤ extension → IsElemAbelian prime extension → extension = localElementary := by
    intro extension hextends hextension
    have hequal := hmaximal (extension.map (sylow : Subgroup ambient).subtype)
      (by
        rw [← Subgroup.map_subgroupOf_eq_of_le hcontained]
        exact Subgroup.map_mono hextends)
      (Subgroup.map_subtype_le extension)
      (elementary_abelian_map prime hextension (sylow : Subgroup ambient).subtype)
    apply Subgroup.map_injective (f := (sylow : Subgroup ambient).subtype) Subtype.val_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hcontained]
    exact hequal
  have hnonnormal := escaping_elementary_rank_two_not_normal_in_containing_sylow prime hprime
    sylow hsylow hcore hsylowRank helementary hcard hcontained hescape
  obtain ⟨characteristic, hcharacteristic, hcharacteristicElementary, hcharacteristicCard, _⟩ :=
    odd_pGroup_nonnormal_maximal_elementary_rank_two_has_characteristic_rank_two
      prime hodd sylow.isPGroup' localElementary hlocalElementary hlocalCard hlocalMaximal hnonnormal
  let : characteristic.Characteristic := hcharacteristic
  let mapped := characteristic.map (sylow : Subgroup ambient).subtype
  have hmapped : IsElemAbelian prime mapped :=
    elementary_abelian_map prime hcharacteristicElementary (sylow : Subgroup ambient).subtype
  have hmappedCard : Nat.card mapped = prime ^ 2 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hcharacteristicCard
  obtain ⟨actor, hactor, hactorElementary, hactorCard⟩ :=
    pRank_attained prime hprime (sylow : Subgroup ambient)
  have hnormalized : actor ≤ Subgroup.normalizer (mapped : Set ambient) :=
    hactor.trans (Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_characteristic characteristic hcharacteristic))
  refine ⟨characteristic, hcharacteristic, hcharacteristicElementary, hcharacteristicCard, ?_⟩
  exact normalizer_le_of_elementary_rank_two_normalized_by_rank_three
    prime hprime sylow hsylow hcore hactorElementary _ hsylowRank hactorCard
      (hactor.trans hsylow) hmapped hmappedCard ((Subgroup.map_subtype_le characteristic).trans hsylow) hnormalized

theorem escaping_primeCore_quotient_normal_pGroup_maximal_elementary_rank_two_is_normal
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup)) (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (hnormal : IsPGroup prime normal)
    (elementary : Subgroup normal) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup normal, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary) : elementary.Normal := by
  let : Fact prime.Prime := ⟨hprime⟩
  by_contra hnonnormal
  obtain ⟨characteristic, hcharacteristic, hcharacteristicElementary, hcharacteristicCard, _⟩ :=
    odd_pGroup_nonnormal_maximal_elementary_rank_two_has_characteristic_rank_two
      prime hodd hnormal elementary helementary hcard hmaximal hnonnormal
  let : characteristic.Characteristic := hcharacteristic
  let image := characteristic.map normal.subtype
  let : image.Normal := inferInstance
  have himageElementary := elementary_abelian_map prime hcharacteristicElementary normal.subtype
  have himageCard : Nat.card image = prime ^ 2 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hcharacteristicCard
  exact escaping_rank_three_primeCore_quotient_has_no_normal_elementary_rank_two
    prime hprime sylow hsylow hcore hrank hescape image himageElementary himageCard

end CFSG.PreuniquenessRankFour.Helpers
