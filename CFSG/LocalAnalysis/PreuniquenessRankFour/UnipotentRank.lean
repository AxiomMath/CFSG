module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSubgroup

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v w

theorem linear_composite_kernel_finrank_bound
    {coefficient : Type u} {source : Type v} {target : Type w}
    [Field coefficient] [AddCommGroup source] [AddCommGroup target]
    [Module coefficient source] [Module coefficient target]
    [FiniteDimensional coefficient source] [FiniteDimensional coefficient target]
    (first : source →ₗ[coefficient] target) (second : target →ₗ[coefficient] target) :
    Module.finrank coefficient (second.comp first).ker ≤
      Module.finrank coefficient first.ker + Module.finrank coefficient second.ker := by
  let kernel := (second.comp first).ker
  let restriction : kernel →ₗ[coefficient] second.ker :=
    (first.domRestrict kernel).codRestrict second.ker (fun member => member.property)
  let kernelEmbedding : restriction.ker →ₗ[coefficient] first.ker :=
    { toFun := fun member => ⟨((member : kernel) : source), by
        have hzero := congrArg (fun value : second.ker => (value : target)) member.property
        exact hzero⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinjective : Function.Injective kernelEmbedding := by
    intro firstMember secondMember hequal
    have hvalues := congrArg (fun member : first.ker => (member : source)) hequal
    exact Subtype.ext (Subtype.ext hvalues)
  have hkernelRank := LinearMap.finrank_le_finrank_of_injective hinjective
  have hrangeRank : Module.finrank coefficient restriction.range ≤
      Module.finrank coefficient second.ker := Submodule.finrank_le _
  have hdimension := restriction.finrank_range_add_finrank_ker
  change Module.finrank coefficient restriction.range + Module.finrank coefficient restriction.ker =
    Module.finrank coefficient (second.comp first).ker at hdimension
  omega

theorem linear_power_kernel_finrank_bound
    {coefficient : Type u} {space : Type v}
    [Field coefficient] [AddCommGroup space] [Module coefficient space]
    [FiniteDimensional coefficient space]
    (endomorphism : Module.End coefficient space) (exponent : ℕ) :
    Module.finrank coefficient (endomorphism ^ exponent).ker ≤
      exponent * Module.finrank coefficient endomorphism.ker := by
  induction exponent with
  | zero =>
    rw [pow_zero]
    change Module.finrank coefficient (LinearMap.id : Module.End coefficient space).ker ≤ _
    rw [LinearMap.ker_id]
    simp
  | succ exponent hinduction =>
    have hcomposition := linear_composite_kernel_finrank_bound
      (endomorphism ^ exponent) endomorphism
    have hequal : endomorphism.comp (endomorphism ^ exponent) = endomorphism ^ (exponent + 1) := by
      rw [pow_succ']
      rfl
    rw [hequal] at hcomposition
    rw [Nat.succ_mul]
    omega

theorem nilpotent_linear_finrank_bound_by_kernel
    {coefficient : Type u} {space : Type v}
    [Field coefficient] [AddCommGroup space] [Module coefficient space]
    [FiniteDimensional coefficient space]
    (endomorphism : Module.End coefficient space) (exponent : ℕ)
    (hzero : endomorphism ^ exponent = 0) :
    Module.finrank coefficient space ≤ exponent * Module.finrank coefficient endomorphism.ker := by
  have hbound := linear_power_kernel_finrank_bound endomorphism exponent
  rw [hzero, LinearMap.ker_zero, finrank_top] at hbound
  exact hbound

theorem prime_order_linear_displacement_nilpotent
    {space : Type v} [AddCommGroup space] (prime : ℕ) [Fact prime.Prime]
    [Module (ZMod prime) space]
    (endomorphism : Module.End (ZMod prime) space) (horder : endomorphism ^ prime = 1) :
    (endomorphism - 1) ^ prime = 0 := by
  have hcommute : Commute endomorphism (-1 : Module.End (ZMod prime) space) :=
    Commute.neg_one_right endomorphism
  obtain ⟨remainder, hequal⟩ := hcommute.exists_add_pow_prime_eq (Fact.out : prime.Prime)
  have hcast : (prime : Module.End (ZMod prime) space) = 0 := by
    ext member
    rw [Module.End.natCast_apply]
    change prime • member = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod prime), CharP.cast_eq_zero (ZMod prime) prime, zero_smul]
  have hnegPower : (-1 : Module.End (ZMod prime) space) ^ prime = -1 := by
    rcases (Fact.out : prime.Prime).eq_two_or_odd' with hequal | hodd
    · subst prime
      have hnegOne : (-1 : Module.End (ZMod 2) space) = 1 := by
        apply neg_eq_iff_add_eq_zero.mpr
        simpa only [Nat.cast_ofNat, one_add_one_eq_two] using hcast
      rw [hnegOne, one_pow]
    · exact hodd.neg_one_pow
  rw [horder, hcast, hnegPower, zero_mul, zero_mul, zero_mul,
    add_neg_cancel, zero_add] at hequal
  simpa only [sub_eq_add_neg] using hequal

theorem prime_order_linear_fixed_space_dimension_bound
    {space : Type v} [AddCommGroup space] (prime : ℕ) [Fact prime.Prime]
    [Module (ZMod prime) space] [FiniteDimensional (ZMod prime) space]
    (endomorphism : Module.End (ZMod prime) space) (horder : endomorphism ^ prime = 1) :
    Module.finrank (ZMod prime) space ≤
      prime * Module.finrank (ZMod prime) (endomorphism - 1).ker :=
  nilpotent_linear_finrank_bound_by_kernel (endomorphism - 1) prime
    (prime_order_linear_displacement_nilpotent prime endomorphism horder)

theorem prime_order_automorphism_elementary_cardinality_bound
    {source : Type v} [CommGroup source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] [Module (ZMod prime) (Additive source)]
    (automorphism : MulAut source) (horder : automorphism ^ prime = 1) (fixedRank : ℕ)
    (hfixed : Nat.card {member : source // automorphism member = member} ≤ prime ^ fixedRank) :
    Nat.card source ≤ prime ^ (prime * fixedRank) := by
  let endomorphism : Module.End (ZMod prime) (Additive source) :=
    AddMonoidHom.toZModLinearMap prime (MonoidHom.toAdditive automorphism.toMonoidHom)
  have hlinearOrder : endomorphism ^ prime = (1 : Module.End (ZMod prime) (Additive source)) := by
    have hpowers : ∀ exponent : ℕ, ∀ member : Additive source,
        (endomorphism ^ exponent) member = Additive.ofMul ((automorphism ^ exponent) member.toMul) := by
      intro exponent
      induction exponent with
      | zero => intro member; rfl
      | succ exponent hinduction =>
        intro member
        rw [pow_succ', pow_succ']
        change endomorphism ((endomorphism ^ exponent) member) =
          Additive.ofMul (automorphism ((automorphism ^ exponent) member.toMul))
        rw [hinduction]
        rfl
    ext member
    rw [hpowers, horder]
    rfl
  let kernel := (endomorphism - 1).ker
  let equivalence : kernel ≃ {member : source // automorphism member = member} :=
    { toFun := fun member => ⟨member.val.toMul, by
        have hzero := member.property
        change Additive.ofMul (automorphism member.val.toMul) - member.val = 0 at hzero
        exact congrArg Additive.toMul (sub_eq_zero.mp hzero)⟩
      invFun := fun member => ⟨Additive.ofMul member.val, by
        change Additive.ofMul (automorphism member.val) - Additive.ofMul member.val = 0
        rw [member.property, sub_self]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hkernelCard : Nat.card kernel = prime ^ Module.finrank (ZMod prime) kernel := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod prime) (V := kernel))
  have hkernelRank : Module.finrank (ZMod prime) kernel ≤ fixedRank := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp
    rw [← hkernelCard, Nat.card_congr equivalence]
    exact hfixed
  have hdimension := prime_order_linear_fixed_space_dimension_bound prime endomorphism hlinearOrder
  have hsourceCard : Nat.card source = prime ^ Module.finrank (ZMod prime) (Additive source) := by
    rw [← Nat.card_congr (Additive.toMul : Additive source ≃ source)]
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod prime) (V := Additive source))
  rw [hsourceCard]
  exact Nat.pow_le_pow_right (Fact.out : prime.Prime).pos
    (hdimension.trans (Nat.mul_le_mul_left prime hkernelRank))

theorem prime_order_elementary_centralizer_cardinality_bound
    {ambient : Type v} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime] (elementary : Subgroup ambient)
    (helementary : IsElemAbelian prime elementary)
    (member : ambient) (hnormalizes : member ∈ Subgroup.normalizer (elementary : Set ambient))
    (hpow : member ^ prime = 1) (fixedRank : ℕ)
    (hfixed : Nat.card (elementary ⊓ Subgroup.centralizer ({member} : Set ambient) : Subgroup ambient) ≤
      prime ^ fixedRank) : Nat.card elementary ≤ prime ^ (prime * fixedRank) := by
  let : IsMulCommutative elementary := helementary.1
  let : CommGroup elementary := IsMulCommutative.instCommGroup
  let : Module (ZMod prime) (Additive elementary) :=
    AddCommGroup.zmodModule (n := prime) (G := Additive elementary) fun scalar => by
      change Additive.ofMul (scalar.toMul ^ prime) = 0
      rw [show scalar.toMul ^ prime = 1 from Subtype.ext (helementary.2 _ scalar.toMul.property)]
      rfl
  let automorphism := elementary.normalizerMonoidHom ⟨member, hnormalizes⟩
  have horder : automorphism ^ prime = 1 := by
    rw [← map_pow]
    have hidentity : (⟨member, hnormalizes⟩ : Subgroup.normalizer (elementary : Set ambient)) ^ prime = 1 :=
      Subtype.ext hpow
    rw [hidentity, map_one]
  let intersection := elementary ⊓ Subgroup.centralizer ({member} : Set ambient)
  let equivalence : {scalar : elementary // automorphism scalar = scalar} ≃ intersection :=
    { toFun := fun scalar => ⟨scalar.val, scalar.val.property, by
        apply Subgroup.mem_centralizer_iff.mpr
        intro other hother
        have hequal := congrArg (fun value : elementary => (value : ambient)) scalar.property
        change member * (scalar.val : ambient) * member⁻¹ = scalar.val at hequal
        have hcommute := congrArg (fun value : ambient => value * member) hequal
        have hsingleton : other = member := Set.mem_singleton_iff.mp hother
        subst other
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcommute⟩
      invFun := fun scalar => ⟨⟨scalar.val, scalar.property.1⟩, by
        apply Subtype.ext
        change member * scalar.val * member⁻¹ = scalar.val
        have hcommute := Subgroup.mem_centralizer_iff.mp scalar.property.2 member (Set.mem_singleton member)
        rw [hcommute, mul_assoc, mul_inv_cancel, mul_one]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply prime_order_automorphism_elementary_cardinality_bound prime automorphism horder fixedRank
  rw [Nat.card_congr equivalence]
  exact hfixed

theorem elementary_rank_two_maximal_centralizer_is_self
    {ambient : Type v} [Group ambient] [Finite ambient]
    (prime : ℕ) {overgroup elementary : Subgroup ambient}
    (helementary : IsElemAbelian prime elementary) (hcontained : elementary ≤ overgroup)
    (hmaximal : ∀ extension : Subgroup ambient, elementary ≤ extension → extension ≤ overgroup →
      IsElemAbelian prime extension → extension = elementary)
    (member : ambient) (hmember : member ∈ overgroup) (hpow : member ^ prime = 1)
    (hcentralizes : member ∈ Subgroup.centralizer (elementary : Set ambient)) : member ∈ elementary := by
  have hcyclicElementary : IsElemAbelian prime (Subgroup.zpowers member) := by
    refine ⟨inferInstance, ?_⟩
    intro scalar hscalar
    obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hscalar
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
  have hcyclicCentral : Subgroup.zpowers member ≤ Subgroup.centralizer (elementary : Set ambient) :=
    Subgroup.zpowers_le.mpr hcentralizes
  have hjoinElementary := elementary_abelian_sup_of_commuting prime hcyclicElementary helementary hcyclicCentral
  have hequal := hmaximal (Subgroup.zpowers member ⊔ elementary) le_sup_right
    (sup_le (Subgroup.zpowers_le.mpr hmember) hcontained) hjoinElementary
  rw [← hequal]
  exact (le_sup_left : Subgroup.zpowers member ≤ Subgroup.zpowers member ⊔ elementary)
    (Subgroup.mem_zpowers member)

theorem maximal_elementary_rank_two_normalized_elementary_fixed_rank_bound
    {ambient : Type v} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime] {overgroup elementary normalized : Subgroup ambient}
    (helementary : IsElemAbelian prime elementary) (hcard : Nat.card elementary = prime ^ 2)
    (hcontained : elementary ≤ overgroup)
    (hmaximal : ∀ extension : Subgroup ambient, elementary ≤ extension → extension ≤ overgroup →
      IsElemAbelian prime extension → extension = elementary)
    (hnormalizedElementary : IsElemAbelian prime normalized) (hnormalizedContained : normalized ≤ overgroup)
    (hnotContained : ¬ elementary ≤ normalized)
    (member : ambient) (hmember : member ∈ elementary)
    (hnormalizes : member ∈ Subgroup.normalizer (normalized : Set ambient))
    (hfixedCentralizes : normalized ⊓ Subgroup.centralizer ({member} : Set ambient) ≤
      Subgroup.centralizer (elementary : Set ambient)) : Nat.card normalized ≤ prime ^ prime := by
  let intersection := normalized ⊓ elementary
  have hintersectionCard : Nat.card intersection < prime ^ 2 := by
    by_contra hnotSmall
    have hequal : intersection = elementary := Subgroup.eq_of_le_of_card_ge inf_le_right
      (by rw [hcard]; omega)
    exact hnotContained (hequal ▸ (show intersection ≤ normalized from inf_le_left))
  have hnormalizedGroup : IsPGroup prime normalized := isPGroup_iff_pow_pow_eq_one.mpr fun scalar =>
    ⟨1, by
      apply Subtype.ext
      change (scalar : ambient) ^ (prime ^ 1) = 1
      simpa only [pow_one] using hnormalizedElementary.2 scalar scalar.property⟩
  obtain ⟨intersectionRank, hintersectionPower⟩ :=
    (hnormalizedGroup.to_le inf_le_left : IsPGroup prime intersection).exists_card_eq
  have hintersectionRank : intersectionRank ≤ 1 := by
    have hbound : prime ^ intersectionRank < prime ^ 2 := hintersectionPower ▸ hintersectionCard
    have hexponent := (Nat.pow_lt_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hbound
    omega
  have hintersectionBound : Nat.card intersection ≤ prime := by
    rw [hintersectionPower]
    simpa only [pow_one] using Nat.pow_le_pow_right (Fact.out : prime.Prime).pos hintersectionRank
  have hfixedContained : normalized ⊓ Subgroup.centralizer ({member} : Set ambient) ≤ intersection := by
    intro scalar hscalar
    refine ⟨hscalar.1, ?_⟩
    exact elementary_rank_two_maximal_centralizer_is_self prime helementary hcontained hmaximal
      scalar (hnormalizedContained hscalar.1) (hnormalizedElementary.2 scalar hscalar.1)
      (hfixedCentralizes hscalar)
  have hfixedBound := (Subgroup.card_le_of_le hfixedContained).trans hintersectionBound
  have hbound := prime_order_elementary_centralizer_cardinality_bound prime normalized
    hnormalizedElementary member hnormalizes (helementary.2 member hmember) 1 (by simpa using hfixedBound)
  simpa only [mul_one] using hbound

theorem maximal_elementary_rank_two_with_central_line_normalized_elementary_bound
    {ambient : Type v} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime] {overgroup elementary normalized line : Subgroup ambient}
    (helementary : IsElemAbelian prime elementary) (hcard : Nat.card elementary = prime ^ 2)
    (hcontained : elementary ≤ overgroup)
    (hmaximal : ∀ extension : Subgroup ambient, elementary ≤ extension → extension ≤ overgroup →
      IsElemAbelian prime extension → extension = elementary)
    (hnormalizedElementary : IsElemAbelian prime normalized) (hnormalizedContained : normalized ≤ overgroup)
    (hnotContained : ¬ elementary ≤ normalized)
    (member : ambient) (hmember : member ∈ elementary)
    (hnormalizes : member ∈ Subgroup.normalizer (normalized : Set ambient))
    (hlineCentral : line ≤ Subgroup.centralizer (normalized : Set ambient))
    (hgeneration : elementary = line ⊔ Subgroup.zpowers member) : Nat.card normalized ≤ prime ^ prime := by
  apply maximal_elementary_rank_two_normalized_elementary_fixed_rank_bound prime helementary hcard
    hcontained hmaximal hnormalizedElementary hnormalizedContained hnotContained member hmember hnormalizes
  apply Subgroup.le_centralizer_iff.mpr
  rw [hgeneration]
  apply sup_le
  · exact hlineCentral.trans (Subgroup.centralizer_le inf_le_left)
  · apply Subgroup.zpowers_le.mpr
    apply Subgroup.mem_centralizer_iff.mpr
    intro scalar hscalar
    exact Subgroup.mem_centralizer_iff.mp hscalar.2 member (Set.mem_singleton member) |>.symm

theorem rank_two_elementary_central_line_has_complement_generator
    {ambient : Type v} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime] {elementary line : Subgroup ambient}
    (helementary : IsElemAbelian prime elementary) (hcard : Nat.card elementary = prime ^ 2)
    (hline : line ≤ elementary) (hlineCard : Nat.card line = prime) :
    ∃ member : ambient, member ∈ elementary ∧ elementary = line ⊔ Subgroup.zpowers member := by
  have hproper : ¬ elementary ≤ line := by
    intro hcontained
    have hbound := Subgroup.card_le_of_le hcontained
    rw [hcard, hlineCard] at hbound
    have hlarge : prime < prime ^ 2 := by
      simpa only [pow_one] using
        (Nat.pow_lt_pow_iff_right (Fact.out : prime.Prime).one_lt).mpr (by omega : 1 < 2)
    omega
  obtain ⟨member, hmember, hnotLine⟩ : ∃ member : ambient, member ∈ elementary ∧ member ∉ line := by
    by_contra hnone
    push Not at hnone
    exact hproper hnone
  let joined := line ⊔ Subgroup.zpowers member
  have hjoinContained : joined ≤ elementary := sup_le hline (Subgroup.zpowers_le.mpr hmember)
  have hjoinLarge : prime < Nat.card joined := by
    by_contra hnotLarge
    have hequal : line = joined := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hlineCard]; omega)
    exact hnotLine (hequal ▸ (le_sup_right : Subgroup.zpowers member ≤ joined) (Subgroup.mem_zpowers member))
  have hgroup : IsPGroup prime elementary := isPGroup_iff_pow_pow_eq_one.mpr fun scalar =>
    ⟨1, by
      apply Subtype.ext
      change (scalar : ambient) ^ (prime ^ 1) = 1
      simpa only [pow_one] using helementary.2 scalar scalar.property⟩
  obtain ⟨rank, hjoinCard⟩ := (hgroup.to_le hjoinContained).exists_card_eq
  have hrank : 2 ≤ rank := by
    have hbound : prime ^ 1 < prime ^ rank := by simpa only [pow_one, ← hjoinCard] using hjoinLarge
    have := (Nat.pow_lt_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hbound
    omega
  have hequal : joined = elementary := Subgroup.eq_of_le_of_card_ge hjoinContained (by
    rw [hcard, hjoinCard]
    exact Nat.pow_le_pow_right (Fact.out : prime.Prime).pos hrank)
  exact ⟨member, hmember, hequal.symm⟩

theorem nonnormal_maximal_elementary_rank_two_has_central_prime_line
    {source : Type v} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (elementary : Subgroup source) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup source, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary)
    (hnonnormal : ¬ elementary.Normal) :
    centralPrimeTorsion prime source ≤ elementary ∧
      Nat.card (centralPrimeTorsion prime source) = prime := by
  let line := centralPrimeTorsion prime source
  let : line.Characteristic := centralPrimeTorsion_characteristic prime
  have hline : line ≤ elementary := by
    intro member hmember
    have hcentral := (mem_centralPrimeTorsion prime member).mp hmember
    apply elementary_rank_two_maximal_centralizer_is_self prime helementary le_top
      (fun extension hcontained _ hextension => hmaximal extension hcontained hextension)
      member (Subgroup.mem_top member) hcentral.2
    exact Subgroup.center_le_centralizer elementary hcentral.1
  have hlineNontrivial : line ≠ ⊥ := by
    have hnontrivialSource : Nontrivial source := Finite.one_lt_card_iff_nontrivial.mp (by
      have hlarge : 1 < prime ^ 2 := one_lt_pow₀ (Fact.out : prime.Prime).one_lt (by omega)
      exact (hcard ▸ hlarge).trans_le elementary.card_le_card_group)
    let : Nontrivial source := hnontrivialSource
    have hintersection := pGroup_normal_subgroup_meets_centralPrimeTorsion prime hsource
      (⊤ : Subgroup source) top_ne_bot
    simpa only [top_inf_eq] using hintersection
  obtain ⟨rank, hlineCard⟩ := (hsource.to_subgroup line).exists_card_eq
  have hsmall : Nat.card line < prime ^ 2 := by
    by_contra hlarge
    have hequal : line = elementary := Subgroup.eq_of_le_of_card_ge hline (by rw [hcard]; omega)
    exact hnonnormal (hequal ▸ (inferInstance : line.Normal))
  have hrank : rank = 1 := by
    have hbound : prime ^ rank < prime ^ 2 := hlineCard ▸ hsmall
    have hupper := (Nat.pow_lt_pow_iff_right (Fact.out : prime.Prime).one_lt).mp hbound
    have hpositive : rank ≠ 0 := by
      intro hzero
      rw [hzero, pow_zero] at hlineCard
      exact hlineNontrivial (Subgroup.card_eq_one.mp hlineCard)
    omega
  exact ⟨hline, by simpa only [hrank, pow_one] using hlineCard⟩

theorem nonnormal_maximal_elementary_rank_two_normalized_elementary_card_bound
    {source : Type v} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (elementary : Subgroup source) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup source, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary)
    (hnonnormal : ¬ elementary.Normal)
    (normalized : Subgroup source) (hnormalized : IsElemAbelian prime normalized)
    (hnormalizes : elementary ≤ Subgroup.normalizer (normalized : Set source))
    (hnotContained : ¬ elementary ≤ normalized) : Nat.card normalized ≤ prime ^ prime := by
  obtain ⟨hline, hlineCard⟩ := nonnormal_maximal_elementary_rank_two_has_central_prime_line
    prime hsource elementary helementary hcard hmaximal hnonnormal
  obtain ⟨member, hmember, hgeneration⟩ := rank_two_elementary_central_line_has_complement_generator
    prime helementary hcard hline hlineCard
  apply maximal_elementary_rank_two_with_central_line_normalized_elementary_bound prime helementary
    hcard le_top (fun extension hcontained _ hextension => hmaximal extension hcontained hextension)
    hnormalized le_top hnotContained member hmember (hnormalizes hmember) _ hgeneration
  intro scalar hscalar
  exact Subgroup.center_le_centralizer normalized
    ((mem_centralPrimeTorsion prime scalar).mp hscalar).1

theorem nonnormal_maximal_elementary_rank_two_normal_elementary_rank_bound
    {source : Type v} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (elementary : Subgroup source) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2)
    (hmaximal : ∀ extension : Subgroup source, elementary ≤ extension →
      IsElemAbelian prime extension → extension = elementary)
    (hnonnormal : ¬ elementary.Normal)
    (normal : Subgroup source) [normal.Normal] (hnormal : IsElemAbelian prime normal) :
    pRank prime normal ≤ prime := by
  have hnotContained : ¬ elementary ≤ normal := by
    intro hcontained
    have hequal := hmaximal normal hcontained hnormal
    exact hnonnormal (hequal ▸ (inferInstance : normal.Normal))
  have hbound := nonnormal_maximal_elementary_rank_two_normalized_elementary_card_bound
    prime hsource elementary helementary hcard hmaximal hnonnormal normal hnormal
    (fun _ _ => by rw [Subgroup.normalizer_eq_top]; trivial) hnotContained
  obtain ⟨attaining, hcontained, _, hattainingCard⟩ := pRank_attained prime Fact.out normal
  apply (Nat.pow_le_pow_iff_right (Fact.out : prime.Prime).one_lt).mp
  rw [← hattainingCard]
  exact (Subgroup.card_le_of_le hcontained).trans hbound

theorem escaping_elementary_rank_two_not_normal_in_containing_sylow
    {ambient : Type v} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup elementary : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hsylowRank : 3 ≤ pRank prime (sylow : Subgroup ambient))
    (helementary : IsElemAbelian prime elementary) (hcard : Nat.card elementary = prime ^ 2)
    (hcontained : elementary ≤ sylow)
    (hescape : ¬ Subgroup.normalizer (elementary : Set ambient) ≤ overgroup) :
    ¬ (elementary.subgroupOf (sylow : Subgroup ambient)).Normal := by
  intro hnormal
  have hnormalized : (sylow : Subgroup ambient) ≤ Subgroup.normalizer (elementary : Set ambient) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcontained).mp hnormal
  have hbound := escaping_elementary_rank_two_normalizer_rank_le_two prime hprime sylow
    hsylow hcore helementary hcard (hcontained.trans hsylow) hescape
  have hlower := pRank_mono prime hprime (le_inf hsylow hnormalized)
  omega

theorem escaping_maximal_elementary_rank_two_sylow_normal_elementary_rank_bound
    {ambient : Type v} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup elementary : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hsylowRank : 3 ≤ pRank prime (sylow : Subgroup ambient))
    (helementary : IsElemAbelian prime elementary) (hcard : Nat.card elementary = prime ^ 2)
    (hcontained : elementary ≤ sylow)
    (hmaximal : ∀ extension : Subgroup ambient, elementary ≤ extension → extension ≤ sylow →
      IsElemAbelian prime extension → extension = elementary)
    (hescape : ¬ Subgroup.normalizer (elementary : Set ambient) ≤ overgroup)
    (normal : Subgroup (sylow : Subgroup ambient)) [normal.Normal]
    (hnormal : IsElemAbelian prime normal) :
    pRank prime (normal.map (sylow : Subgroup ambient).subtype) ≤ prime := by
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
  rw [pRank_map_of_injective prime hprime (sylow : Subgroup ambient).subtype Subtype.val_injective]
  exact nonnormal_maximal_elementary_rank_two_normal_elementary_rank_bound prime sylow.isPGroup'
    localElementary hlocalElementary hlocalCard hlocalMaximal hnonnormal normal hnormal

end CFSG.PreuniquenessRankFour.Helpers
