module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSubgroup

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem normal_pSubgroup_has_central_prime_line
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (normal : Subgroup source) [normal.Normal] (hnontrivial : normal ≠ ⊥) :
    ∃ line : Subgroup source, line ≤ normal ∧ line ≤ Subgroup.center source ∧
      Nat.card line = prime ∧ line.Normal := by
  let intersection := normal ⊓ Subgroup.center source
  have hintersection : intersection ≠ ⊥ :=
    pGroup_normal_subgroup_meets_center prime hsource normal hnontrivial
  have hdivides : prime ∣ Nat.card intersection :=
    (hsource.to_subgroup intersection).card_eq_or_dvd.resolve_left
      (fun hcard => hintersection (Subgroup.card_eq_one.mp hcard))
  obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' prime hdivides
  let line := Subgroup.zpowers (member : source)
  have hlineNormal : line.Normal := by
    refine ⟨?_⟩
    intro scalar hscalar conjugator
    have hcentral : scalar ∈ Subgroup.center source :=
      (Subgroup.zpowers_le.mpr member.property.2) hscalar
    have hequal : conjugator * scalar * conjugator⁻¹ = scalar := by
      rw [Subgroup.mem_center_iff.mp hcentral, mul_inv_cancel_right]
    simpa only [hequal] using hscalar
  refine ⟨line, Subgroup.zpowers_le.mpr member.property.1,
    Subgroup.zpowers_le.mpr member.property.2, ?_, hlineNormal⟩
  rw [Nat.card_zpowers]
  exact (orderOf_injective intersection.subtype Subtype.val_injective member).trans horder

theorem surjective_hom_preimage_card
    {source target : Type u} [Group source] [Group target] [Finite source] [Finite target]
    (hom : source →* target) (hsurjective : Function.Surjective hom)
    (subgroup : Subgroup target) :
    Nat.card (subgroup.comap hom) = Nat.card subgroup * Nat.card hom.ker := by
  let preimage := subgroup.comap hom
  let restriction : preimage →* subgroup :=
    (hom.comp preimage.subtype).codRestrict subgroup (fun member => member.property)
  have hrestriction : Function.Surjective restriction := by
    intro member
    obtain ⟨lift, hlift⟩ := hsurjective member
    refine ⟨⟨lift, ?_⟩, Subtype.ext hlift⟩
    change hom lift ∈ subgroup
    rw [hlift]
    exact member.property
  have hkernel : restriction.ker.map preimage.subtype = hom.ker := by
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact congrArg (fun value : subgroup => (value : target)) hlift
    · intro hmember
      have hcontained : member ∈ preimage := by
        change hom member ∈ subgroup
        rw [MonoidHom.mem_ker.mp hmember]
        exact subgroup.one_mem
      refine ⟨⟨member, hcontained⟩, ?_, rfl⟩
      exact Subtype.ext (MonoidHom.mem_ker.mp hmember)
  have hkernelCard : Nat.card restriction.ker = Nat.card hom.ker := by
    rw [← hkernel, Subgroup.card_map_of_injective Subtype.val_injective]
  rw [restriction.ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective restriction hrestriction).toEquiv, hkernelCard]

theorem normal_pSubgroup_has_ambient_normal_subgroup_of_each_order
    (prime : ℕ) [Fact prime.Prime] (rank : ℕ) :
    ∀ {source : Type u} [Group source] [Finite source], IsPGroup prime source →
      ∀ normal : Subgroup source, normal.Normal → Nat.card normal = prime ^ rank →
        ∀ width ≤ rank, ∃ subgroup : Subgroup source,
          subgroup ≤ normal ∧ subgroup.Normal ∧ Nat.card subgroup = prime ^ width := by
  induction rank with
  | zero =>
    intro source _ _ _ normal _ _ width hwidth
    have hzero : width = 0 := by omega
    exact ⟨⊥, bot_le, inferInstance, by simp [hzero]⟩
  | succ rank hinduction =>
    intro source _ _ hsource normal hnormal hcard width hwidth
    let : normal.Normal := hnormal
    by_cases hzero : width = 0
    · exact ⟨⊥, bot_le, inferInstance, by simp [hzero]⟩
    have hnontrivial : normal ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcard
      have hlarge : 1 < prime ^ (rank + 1) :=
        one_lt_pow₀ (Fact.out : prime.Prime).one_lt (by omega)
      omega
    obtain ⟨line, hline, _, hlineCard, hlineNormal⟩ :=
      normal_pSubgroup_has_central_prime_line prime hsource normal hnontrivial
    let : line.Normal := hlineNormal
    let quotientMap := QuotientGroup.mk' line
    let image := normal.map quotientMap
    let : image.Normal := Subgroup.Normal.map hnormal quotientMap (QuotientGroup.mk'_surjective line)
    have himageCard : Nat.card image = prime ^ rank := by
      have hpreimage : image.comap quotientMap = normal := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hline]
      have hpreimageCard := surjective_hom_preimage_card
        quotientMap (QuotientGroup.mk'_surjective line) image
      rw [hpreimage, QuotientGroup.ker_mk', hlineCard, hcard, pow_succ] at hpreimageCard
      exact Nat.mul_right_cancel (Fact.out : prime.Prime).pos hpreimageCard.symm
    obtain ⟨small, hsmall, hsmallNormal, hsmallCard⟩ := hinduction
      (hsource.to_quotient line) image (inferInstance : image.Normal) himageCard
        (width - 1) (by omega)
    let : small.Normal := hsmallNormal
    refine ⟨small.comap quotientMap, ?_, inferInstance, ?_⟩
    · have hpreimage : image.comap quotientMap = normal := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hline]
      exact hpreimage ▸ Subgroup.comap_mono hsmall
    · rw [surjective_hom_preimage_card quotientMap (QuotientGroup.mk'_surjective line),
        QuotientGroup.ker_mk', hlineCard, hsmallCard, ← pow_succ]
      congr 1
      omega

end CFSG.PreuniquenessRankFour.Helpers
