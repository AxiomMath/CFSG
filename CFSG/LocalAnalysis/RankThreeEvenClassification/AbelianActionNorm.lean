module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

abbrev primeLines (prime : ℕ) (actor : Type u) [Group actor] :=
  {line : Subgroup actor // Nat.card line = prime}

@[expose] def primeLineNonidentityMap {actor : Type u} [Group actor] (prime : ℕ) :
    (Σ line : primeLines prime actor, {element : line.1 // element ≠ 1}) →
      {element : actor // element ≠ 1} :=
  fun member => ⟨member.2.1, fun heq => member.2.2 (Subtype.ext heq)⟩

theorem prime_line_eq_zpowers_of_mem {actor : Type u} [Group actor]
    (prime : ℕ) (hprime : prime.Prime) (hpower : ∀ element : actor, element ^ prime = 1)
    (line : primeLines prime actor) (element : actor) (hmem : element ∈ line.1) (hne : element ≠ 1) :
    line.1 = Subgroup.zpowers element := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Finite line.1 := Nat.finite_of_card_ne_zero
    (fun heq => hprime.ne_zero (line.2.symm.trans heq))
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hmem)
  rw [line.2, Nat.card_zpowers, orderOf_eq_prime (hpower element) hne]

theorem primeLineNonidentityMap_bijective {actor : Type u} [Group actor]
    (prime : ℕ) (hprime : prime.Prime) (hpower : ∀ element : actor, element ^ prime = 1) :
    Function.Bijective (primeLineNonidentityMap (actor := actor) prime) := by
  have : Fact prime.Prime := ⟨hprime⟩
  constructor
  · rintro ⟨firstLine, first⟩ ⟨secondLine, second⟩ heq
    have hvalue : ((first : firstLine.1) : actor) = ((second : secondLine.1) : actor) :=
      congrArg Subtype.val heq
    have hfirstNe : ((first : firstLine.1) : actor) ≠ 1 := fun heq => first.2 (Subtype.ext heq)
    have hsecondNe : ((second : secondLine.1) : actor) ≠ 1 := fun heq => second.2 (Subtype.ext heq)
    have hfirstLine := prime_line_eq_zpowers_of_mem prime hprime hpower firstLine first first.1.property hfirstNe
    have hsecondLine := prime_line_eq_zpowers_of_mem prime hprime hpower secondLine second second.1.property hsecondNe
    have hlineEq : firstLine = secondLine := by
      apply Subtype.ext
      rw [hfirstLine, hsecondLine, hvalue]
    cases hlineEq
    exact congrArg (Sigma.mk firstLine) (Subtype.ext (Subtype.ext hvalue))
  · intro element
    let line : primeLines prime actor :=
      ⟨Subgroup.zpowers element.1, by rw [Nat.card_zpowers, orderOf_eq_prime (hpower element) element.2]⟩
    let internal : line.1 := ⟨element, Subgroup.mem_zpowers element.1⟩
    refine ⟨⟨line, internal, fun heq => element.2 (congrArg Subtype.val heq)⟩, ?_⟩
    rfl

theorem card_nonidentity {actor : Type u} [Group actor] [Fintype actor] [DecidableEq actor] :
    Fintype.card {element : actor // element ≠ 1} = Fintype.card actor - 1 := by
  classical
  simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun element : actor => element = 1)

theorem primeLines_card_of_square {actor : Type u} [Group actor] [Finite actor]
    (prime : ℕ) (hprime : prime.Prime) (hpower : ∀ element : actor, element ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 2) : Nat.card (primeLines prime actor) = prime + 1 := by
  classical
  let : Fintype actor := Fintype.ofFinite actor
  let : Fintype (primeLines prime actor) := Fintype.ofFinite _
  let : ∀ line : primeLines prime actor, Fintype line.1 := fun _ => Fintype.ofFinite _
  have hlineCard : ∀ line : primeLines prime actor,
      Fintype.card {element : line.1 // element ≠ 1} = prime - 1 := by
    intro line
    let : Fintype line.1 := Fintype.ofFinite _
    rw [card_nonidentity, ← Nat.card_eq_fintype_card, line.2]
  have hequivalence := Equiv.ofBijective (primeLineNonidentityMap (actor := actor) prime)
    (primeLineNonidentityMap_bijective prime hprime hpower)
  have hcount := Fintype.card_congr hequivalence
  rw [Fintype.card_sigma, card_nonidentity, ← Nat.card_eq_fintype_card, hcard] at hcount
  simp only [hlineCard, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hcount
  have hprimeLower := hprime.two_le
  have hfactor : (prime + 1) * (prime - 1) = prime ^ 2 - 1 := by
    have hsub : prime - 1 + 1 = prime := Nat.sub_add_cancel (by omega)
    have hsquareSub : prime ^ 2 - 1 + 1 = prime ^ 2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  have hlineEq : Fintype.card (primeLines prime actor) = prime + 1 := by
    exact Nat.eq_of_mul_eq_mul_right (by omega) (hcount.trans hfactor.symm)
  simpa only [Nat.card_eq_fintype_card] using hlineEq

@[expose] noncomputable def actionNorm {actor : Type u} {acted : Type v} [Group actor] [CommGroup acted]
    [MulDistribMulAction actor acted] (subgroup : Subgroup actor) [Fintype subgroup]
    (element : acted) : acted := ∏ member : subgroup, (member : actor) • element

theorem actionNorm_fixed {actor : Type u} {acted : Type v} [Group actor] [CommGroup acted]
    [MulDistribMulAction actor acted] (subgroup : Subgroup actor) [Fintype subgroup]
    (element : acted) (member : subgroup) :
    (member : actor) • actionNorm subgroup element = actionNorm subgroup element := by
  classical
  rw [actionNorm, Finset.smul_prod']
  exact Fintype.prod_equiv (Equiv.mulLeft member)
    (fun other : subgroup => (member : actor) • ((other : actor) • element))
    (fun other : subgroup => (other : actor) • element)
    (fun other => (mul_smul (member : actor) (other : actor) element).symm)

theorem prime_line_norm_product {actor : Type u} {acted : Type v}
    [Group actor] [Fintype actor] [DecidableEq actor] [CommGroup acted] [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpower : ∀ member : actor, member ^ prime = 1)
    [Fintype (primeLines prime actor)] [∀ line : primeLines prime actor, Fintype line.1]
    (element : acted) :
    (∏ line : primeLines prime actor, actionNorm line.1 element) =
      element ^ (Fintype.card (primeLines prime actor)) *
        ∏ member : {member : actor // member ≠ 1}, (member : actor) • element := by
  classical
  have hlineNorm : ∀ line : primeLines prime actor,
      actionNorm line.1 element = element *
        ∏ member : {member : line.1 // member ≠ 1}, ((member : line.1) : actor) • element := by
    intro line
    rw [actionNorm, Fintype.prod_eq_mul_prod_subtype_ne _ 1]
    simp only [Subgroup.coe_one, one_smul]
  simp only [hlineNorm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [← Fintype.prod_sigma' (fun (line : primeLines prime actor)
    (member : {member : line.1 // member ≠ 1}) => ((member : line.1) : actor) • element)]
  exact Fintype.prod_equiv
    (Equiv.ofBijective (primeLineNonidentityMap (actor := actor) prime)
      (primeLineNonidentityMap_bijective prime hprime hpower)) _ _ (fun _ => rfl)

@[expose] def actionFixedSubgroup {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    [MulDistribMulAction actor acted] (member : actor) : Subgroup acted :=
  (MulDistribMulAction.toMonoidHom acted member).eqLocus (MonoidHom.id acted)

@[expose] noncomputable def actionFixedGenerated {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted] : Subgroup acted :=
  ⨆ (member : actor) (_ : member ≠ 1), actionFixedSubgroup member

theorem actionNorm_mem_fixed_generated {actor : Type u} {acted : Type v}
    [Group actor] [CommGroup acted] [MulDistribMulAction actor acted]
    (subgroup : Subgroup actor) [Fintype subgroup]
    (hne : subgroup ≠ ⊥) (element : acted) :
    actionNorm subgroup element ∈ actionFixedGenerated (actor := actor) := by
  obtain ⟨member, hmemberNe⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hneActor : (member : actor) ≠ 1 := fun heq => hmemberNe (Subtype.ext heq)
  apply Subgroup.mem_iSup_of_mem (member : actor)
  apply Subgroup.mem_iSup_of_mem hneActor
  exact actionNorm_fixed subgroup element member

theorem abelian_action_fixed_generated_eq_top {actor : Type u} {acted : Type v}
    [Group actor] [Finite actor] [CommGroup acted] [Finite acted]
    [MulDistribMulAction actor acted] (prime : ℕ) (hprime : prime.Prime)
    (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 2) (hcomplement : ¬prime ∣ Nat.card acted) :
    actionFixedGenerated (actor := actor) (acted := acted) = ⊤ := by
  classical
  let : Fintype actor := Fintype.ofFinite _
  let : Fintype (primeLines prime actor) := Fintype.ofFinite _
  let : ∀ line : primeLines prime actor, Fintype line.1 := fun _ => Fintype.ofFinite _
  let : Fintype (⊤ : Subgroup actor) := Fintype.ofFinite _
  have hlineCount : Fintype.card (primeLines prime actor) = prime + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact primeLines_card_of_square prime hprime hpower hcard
  have hactorNontrivial : (⊤ : Subgroup actor) ≠ ⊥ := by
    intro heq
    have hone := Subgroup.card_eq_one.mpr heq
    rw [Subgroup.card_top, hcard] at hone
    have hlarge : 1 < prime ^ 2 := by nlinarith [hprime.two_le]
    omega
  have hpowerMem : ∀ element : acted, element ^ prime ∈ actionFixedGenerated (actor := actor) := by
    intro element
    have hlineProductMem : (∏ line : primeLines prime actor, actionNorm line.1 element) ∈
        actionFixedGenerated (actor := actor) := by
      apply Subgroup.prod_mem
      intro line _
      apply actionNorm_mem_fixed_generated line.1 _ element
      intro heq
      have hone := Subgroup.card_eq_one.mpr heq
      exact hprime.ne_one (line.2.symm.trans hone)
    have hfullNormMem := actionNorm_mem_fixed_generated (⊤ : Subgroup actor) hactorNontrivial element
    have hfullNorm : actionNorm (⊤ : Subgroup actor) element = ∏ member : actor, member • element := by
      exact Fintype.prod_equiv Subgroup.topEquiv.toEquiv _ _ (fun _ => rfl)
    have hlineProduct := prime_line_norm_product prime hprime hpower element
    rw [hlineCount] at hlineProduct
    have hfullProduct := Fintype.prod_eq_mul_prod_subtype_ne (fun member : actor => member • element) 1
    simp only [one_smul] at hfullProduct
    have hnormIdentity : (∏ line : primeLines prime actor, actionNorm line.1 element) *
        (actionNorm (⊤ : Subgroup actor) element)⁻¹ = element ^ prime := by
      rw [hlineProduct, hfullNorm, hfullProduct, pow_succ]
      group
    rw [← hnormIdentity]
    exact (actionFixedGenerated (actor := actor)).mul_mem hlineProductMem
      ((actionFixedGenerated (actor := actor)).inv_mem hfullNormMem)
  apply top_le_iff.mp
  intro element _
  obtain ⟨preimage, rfl⟩ :=
    (hprime.coprime_iff_not_dvd.mpr hcomplement).symm.pow_left_bijective.surjective element
  exact hpowerMem preimage

end CFSG.RankThreeEvenClassification.Helpers
