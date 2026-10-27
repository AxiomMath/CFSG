module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.ComponentClassification.CoprimeAutomorphisms

theorem eq_one_of_fixed_displacement {G : Type*} [Group G]
    (subgroup : Subgroup G) [Finite subgroup] (automorphism : MulAut G)
    (exponent : ℕ) (hpower : automorphism ^ exponent = 1)
    (hcoprime : exponent.Coprime (Nat.card subgroup))
    (hfixed : ∀ element ∈ subgroup, automorphism element = element)
    (hdisplacement : ∀ element : G, element⁻¹ * automorphism element ∈ subgroup) :
    automorphism = 1 := by
  ext element
  let displacement := element⁻¹ * automorphism element
  have hmem : displacement ∈ subgroup := hdisplacement element
  have hdisplacementFixed : automorphism displacement = displacement := hfixed displacement hmem
  have hpowers : ∀ power : ℕ, (automorphism ^ power) element = element * displacement ^ power := by
    intro power
    induction power with
    | zero => simp
    | succ power hinduction =>
        rw [pow_succ', MulAut.mul_apply, hinduction, map_mul, map_pow, hdisplacementFixed]
        have hfirst : automorphism element = element * displacement := by dsimp [displacement]; group
        rw [hfirst, pow_succ']
        exact mul_assoc _ _ _
  have hpowerDisplacement : displacement ^ exponent = 1 := by
    have heq := hpowers exponent
    rw [hpower] at heq
    change element = element * displacement ^ exponent at heq
    exact mul_left_cancel (heq.symm.trans (mul_one element).symm)
  have hcardDisplacement : displacement ^ Nat.card subgroup = 1 := by
    have heq := pow_card_eq_one' (x := (⟨displacement, hmem⟩ : subgroup))
    exact congrArg Subtype.val heq
  have hone : displacement = 1 := (pow_eq_one_iff_of_coprime hcoprime).mp
    ⟨hpowerDisplacement, hcardDisplacement⟩
  change automorphism element = element
  exact (inv_mul_eq_one.mp hone).symm

theorem eq_one_of_self_centralizing_nilpotent {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G]
    (subgroup : Subgroup G) (hself : Subgroup.centralizer (subgroup : Set G) ≤ subgroup)
    (automorphism : MulAut G) (exponent : ℕ) (hpower : automorphism ^ exponent = 1)
    (hcoprime : exponent.Coprime (Nat.card G))
    (hfixed : ∀ element ∈ subgroup, automorphism element = element) : automorphism = 1 := by
  let fixed := FixedCommutingProduct.fixedSubgroup automorphism
  have hsubgroupFixed : subgroup ≤ fixed := hfixed
  have hfixedInvariant : fixed.map automorphism.toMonoidHom = fixed := by
    ext element
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      change automorphism (automorphism lift) = automorphism lift
      exact congrArg automorphism hlift
    · intro hmem
      exact ⟨element, hmem, hmem⟩
  let normalizer := Subgroup.normalizer (fixed : Set G)
  have hnormalizerInvariant : normalizer.map automorphism.toMonoidHom = normalizer := by
    rw [Subgroup.map_equiv_normalizer_eq, hfixedInvariant]
  let normalizerAutomorphism : MulAut normalizer :=
    (automorphism.subgroupMap normalizer).trans (MulEquiv.subgroupCongr hnormalizerInvariant)
  have hcentralDisplacement : ∀ element : normalizer,
      element.val⁻¹ * automorphism element.val ∈ Subgroup.centralizer (fixed : Set G) := by
    intro element
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have hconjugateMem := (Subgroup.mem_normalizer_iff.mp element.property member).mp hmember
    have hconjugateFixed : automorphism (element.val * member * element.val⁻¹) =
        element.val * member * element.val⁻¹ := hconjugateMem
    have hmemberFixed : automorphism member = member := hmember
    rw [map_mul, map_mul, map_inv, hmemberFixed] at hconjugateFixed
    have heq := congrArg (fun value : G => element.val⁻¹ * value * automorphism element.val)
      hconjugateFixed
    calc
      member * (element.val⁻¹ * automorphism element.val) =
          element.val⁻¹ * (element.val * member * element.val⁻¹) *
            automorphism element.val := by group
      _ = element.val⁻¹ * (automorphism element.val * member * (automorphism element.val)⁻¹) *
          automorphism element.val := heq.symm
      _ = (element.val⁻¹ * automorphism element.val) * member := by group
  have hdisplacementFixed : ∀ element : normalizer,
      element⁻¹ * normalizerAutomorphism element ∈ fixed.subgroupOf normalizer := by
    intro element
    have hcentralizerLe : Subgroup.centralizer (fixed : Set G) ≤ subgroup :=
      (Subgroup.centralizer_le hsubgroupFixed).trans hself
    exact hsubgroupFixed (hcentralizerLe (hcentralDisplacement element))
  have hnormalizerPower : normalizerAutomorphism ^ exponent = 1 := by
    have hpowers : ∀ power : ℕ, ∀ element : normalizer,
        ((normalizerAutomorphism ^ power) element).val = (automorphism ^ power) element.val := by
      intro power
      induction power with
      | zero => intro element; rfl
      | succ power hinduction =>
          intro element
          rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply]
          change automorphism (((normalizerAutomorphism ^ power) element).val) =
            automorphism ((automorphism ^ power) element.val)
          rw [hinduction]
    ext element
    rw [hpowers, hpower]
    rfl
  have hlocalFixed : ∀ element ∈ fixed.subgroupOf normalizer,
      normalizerAutomorphism element = element := by
    intro element hmem
    exact Subtype.ext hmem
  have hlocalCoprime : exponent.Coprime (Nat.card (fixed.subgroupOf normalizer)) :=
    hcoprime.of_dvd_right
      ((Subgroup.card_subgroup_dvd_card (fixed.subgroupOf normalizer)).trans
        (Subgroup.card_subgroup_dvd_card normalizer))
  have hnormalizerIdentity := eq_one_of_fixed_displacement (fixed.subgroupOf normalizer)
    normalizerAutomorphism exponent hnormalizerPower hlocalCoprime hlocalFixed hdisplacementFixed
  have hnormalizerLe : normalizer ≤ fixed := by
    intro element hmem
    have heq := congrArg (fun action : MulAut normalizer => action (⟨element, hmem⟩ : normalizer))
      hnormalizerIdentity
    exact congrArg Subtype.val heq
  have hnormalizerEq : normalizer = fixed := le_antisymm hnormalizerLe Subgroup.le_normalizer
  have hfixedTop : fixed = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent) fixed hnormalizerEq
  ext element
  have hmem : element ∈ fixed := by rw [hfixedTop]; exact Subgroup.mem_top _
  exact hmem

theorem eq_one_of_self_centralizing {G : Type*} [Group G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] (htwo : IsPGroup prime G)
    (subgroup : Subgroup G) (hself : Subgroup.centralizer (subgroup : Set G) ≤ subgroup)
    (automorphism : MulAut G) (exponent : ℕ) (hpower : automorphism ^ exponent = 1)
    (hcoprime : exponent.Coprime (Nat.card G))
    (hfixed : ∀ element ∈ subgroup, automorphism element = element) : automorphism = 1 := by
  let : Group.IsNilpotent G := htwo.isNilpotent
  exact eq_one_of_self_centralizing_nilpotent subgroup hself automorphism exponent
    hpower hcoprime hfixed

end CFSG.ComponentClassification.CoprimeAutomorphisms
