module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticLinearIdentities
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantLinearActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

theorem pGroup_of_pKernel_pRange {G : Type u} {H : Type v} [Group G] [Group H]
    (prime : ℕ) (homomorphism : G →* H)
    (hkernel : IsPGroup prime homomorphism.ker) (hrange : IsPGroup prime homomorphism.range) :
    IsPGroup prime G := by
  have htop : (⊤ : Subgroup homomorphism.range).comap homomorphism.rangeRestrict = ⊤ :=
    Subgroup.comap_top _
  have hpreimageGroup : IsPGroup prime ((⊤ : Subgroup homomorphism.range).comap homomorphism.rangeRestrict) := by
    exact ((hrange.to_subgroup ⊤).comap_of_ker_isPGroup homomorphism.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict]
      exact hkernel))
  exact (hpreimageGroup.of_equiv (MulEquiv.subgroupCongr htop)).of_equiv Subgroup.topEquiv

theorem quadratic_linear_of_fixed_subspace_quotient {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (equivalence : space ≃ₗ[field] space) (subspace : Submodule field space)
    (hfixed : ∀ member ∈ subspace, equivalence member = member)
    (hquotient : ∀ member : space, equivalence member - member ∈ subspace) :
    ((equivalence : Module.End field space) - LinearMap.id) ^ 2 = 0 := by
  apply LinearMap.ext
  intro member
  rw [pow_two, Module.End.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
  have heq : equivalence (equivalence member - member) = equivalence member - member :=
    hfixed _ (hquotient member)
  change equivalence (equivalence member - member) - (equivalence member - member) = 0
  rw [heq, sub_self]

theorem linear_subspace_quotient_kernel_isPGroup {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) [CharP field prime] (action : actor →* (space ≃ₗ[field] space))
    (hinjective : Function.Injective action) (subspace : Submodule field space)
    (hinvariant : ∀ member : actor, subspace.map (action member : Module.End field space) = subspace) :
    IsPGroup prime ((linearSubspaceAction action subspace hinvariant).prod
      (linearQuotientAction action subspace hinvariant)).ker := by
  let restriction := linearSubspaceAction action subspace hinvariant
  let quotient := linearQuotientAction action subspace hinvariant
  apply IsPGroup.of_exponent_dvd_pow (n := 1)
  rw [pow_one]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro member
  have hproduct := MonoidHom.mem_ker.mp member.property
  have hrestriction : restriction member = 1 := congrArg Prod.fst hproduct
  have hquotient : quotient member = 1 := congrArg Prod.snd hproduct
  have hfixed : ∀ element ∈ subspace, action member element = element := by
    intro element helement
    have heq := DFunLike.congr_fun hrestriction (⟨element, helement⟩ : subspace)
    have hambient := congrArg (fun value : subspace => (value : space)) heq
    change ((linearSubspaceAction action subspace hinvariant member ⟨element, helement⟩ : subspace) : space) =
      element at hambient
    rw [linearSubspaceAction_apply] at hambient
    exact hambient
  have hquotientMem : ∀ element : space, action member element - element ∈ subspace := by
    intro element
    have heq := DFunLike.congr_fun hquotient (subspace.mkQ element)
    change linearQuotientAction action subspace hinvariant member (subspace.mkQ element) = subspace.mkQ element at heq
    rw [linearQuotientAction_apply, Submodule.mkQ_apply, Submodule.mkQ_apply] at heq
    exact (Submodule.Quotient.eq subspace).mp heq
  have hquadratic := quadratic_linear_of_fixed_subspace_quotient (action member) subspace hfixed hquotientMem
  apply Subtype.ext
  apply hinjective
  change action ((member : actor) ^ prime) = action 1
  rw [map_pow, map_one]
  exact quadratic_linear_pow_prime_eq_one prime (action member) hquadratic

theorem finite_pGroup_product {first : Type u} {second : Type v}
    [Group first] [Group second] [Finite first] [Finite second]
    (prime : ℕ) (hprime : prime.Prime) (hfirst : IsPGroup prime first)
    (hsecond : IsPGroup prime second) : IsPGroup prime (first × second) := by
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨firstDimension, hfirstCard⟩ := hfirst.exists_card_eq
  obtain ⟨secondDimension, hsecondCard⟩ := hsecond.exists_card_eq
  apply IsPGroup.of_card (n := firstDimension + secondDimension)
  rw [Nat.card_prod, hfirstCard, hsecondCard, pow_add]

theorem faithful_linear_pGroup_of_subspace_quotient {actor : Type w} {field : Type u} {space : Type v}
    [Group actor] [Finite actor] [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (action : actor →* (space ≃ₗ[field] space)) (hinjective : Function.Injective action)
    (subspace : Submodule field space)
    (hinvariant : ∀ member : actor, subspace.map (action member : Module.End field space) = subspace)
    (hsubspace : IsPGroup prime (linearSubspaceAction action subspace hinvariant).range)
    (hquotient : IsPGroup prime (linearQuotientAction action subspace hinvariant).range) :
    IsPGroup prime actor := by
  let restriction := linearSubspaceAction action subspace hinvariant
  let quotient := linearQuotientAction action subspace hinvariant
  let combined := restriction.rangeRestrict.prod quotient.rangeRestrict
  have : Finite restriction.range := Finite.of_surjective restriction.rangeRestrict restriction.rangeRestrict_surjective
  have : Finite quotient.range := Finite.of_surjective quotient.rangeRestrict quotient.rangeRestrict_surjective
  have htarget := finite_pGroup_product prime hprime hsubspace hquotient
  have hkernelEq : combined.ker = (restriction.prod quotient).ker := by
    ext member
    constructor
    · intro hmember
      apply MonoidHom.mem_ker.mpr
      apply Prod.ext
      · exact congrArg (fun value => (value.1 : subspace ≃ₗ[field] subspace))
          (MonoidHom.mem_ker.mp hmember)
      · exact congrArg (fun value => (value.2 : (space ⧸ subspace) ≃ₗ[field] (space ⧸ subspace)))
          (MonoidHom.mem_ker.mp hmember)
    · intro hmember
      apply MonoidHom.mem_ker.mpr
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst (MonoidHom.mem_ker.mp hmember)
      · apply Subtype.ext
        exact congrArg Prod.snd (MonoidHom.mem_ker.mp hmember)
  have hkernel : IsPGroup prime combined.ker := by
    apply (linear_subspace_quotient_kernel_isPGroup prime action hinjective subspace hinvariant).of_equiv
    exact MulEquiv.subgroupCongr hkernelEq.symm
  exact pGroup_of_pKernel_pRange prime combined hkernel (htarget.to_subgroup combined.range)

end CFSG.RankThreeEvenClassification.Helpers
