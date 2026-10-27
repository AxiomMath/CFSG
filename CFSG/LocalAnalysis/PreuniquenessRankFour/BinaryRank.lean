module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSymplectic

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v w

theorem binary_prime_order_at_least_two
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) :
    2 ≤ orderOf (2 : ZMod prime) := by
  have hnonzero : (2 : ZMod prime) ≠ 0 := by
    intro hzero
    have hdivides := (ZMod.natCast_eq_zero_iff 2 prime).mp hzero
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdivides with hone | htwo
    · exact (Fact.out : prime.Prime).ne_one hone
    · exact hodd htwo
  have hpositive : 0 < orderOf (2 : ZMod prime) :=
    orderOf_pos_iff.mpr (isUnit_iff_ne_zero.mpr hnonzero).isOfFinOrder
  have hnotOne : orderOf (2 : ZMod prime) ≠ 1 := by
    intro hone
    have hequal : (2 : ZMod prime) = 1 := (orderOf_eq_one_iff (x := (2 : ZMod prime))).mp hone
    have hcast : ((1 : ℕ) : ZMod prime) = ((2 : ℕ) : ZMod prime) := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using hequal.symm
    have hcongruence := (ZMod.natCast_eq_natCast_iff 1 2 prime).mp hcast
    have hdivides := (Nat.modEq_iff_dvd' (by omega : 1 ≤ 2)).mp hcongruence
    norm_num at hdivides
    exact (Fact.out : prime.Prime).ne_one hdivides
  omega

theorem binary_prime_order_eq_two_forces_prime_three
    (prime : ℕ) [Fact prime.Prime] (horder : orderOf (2 : ZMod prime) = 2) : prime = 3 := by
  have hequal := pow_orderOf_eq_one (2 : ZMod prime)
  rw [horder] at hequal
  have hcast : ((1 : ℕ) : ZMod prime) = ((4 : ℕ) : ZMod prime) := by
    norm_num at hequal ⊢
    exact hequal.symm
  have hcongruence := (ZMod.natCast_eq_natCast_iff 1 4 prime).mp hcast
  have hdivides := (Nat.modEq_iff_dvd' (by omega : 1 ≤ 4)).mp hcongruence
  norm_num at hdivides
  exact ((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdivides).resolve_left
    (Fact.out : prime.Prime).ne_one

theorem binary_prime_order_at_least_three_of_ne_three
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) (hthree : prime ≠ 3) :
    3 ≤ orderOf (2 : ZMod prime) := by
  have hminimum := binary_prime_order_at_least_two prime hodd
  have hnotTwo : orderOf (2 : ZMod prime) ≠ 2 :=
    fun hequal => hthree (binary_prime_order_eq_two_forces_prime_three prime hequal)
  omega

theorem simple_commutative_binary_module_prime_kernel_order_cost
    {coefficient : Type u} {space : Type v} {acting : Type w}
    [CommRing coefficient] [AddCommGroup space] [Module coefficient space]
    [IsSimpleModule coefficient space] [Finite space]
    [Module (ZMod 2) space] [Group acting] [Finite acting]
    (prime : ℕ) [Fact prime.Prime]
    (hom : acting →* coefficient) (hpow : ∀ scalar : acting, scalar ^ prime = 1) :
    ∃ kernel : Subgroup acting, kernel.Normal ∧
      (kernel.index = 1 ∨ kernel.index = prime) ∧
        (kernel.index = prime → orderOf (2 : ZMod prime) ≤ Module.finrank (ZMod 2) space) ∧
          ∀ scalar ∈ kernel, ∀ member : space, hom scalar • member = member := by
  obtain ⟨ideal, hideal, ⟨equivalence⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule coefficient space)
  let : ideal.IsMaximal := hideal
  let : Field (coefficient ⧸ ideal) := Ideal.Quotient.field ideal
  let : Finite (coefficient ⧸ ideal) := Finite.of_equiv space equivalence.toEquiv
  let unitHom := ((Ideal.Quotient.mk ideal).toMonoidHom.comp hom).toHomUnits
  have hindex : unitHom.ker.index = Nat.card unitHom.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange unitHom).toEquiv
  let : IsCyclic unitHom.range := inferInstance
  have hdivides : Nat.card unitHom.range ∣ prime := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro member
    obtain ⟨scalar, hscalar⟩ := member.property
    apply Subtype.ext
    change member.val ^ prime = 1
    rw [← hscalar, ← map_pow, hpow, map_one]
  refine ⟨unitHom.ker, inferInstance, ?_, ?_, ?_⟩
  · rw [hindex]
    exact (Nat.dvd_prime Fact.out).mp hdivides
  · intro hlarge
    have hspaceCard : Nat.card space = 2 ^ Module.finrank (ZMod 2) space := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := space))
    have hprimeDivides : prime ∣ 2 ^ Module.finrank (ZMod 2) space - 1 := by
      have hdividesUnits := unitHom.range.card_subgroup_dvd_card
      rw [← hindex, hlarge, Nat.card_units, ← Nat.card_congr equivalence.toEquiv, hspaceCard] at hdividesUnits
      exact hdividesUnits
    have hcongruence : 1 ≡ 2 ^ Module.finrank (ZMod 2) space [MOD prime] :=
      (Nat.modEq_iff_dvd' (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))).mpr hprimeDivides
    have hcast := (ZMod.natCast_eq_natCast_iff 1 (2 ^ Module.finrank (ZMod 2) space) prime).mpr hcongruence
    have hpower : (2 : ZMod prime) ^ Module.finrank (ZMod 2) space = 1 := by
      simpa only [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using hcast.symm
    exact orderOf_le_of_pow_eq_one
      (Module.finrank_pos_iff.mpr (IsSimpleModule.nontrivial coefficient space)) hpower
  · intro scalar hscalar member
    apply equivalence.injective
    rw [map_smul]
    have hquotient : (Ideal.Quotient.mk ideal) (hom scalar) = 1 := congrArg Units.val hscalar
    change (Ideal.Quotient.mk ideal) (hom scalar) * equivalence member = equivalence member
    rw [hquotient, one_mul]

theorem simple_commutative_binary_module_prime_kernel_cost
    {coefficient : Type u} {space : Type v} {acting : Type w}
    [CommRing coefficient] [AddCommGroup space] [Module coefficient space]
    [IsSimpleModule coefficient space] [Finite space]
    [Module (ZMod 2) space] [Group acting] [Finite acting]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hom : acting →* coefficient) (hpow : ∀ scalar : acting, scalar ^ prime = 1) :
    ∃ kernel : Subgroup acting, kernel.Normal ∧
      (kernel.index = 1 ∨ kernel.index = prime) ∧
        (kernel.index = prime → 2 ≤ Module.finrank (ZMod 2) space) ∧
          ∀ scalar ∈ kernel, ∀ member : space, hom scalar • member = member := by
  obtain ⟨ideal, hideal, ⟨equivalence⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule coefficient space)
  let : ideal.IsMaximal := hideal
  let : Field (coefficient ⧸ ideal) := Ideal.Quotient.field ideal
  let : Finite (coefficient ⧸ ideal) := Finite.of_equiv space equivalence.toEquiv
  let unitHom := ((Ideal.Quotient.mk ideal).toMonoidHom.comp hom).toHomUnits
  have hindex : unitHom.ker.index = Nat.card unitHom.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange unitHom).toEquiv
  let : IsCyclic unitHom.range := inferInstance
  have hdivides : Nat.card unitHom.range ∣ prime := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro member
    obtain ⟨scalar, hscalar⟩ := member.property
    apply Subtype.ext
    change member.val ^ prime = 1
    rw [← hscalar, ← map_pow, hpow, map_one]
  refine ⟨unitHom.ker, inferInstance, ?_, ?_, ?_⟩
  · rw [hindex]
    exact (Nat.dvd_prime Fact.out).mp hdivides
  · intro hlarge
    have hbound : prime ≤ Nat.card space - 1 := by
      rw [hindex] at hlarge
      have hcardLe := Nat.card_le_card_of_injective unitHom.range.subtype Subtype.val_injective
      rw [Nat.card_units, ← Nat.card_congr equivalence.toEquiv, hlarge] at hcardLe
      exact hcardLe
    have hspaceCard : Nat.card space = 2 ^ Module.finrank (ZMod 2) space := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := space))
    have hprimeLarge : 3 ≤ prime := by have := (Fact.out : prime.Prime).two_le; omega
    by_contra hsmall
    have hdimension : Module.finrank (ZMod 2) space = 0 ∨ Module.finrank (ZMod 2) space = 1 := by omega
    rcases hdimension with hzero | hone
    · rw [hzero] at hspaceCard
      norm_num at hspaceCard
      omega
    · rw [hone] at hspaceCard
      norm_num at hspaceCard
      omega
  · intro scalar hscalar member
    apply equivalence.injective
    rw [map_smul]
    have hquotient : (Ideal.Quotient.mk ideal) (hom scalar) = 1 := congrArg Units.val hscalar
    change (Ideal.Quotient.mk ideal) (hom scalar) * equivalence member = equivalence member
    rw [hquotient, one_mul]

theorem separating_prime_index_kernels_with_cost
    {acting : Type u} {index : Type v} [Group acting] [Finite acting] [Fintype index]
    (prime rank perKernel : ℕ) (hprime : prime.Prime) (hcard : Nat.card acting = prime ^ rank)
    (kernel : index → Subgroup acting) [∀ position, (kernel position).Normal]
    (cost : index → ℕ)
    (hindex : ∀ position, (kernel position).index = 1 ∨ (kernel position).index = prime)
    (hcost : ∀ position, (kernel position).index = prime → perKernel ≤ cost position)
    (hseparating : ∀ scalar : acting, (∀ position, scalar ∈ kernel position) → scalar = 1) :
    perKernel * rank ≤ ∑ position, cost position := by
  classical
  let width : index → ℕ := fun position => if (kernel position).index = prime then 1 else 0
  have hwidthIndex : ∀ position, (kernel position).index = prime ^ width position := by
    intro position
    rcases hindex position with hone | hprimeIndex
    · have hnot : (kernel position).index ≠ prime := by rw [hone]; exact hprime.ne_one.symm
      change (kernel position).index = prime ^ (if (kernel position).index = prime then 1 else 0)
      rw [ite_eq_right hnot, pow_zero, hone]
    · simp only [width, hprimeIndex, ↓reduceIte, pow_one]
  let hom : acting →* ((position : index) → acting ⧸ kernel position) :=
    MonoidHom.pi fun position => QuotientGroup.mk' (kernel position)
  have hinjective : Function.Injective hom := by
    apply hom.ker_eq_bot_iff.mp
    apply (Subgroup.eq_bot_iff_forall hom.ker).mpr
    intro scalar hscalar
    apply hseparating
    intro position
    have hequal := congrArg (fun member => member position) (show hom scalar = 1 from hscalar)
    exact (QuotientGroup.eq_one_iff scalar).mp hequal
  have hcardLe := Nat.card_le_card_of_injective hom hinjective
  rw [hcard, Nat.card_pi] at hcardLe
  have hquotientCard : ∀ position, Nat.card (acting ⧸ kernel position) = prime ^ width position :=
    fun position => (kernel position).index_eq_card.symm.trans (hwidthIndex position)
  simp only [hquotientCard, Finset.prod_pow_eq_pow_sum] at hcardLe
  have hrankLe : rank ≤ ∑ position, width position := (pow_le_pow_iff_right₀ hprime.one_lt).mp hcardLe
  have hcostLe : ∀ position, perKernel * width position ≤ cost position := by
    intro position
    by_cases hlarge : (kernel position).index = prime
    · simpa only [width, hlarge, ↓reduceIte, mul_one] using hcost position hlarge
    · simp only [width, hlarge, ↓reduceIte, mul_zero, zero_le]
  calc
    perKernel * rank ≤ perKernel * ∑ position, width position := Nat.mul_le_mul_left perKernel hrankLe
    _ = ∑ position, perKernel * width position := Finset.mul_sum _ _ _
    _ ≤ ∑ position, cost position := Finset.sum_le_sum fun position _ => hcostLe position

theorem separating_prime_index_kernels_dimension_cost
    {acting : Type u} {index : Type v} [Group acting] [Finite acting] [Fintype index]
    (prime rank : ℕ) (hprime : prime.Prime) (hcard : Nat.card acting = prime ^ rank)
    (kernel : index → Subgroup acting) [∀ position, (kernel position).Normal]
    (cost : index → ℕ)
    (hindex : ∀ position, (kernel position).index = 1 ∨ (kernel position).index = prime)
    (hcost : ∀ position, (kernel position).index = prime → 2 ≤ cost position)
    (hseparating : ∀ scalar : acting, (∀ position, scalar ∈ kernel position) → scalar = 1) :
    2 * rank ≤ ∑ position, cost position := by
  exact separating_prime_index_kernels_with_cost prime rank 2 hprime hcard kernel cost hindex hcost hseparating

theorem faithful_binary_elementary_representation_order_dimension_bound
    {acting : Type u} {space : Type v}
    [CommGroup acting] [Finite acting] [AddCommGroup space] [Finite space]
    [Module (ZMod 2) space] [NeZero (Nat.card acting : ZMod 2)]
    (prime rank : ℕ) [Fact prime.Prime]
    (hcard : Nat.card acting = prime ^ rank)
    (representation : Representation (ZMod 2) acting space)
    (hpow : ∀ scalar : acting, scalar ^ prime = 1)
    (hfaithful : Function.Injective representation) :
    orderOf (2 : ZMod prime) * rank ≤ Module.finrank (ZMod 2) space := by
  classical
  let : Finite representation.asModule :=
    Finite.of_equiv space representation.asModuleEquiv.symm.toEquiv
  obtain ⟨count, summand, decomposition, hsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp
      (MonoidAlgebra (ZMod 2) acting) representation.asModule
  let : ∀ position, IsSimpleModule (MonoidAlgebra (ZMod 2) acting) (summand position) := hsimple
  have hsummand : ∀ position : Fin count,
      ∃ kernel : Subgroup acting, kernel.Normal ∧
        (kernel.index = 1 ∨ kernel.index = prime) ∧
          (kernel.index = prime → orderOf (2 : ZMod prime) ≤ Module.finrank (ZMod 2) (summand position)) ∧
            ∀ scalar ∈ kernel, ∀ member : summand position,
              (MonoidAlgebra.of (ZMod 2) acting) scalar • member = member := by
    intro position
    exact simple_commutative_binary_module_prime_kernel_order_cost
      (space := summand position) prime (MonoidAlgebra.of (ZMod 2) acting) hpow
  choose kernel hnormal hindex hcost hfixed using hsummand
  let : ∀ position, (kernel position).Normal := hnormal
  have hseparating : ∀ scalar : acting, (∀ position, scalar ∈ kernel position) → scalar = 1 := by
    intro scalar hscalar
    have hwholeFixed : ∀ member : representation.asModule,
        (MonoidAlgebra.of (ZMod 2) acting) scalar • member = member := by
      intro member
      apply decomposition.injective
      rw [map_smul]
      apply DFinsupp.ext
      intro position
      exact hfixed position scalar (hscalar position) (decomposition member position)
    apply hfaithful
    rw [map_one]
    apply LinearMap.ext
    intro member
    change representation scalar member = member
    have hequal := congrArg representation.asModuleEquiv
      (hwholeFixed (representation.asModuleEquiv.symm member))
    simpa only [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of,
      LinearEquiv.apply_symm_apply] using hequal
  have hrankBound := separating_prime_index_kernels_with_cost prime rank (orderOf (2 : ZMod prime)) Fact.out hcard
    kernel (fun position => Module.finrank (ZMod 2) (summand position)) hindex hcost hseparating
  have hdimension : Module.finrank (ZMod 2) space =
      ∑ position, Module.finrank (ZMod 2) (summand position) := by
    let equiv : space ≃ₗ[ZMod 2] ((position : Fin count) → summand position) :=
      representation.asModuleEquiv.symm.trans
        ((decomposition.restrictScalars (ZMod 2)).trans DFinsupp.linearEquivFunOnFintype)
    rw [equiv.finrank_eq, Module.finrank_pi_fintype]
  rw [hdimension]
  exact hrankBound

theorem faithful_binary_elementary_representation_dimension_bound
    {acting : Type u} {space : Type v}
    [CommGroup acting] [Finite acting] [AddCommGroup space] [Finite space]
    [Module (ZMod 2) space] [NeZero (Nat.card acting : ZMod 2)]
    (prime rank : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hcard : Nat.card acting = prime ^ rank)
    (representation : Representation (ZMod 2) acting space)
    (hpow : ∀ scalar : acting, scalar ^ prime = 1)
    (hfaithful : Function.Injective representation) :
    2 * rank ≤ Module.finrank (ZMod 2) space := by
  exact (Nat.mul_le_mul_right rank (binary_prime_order_at_least_two prime hodd)).trans
    (faithful_binary_elementary_representation_order_dimension_bound prime rank hcard representation hpow hfaithful)

theorem faithful_binary_elementary_linear_action_order_dimension_bound
    {acting : Type u} {space : Type v}
    [CommGroup acting] [Finite acting] [AddCommGroup space] [Finite space] [Module (ZMod 2) space]
    (prime rank : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hcard : Nat.card acting = prime ^ rank) (hpow : ∀ scalar : acting, scalar ^ prime = 1)
    (embedding : acting →* (space ≃ₗ[ZMod 2] space)) (hfaithful : Function.Injective embedding) :
    orderOf (2 : ZMod prime) * rank ≤ Module.finrank (ZMod 2) space := by
  let : NeZero (Nat.card acting : ZMod 2) := by
    constructor
    intro hzero
    have hdivides := (ZMod.natCast_eq_zero_iff (Nat.card acting) 2).mp hzero
    rw [hcard] at hdivides
    have hcoprime : Nat.Coprime 2 (prime ^ rank) := by
      simpa only [pow_one] using Nat.coprime_pow_primes 1 rank (by norm_num) Fact.out hodd.symm
    exact (show Nat.Prime 2 by norm_num).coprime_iff_not_dvd.mp hcoprime hdivides
  let representation : Representation (ZMod 2) acting space :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp embedding
  have hrepresentationFaithful : Function.Injective representation :=
    LinearEquiv.toLinearMap_injective.comp hfaithful
  exact faithful_binary_elementary_representation_order_dimension_bound prime rank hcard
    representation hpow hrepresentationFaithful

theorem faithful_binary_elementary_linear_action_dimension_bound
    {acting : Type u} {space : Type v}
    [CommGroup acting] [Finite acting] [AddCommGroup space] [Finite space] [Module (ZMod 2) space]
    (prime rank : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hcard : Nat.card acting = prime ^ rank) (hpow : ∀ scalar : acting, scalar ^ prime = 1)
    (embedding : acting →* (space ≃ₗ[ZMod 2] space)) (hfaithful : Function.Injective embedding) :
    2 * rank ≤ Module.finrank (ZMod 2) space := by
  exact (Nat.mul_le_mul_right rank (binary_prime_order_at_least_two prime hodd)).trans
    (faithful_binary_elementary_linear_action_order_dimension_bound prime rank hodd hcard hpow embedding hfaithful)

theorem faithful_binary_multiplicative_action_order_rank_bound
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [CommGroup source] [Finite source]
    [MulDistribMulAction acting source] [Module (ZMod 2) (Additive source)]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    orderOf (2 : ZMod prime) * pRank prime (⊤ : Subgroup acting) ≤
      Module.finrank (ZMod 2) (Additive source) := by
  obtain ⟨elementary, _, helementary, hcard⟩ := pRank_attained prime Fact.out (⊤ : Subgroup acting)
  let : IsMulCommutative elementary := helementary.1
  let : CommGroup elementary := IsMulCommutative.instCommGroup
  have helementaryFaithful : Function.Injective (MulDistribMulAction.toMulAut elementary source) := by
    intro first second hequal
    apply Subtype.ext
    apply hfaithful
    apply MulEquiv.ext
    intro member
    exact congrArg (fun equivalence : MulAut source => equivalence member) hequal
  exact faithful_binary_elementary_linear_action_order_dimension_bound prime _ hodd hcard
    (fun scalar => Subtype.ext (helementary.2 scalar scalar.property))
    (multiplicative_action_zmod_linear_aut (acting := elementary) (source := source) 2)
    (faithful_multiplicative_action_zmod_linear_aut 2 helementaryFaithful)

theorem faithful_binary_multiplicative_action_rank_bound
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [CommGroup source] [Finite source]
    [MulDistribMulAction acting source] [Module (ZMod 2) (Additive source)]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    2 * pRank prime (⊤ : Subgroup acting) ≤ Module.finrank (ZMod 2) (Additive source) := by
  exact (Nat.mul_le_mul_right _ (binary_prime_order_at_least_two prime hodd)).trans
    (faithful_binary_multiplicative_action_order_rank_bound prime hodd hfaithful)

@[instance_reducible]
def pGroup_binary_frattini_quotient_module
    {source : Type u} [Group source] [Finite source] (hsource : IsPGroup 2 source) :
    letI : IsMulCommutative (source ⧸ frattini source) := pGroup_frattini_quotient_isMulCommutative 2 hsource
    letI : CommGroup (source ⧸ frattini source) := IsMulCommutative.instCommGroup
    Module (ZMod 2) (Additive (source ⧸ frattini source)) := by
  let : IsMulCommutative (source ⧸ frattini source) := pGroup_frattini_quotient_isMulCommutative 2 hsource
  let : CommGroup (source ⧸ frattini source) := IsMulCommutative.instCommGroup
  exact AddCommGroup.zmodModule (n := 2) (G := Additive (source ⧸ frattini source)) fun member => by
    change Additive.ofMul (member.toMul ^ 2) = 0
    rw [pGroup_frattini_quotient_pow_eq_one 2 hsource]
    rfl

theorem local_twoCore_frattini_order_dimension_bound
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup) :
    letI : IsMulCommutative (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) :=
      pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 localGroup)
    letI : CommGroup (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) := IsMulCommutative.instCommGroup
    letI := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 localGroup)
    orderOf (2 : ZMod prime) * pRank prime localGroup ≤
      Module.finrank (ZMod 2) (Additive (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup))) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsMulCommutative (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) :=
    pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 localGroup)
  let : CommGroup (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 localGroup)
  obtain ⟨elementary, hcontained, helementary, hcard⟩ := pRank_attained prime hprime localGroup
  let : IsMulCommutative elementary := helementary.1
  let : CommGroup elementary := IsMulCommutative.instCommGroup
  have hgroup : IsPGroup prime elementary := IsPGroup.of_card hcard
  let : MulDistribMulAction elementary (pCoreOf 2 localGroup) :=
    MulDistribMulAction.compHom (pCoreOf 2 localGroup)
      (((pCoreOf 2 localGroup).normalizerMonoidHom).comp
        (Subgroup.inclusion (hcontained.trans (subgroup_normalizes_pCoreOf 2 localGroup))))
  let := characteristic_quotient_mulDistribMulAction (acting := elementary) (frattini (pCoreOf 2 localGroup))
  have hfaithful := odd_pSubgroup_twoCore_frattini_action_injective
    prime hprime hodd hchar hgroup hcontained hlocal
  exact faithful_binary_elementary_linear_action_order_dimension_bound prime _ hodd hcard
    (fun scalar => Subtype.ext (helementary.2 scalar scalar.property))
    (multiplicative_action_zmod_linear_aut
      (acting := elementary) (source := pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) 2)
    (faithful_multiplicative_action_zmod_linear_aut 2 hfaithful)

theorem local_twoCore_frattini_dimension_bound
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup) :
    letI : IsMulCommutative (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) :=
      pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 localGroup)
    letI : CommGroup (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) := IsMulCommutative.instCommGroup
    letI := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 localGroup)
    2 * pRank prime localGroup ≤
      Module.finrank (ZMod 2) (Additive (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup))) := by
  let : Fact prime.Prime := ⟨hprime⟩
  exact (Nat.mul_le_mul_right _ (binary_prime_order_at_least_two prime hodd)).trans
    (local_twoCore_frattini_order_dimension_bound prime hprime hodd hchar localGroup hlocal)

theorem rank_four_local_small_frattini_dimension_forces_prime_three
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup)
    (hrank : 4 ≤ pRank prime localGroup) :
    letI : IsMulCommutative (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) :=
      pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 localGroup)
    letI : CommGroup (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) := IsMulCommutative.instCommGroup
    letI := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 localGroup)
    Module.finrank (ZMod 2) (Additive (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup))) ≤ 11 →
      prime = 3 := by
  let : Fact prime.Prime := ⟨hprime⟩
  intro hdimension
  by_contra hthree
  have hminimum := binary_prime_order_at_least_three_of_ne_three prime hodd hthree
  have hcost := local_twoCore_frattini_order_dimension_bound prime hprime hodd hchar localGroup hlocal
  have hlower : 3 * 4 ≤ orderOf (2 : ZMod prime) * pRank prime localGroup :=
    Nat.mul_le_mul hminimum hrank
  omega

theorem local_twoCore_frattini_cardinality_bound
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup) :
    2 ^ (2 * pRank prime localGroup) ≤
      Nat.card (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) := by
  let : IsMulCommutative (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) :=
    pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 localGroup)
  let : CommGroup (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 localGroup)
  have hdimension := local_twoCore_frattini_dimension_bound prime hprime hodd hchar localGroup hlocal
  have hcard : Nat.card (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) =
      2 ^ Module.finrank (ZMod 2) (Additive (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup))) := by
    rw [Nat.card_congr (Additive.ofMul :
      (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup)) ≃
        Additive (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup))),
      Module.natCard_eq_pow_finrank (K := ZMod 2)]
    congr 1
    exact (Nat.card_eq_fintype_card.trans (ZMod.card 2))
  rw [hcard]
  exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hdimension

theorem local_twoCore_cardinality_bound
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup) :
    2 ^ (2 * pRank prime localGroup) ≤ Nat.card (pCoreOf 2 localGroup) := by
  apply (local_twoCore_frattini_cardinality_bound prime hprime hodd hchar localGroup hlocal).trans
  exact Nat.le_of_dvd Nat.card_pos (frattini (pCoreOf 2 localGroup)).card_quotient_dvd_card

theorem rank_four_local_twoCore_cardinality_at_least_256
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient) (localGroup : Subgroup ambient) (hlocal : IsTwoLocal localGroup)
    (hrank : 4 ≤ pRank prime localGroup) : 256 ≤ Nat.card (pCoreOf 2 localGroup) := by
  have hpower : 2 ^ (2 * 4) ≤ 2 ^ (2 * pRank prime localGroup) :=
    pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (Nat.mul_le_mul_left 2 hrank)
  have hminimum : 256 ≤ 2 ^ (2 * pRank prime localGroup) := by norm_num at hpower ⊢; exact hpower
  exact hminimum.trans
    (local_twoCore_cardinality_bound prime hprime hodd hchar localGroup hlocal)

theorem faithful_odd_action_cyclic_center_quotient_order_dimension_bound
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hacting : IsPGroup prime acting) (hsource : IsPGroup 2 source)
    (hcenter : IsCyclic (Subgroup.center source))
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    letI : IsMulCommutative (source ⧸ Subgroup.center source) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    letI := class_two_binary_center_quotient_module hsquares
    orderOf (2 : ZMod prime) * pRank prime (⊤ : Subgroup acting) ≤
      Module.finrank (ZMod 2) (Additive (source ⧸ Subgroup.center source)) := by
  let : IsMulCommutative (source ⧸ Subgroup.center source) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
  let : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
  let := class_two_binary_center_quotient_module hsquares
  let := characteristic_quotient_mulDistribMulAction (acting := acting) (Subgroup.center source)
  exact faithful_binary_multiplicative_action_order_rank_bound prime hodd
    (faithful_odd_pGroup_action_on_cyclic_center_quotient prime Fact.out hodd hacting hsource hcenter hfaithful)

theorem faithful_odd_action_cyclic_center_quotient_dimension_bound
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hacting : IsPGroup prime acting) (hsource : IsPGroup 2 source)
    (hcenter : IsCyclic (Subgroup.center source))
    (hcommutator : commutator source ≤ Subgroup.center source)
    (hsquares : ∀ member : source, member ^ 2 ∈ Subgroup.center source)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    letI : IsMulCommutative (source ⧸ Subgroup.center source) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
    letI : CommGroup (source ⧸ Subgroup.center source) := IsMulCommutative.instCommGroup
    letI := class_two_binary_center_quotient_module hsquares
    2 * pRank prime (⊤ : Subgroup acting) ≤
      Module.finrank (ZMod 2) (Additive (source ⧸ Subgroup.center source)) := by
  exact (Nat.mul_le_mul_right _ (binary_prime_order_at_least_two prime hodd)).trans
    (faithful_odd_action_cyclic_center_quotient_order_dimension_bound prime hodd hacting hsource hcenter
      hcommutator hsquares hfaithful)

theorem faithful_odd_action_critical_cyclic_center_quotient_dimension_bound
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (hacting : IsPGroup prime acting) (hsource : IsPGroup 2 source)
    (critical : Subgroup source) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hfrattini : (frattini critical).map critical.subtype ≤ (Subgroup.center critical).map critical.subtype)
    (hcenter : IsCyclic (Subgroup.center critical))
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    ∃ hcommutator : commutator critical ≤ Subgroup.center critical,
      ∃ hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical,
        letI : IsMulCommutative (critical ⧸ Subgroup.center critical) :=
          Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommutator
        letI : CommGroup (critical ⧸ Subgroup.center critical) := IsMulCommutative.instCommGroup
        letI := class_two_binary_center_quotient_module hsquares
        2 * pRank prime (⊤ : Subgroup acting) ≤
          Module.finrank (ZMod 2) (Additive (critical ⧸ Subgroup.center critical)) := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hfrattiniLocal : frattini critical ≤ Subgroup.center critical :=
    (Subgroup.map_le_map_iff_of_injective (f := critical.subtype) Subtype.val_injective).mp hfrattini
  have hcommutator : commutator critical ≤ Subgroup.center critical :=
    (pGroup_commutator_le_frattini 2 (hsource.to_subgroup critical)).trans hfrattiniLocal
  have hsquares : ∀ member : critical, member ^ 2 ∈ Subgroup.center critical :=
    fun member => hfrattiniLocal (pGroup_pow_mem_frattini 2 (hsource.to_subgroup critical) member)
  let := characteristic_subgroup_mulDistribMulAction (acting := acting) critical
  have hcriticalFaithful := faithful_coprime_pGroup_action_on_characteristic_critical_subgroup
    prime 2 hodd hacting hsource critical hcritical hfaithful
  refine ⟨hcommutator, hsquares, ?_⟩
  exact faithful_odd_action_cyclic_center_quotient_dimension_bound prime hodd hacting
    (hsource.to_subgroup critical) hcenter hcommutator hsquares hcriticalFaithful

theorem faithful_binary_linear_action_order_rank_bound
    {acting : Type u} {space : Type v}
    [Group acting] [Finite acting] [AddCommGroup space] [Finite space] [Module (ZMod 2) space]
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2)
    (embedding : acting →* (space ≃ₗ[ZMod 2] space)) (hinjective : Function.Injective embedding) :
    orderOf (2 : ZMod prime) * pRank prime (⊤ : Subgroup acting) ≤ Module.finrank (ZMod 2) space := by
  obtain ⟨elementary, _, helementary, hcard⟩ := pRank_attained prime Fact.out (⊤ : Subgroup acting)
  let : IsMulCommutative elementary := helementary.1
  let : CommGroup elementary := IsMulCommutative.instCommGroup
  exact faithful_binary_elementary_linear_action_order_dimension_bound prime _ hodd hcard
    (fun scalar => Subtype.ext (helementary.2 scalar scalar.property))
    (embedding.comp elementary.subtype) (hinjective.comp Subtype.val_injective)

end CFSG.PreuniquenessRankFour.Helpers
