module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6LocalAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Field
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.OuterAutomorphisms OuterFourInAux

namespace E6LocalAux

section Model


theorem exists_twE6_model {Q : Type} [Group Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (2 ^ 3) ^ 2 ∧
      (∀ c, σ c = c ^ (2 ^ 3)) ∧ Nonempty (Q ≃* twistedE6RootGroup K σ) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hQ
  cases d with
  | twistedE6 q =>
    obtain ⟨K, fK, σ, hK, hσ, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hq : q.p ^ q.exponent = 2 ^ 3 := by rw [hd.1, hd.2]
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    exact ⟨K, fK, inferInstance, σ, by rw [hK, hq], fun c => by rw [hσ, hq], ⟨e.trans eC⟩⟩
  | _ => exact hd.elim

theorem card_eq_ordTwistedE6 {Q : Type} [Group Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)) : Nat.card Q = ordTwistedE6 8 := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twE6_model hQ
  rw [Nat.card_congr e.toEquiv,
    CFSG.LieType.SeitzGeneration.ExcHighThree.card_twistedE6RootGroup_eq (ℓ := 2) (f := 3)
      Nat.prime_two (by norm_num) σ hK hσ]
  norm_num

theorem outer_sq_eq_one_of_coprime {S : Type} [Group S]
    (hS : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∀ x : Outer S, Nat.Coprime 3 (orderOf x) →
      x ^ 2 = 1 := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twE6_model hS
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two
      (by norm_num : 1 ≤ 3) K hK σ hσ
  let u : MulAut S →* RingAut K := Θ.comp (MulAut.congr e).toMonoidHom
  have hK6 : Nat.card K = 2 ^ 6 := by rw [hK]; norm_num
  have hR : ∀ r : RingAut K, r ^ 6 = 1 := by
    intro r
    have := pow_card_eq_one' (G := RingAut K) (x := r)
    rwa [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK6).1]
      at this
  have hI : inner S ≤ u.ker := by
    rintro _ ⟨s, rfl⟩
    rw [MonoidHom.mem_ker]
    change Θ (MulAut.congr e (MulAut.conj s)) = 1
    rw [congr_conj_apply e s]
    have hmem : MulAut.conj (e s) ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ :=
      Subgroup.mem_sup_left ⟨e s, rfl⟩
    rw [← hker] at hmem
    exact MonoidHom.mem_ker.1 hmem
  have hN : ∀ g ∈ u.ker, g ^ 3 ∈ inner S := by
    intro g hg
    have hg' : MulAut.congr e g ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker]
      exact hg
    have h1 := hcube (QuotientGroup.mk ⟨MulAut.congr e g, hg'⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨e.symm c, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj_apply, MulEquiv.apply_symm_apply, map_pow]
    exact hc
  intro x hx
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : α ^ orderOf (QuotientGroup.mk α : Outer S) ∈ inner S := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  have h2 := sq_mem_of_pow_mem_of_hom u hI hR hN hx h1
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 h2

end Model

section FieldCore


theorem fieldCoreAt_of_fieldAutTwE6 {S : Type} [Group S] {φ : MulAut S} (hφ3 : φ ^ 3 = 1)
    (hφ : FieldAutTwE6 S φ) : FieldCoreAt 3 φ := by
  obtain ⟨K, _, _, σE, eC, η, γ, hK, hσE, hη1, hηodd, hγ⟩ := fieldAutTwE6_model hφ
  have hK' : Nat.card K = 2 ^ (2 * 3) := by rw [hK]; norm_num
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two
      (by norm_num : 1 ≤ 3) K hK σE hσE
  have hx3 : (MulAut.congr eC φ) ^ 3 = 1 := by rw [← map_pow, hφ3, map_one]
  have hxo : MulAut.congr eC φ ∉ twistedE6Inn K σE ⊔ twistedE6Diag K σE := by
    intro hmem
    rw [← hker, MonoidHom.mem_ker] at hmem
    have h1 : Θ (fieldActor σE η) = η := hΘ _ 1 1 η (by rw [map_one, map_one, one_mul, one_mul])
    have h2 : Θ (fieldActor σE η) = 1 := by
      rw [← hγ, map_mul, map_mul, map_inv, hmem]
      group
    exact hη1 (h1.symm.trans h2)
  have hfc : FieldCoreAt 3 (MulAut.congr eC φ) :=
    fieldCoreAt_twistedE6_of_not_mem_inndiag Nat.prime_two (by norm_num) (by norm_num) K hK' σE
      hσE hx3 hxo
  have hfc' := FieldCoreAt.congr hfc eC.symm
  rwa [congr_symm_congr] at hfc'

end FieldCore

end E6LocalAux

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
