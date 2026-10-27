module

public import CFSG.FeitThompson.Representations.NormalKernelLayerWeightedDegreeSum
public import CFSG.FeitThompson.Local.ChiefFactorIrreducibleModule
import CFSG.FeitThompson.Representations.LargeAbelianizationFrobeniusIsometryCoherence
import CFSG.FeitThompson.Local.NilpotentFrobeniusAbelianizationPrimePower
import CFSG.FeitThompson.Local.SmallFrobeniusCyclicKernel
import CFSG.FeitThompson.Representations.EqualDegreeFamilyCoherence
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Representations.AbelianNormalDetectingRestrictionSplit
import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInducedFamily

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open scoped Pointwise

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {H E : Subgroup L}

section Main

variable [H.Normal] [Group.IsNilpotent ↥H]
  (hodd : Odd (Nat.card L)) (hH : H ≠ ⊥)
  (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
  (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
  (τ : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H) →+ virtualChars G)
  (hτiso : ∀ f g : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H),
    cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
  (hτ1 : ∀ f : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H), (τ f : G → ℂ) 1 = 0)
  (hnc : ¬ IsCoherent (kerLayerIndFam (⊥ : Subgroup L) H) τ)

include hodd hH hmul hinf hC hτiso hτ1 hnc

theorem relIndex_commutator_self_le_of_not_isCoherent :
    (⁅H, H⁆ : Subgroup L).relIndex H ≤ 4 * Nat.card ↥E ^ 2 + 1 :=
  le_of_not_gt fun hlt => hnc
    (isCoherent_kerLayerIndFam_bot_of_lt_card_sq (E := E) hodd hH hmul hinf hC hlt τ hτiso hτ1)

theorem relIndex_commutator_self_le_index_sq_of_not_isCoherent :
    (⁅H, H⁆ : Subgroup L).relIndex H ≤ 4 * H.index ^ 2 + 1 := by
  rw [index_eq_natCard_of_isComplement'
    (isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf)]
  exact relIndex_commutator_self_le_of_not_isCoherent hodd hH hmul hinf hC τ hτiso hτ1 hnc

omit hodd [Group.IsNilpotent ↥H] in
theorem not_isMulCommutative_of_not_isCoherent : ¬ IsMulCommutative ↥H := fun hab => by
  have := hab
  refine hnc (isCoherent_of_forall_apply_one_eq (d := (Nat.card ↥E : ℂ))
    finite_kerLayerIndFam
    (kerLayerIndFam_subset_Irr_of_frobenius (E := E) ⊥ hH hmul hinf hC) ?_ τ hτiso hτ1)
  intro χ hχ
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hχ
  obtain ⟨hθIrr, -, -⟩ := mem_kerLayerIrr.1 hθ
  exact indClassFun_one_eq_card (isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf)
    (Irr.apply_one_eq_one_of_isMulCommutative hθIrr)

theorem nontrivial_quotientFactor_commutator_self_of_not_isCoherent :
    Nontrivial ↥(quotientFactor H ⁅H, H⁆) :=
  nontrivial_quotientFactor_commutator_self (E := E) hodd hH hC
    (relIndex_commutator_self_le_of_not_isCoherent hodd hH hmul hinf hC τ hτiso hτ1 hnc)

theorem eq_bot_of_normal_lt_quotientFactor_commutator_self_of_not_isCoherent
    (K : Subgroup (L ⧸ ⁅H, H⁆)) (hK : K.Normal) (hKlt : K < quotientFactor H ⁅H, H⁆) : K = ⊥ :=
  eq_bot_of_normal_lt_quotientFactor_commutator_self (E := E) hodd hH hC
    (relIndex_commutator_self_le_of_not_isCoherent hodd hH hmul hinf hC τ hτiso hτ1 hnc) K hK hKlt

theorem exists_prime_pow_natCard_not_dvd_sub_one_of_not_isCoherent :
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥H = p ^ a ∧
      Nonempty (↥(quotientFactor H ⁅H, H⁆) ≃* Multiplicative (Fin d → ZMod p)) ∧
      ¬ Nat.card ↥E ∣ p - 1 := by
  have hbd := relIndex_commutator_self_le_of_not_isCoherent hodd hH hmul hinf hC τ hτiso hτ1 hnc
  obtain ⟨p, a, d, hp, ha, hd, hcard, he⟩ :=
    exists_prime_pow_natCard_nonempty_mulEquiv_quotientFactor_commutator_self
      (E := E) hodd hH hC hbd
  refine ⟨p, a, d, hp, ha, hd, hcard, he, fun hdvd => ?_⟩
  have hpH : p ∣ Nat.card ↥H := hcard ▸ dvd_pow_self p (by omega)
  have : IsCyclic ↥H :=
    isCyclic_of_relIndex_commutator_self_le_of_prime_dvd (E := E) hodd hH hC hp hpH hbd hdvd
  exact not_isMulCommutative_of_not_isCoherent hH hmul hinf hC τ hτiso hτ1 hnc
    IsCyclic.isMulCommutative

theorem obstruction_of_not_isCoherent_kerLayerIndFam :
    (Nontrivial ↥(quotientFactor H ⁅H, H⁆) ∧
      ∀ K : Subgroup (L ⧸ ⁅H, H⁆), K.Normal → K < quotientFactor H ⁅H, H⁆ → K = ⊥) ∧
    (⁅H, H⁆ : Subgroup L).relIndex H ≤ 4 * Nat.card ↥E ^ 2 + 1 ∧
    ¬ IsMulCommutative ↥H ∧
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥H = p ^ a ∧
      Nonempty (↥(quotientFactor H ⁅H, H⁆) ≃* Multiplicative (Fin d → ZMod p)) ∧
      ¬ Nat.card ↥E ∣ p - 1 :=
  ⟨⟨nontrivial_quotientFactor_commutator_self_of_not_isCoherent
      (E := E) hodd hH hmul hinf hC τ hτiso hτ1 hnc,
    eq_bot_of_normal_lt_quotientFactor_commutator_self_of_not_isCoherent
      (E := E) hodd hH hmul hinf hC τ hτiso hτ1 hnc⟩,
   relIndex_commutator_self_le_of_not_isCoherent hodd hH hmul hinf hC τ hτiso hτ1 hnc,
   not_isMulCommutative_of_not_isCoherent hH hmul hinf hC τ hτiso hτ1 hnc,
   exists_prime_pow_natCard_not_dvd_sub_one_of_not_isCoherent
     hodd hH hmul hinf hC τ hτiso hτ1 hnc⟩

end Main

end CFSG.FeitThompson

end
