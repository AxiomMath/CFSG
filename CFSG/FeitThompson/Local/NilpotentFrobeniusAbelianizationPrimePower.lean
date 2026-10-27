module

public import CFSG.FeitThompson.Local.SmallAbelianizationChiefFactor
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.AbelianSolvable
import CFSG.FeitThompson.Local.NilpotentAbelianizationSamePrimes

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {L : Type*} [Group L] {H E : Subgroup L}

private noncomputable abbrev mkComp (H : Subgroup L) [H.Normal] : ↥H →* L ⧸ ⁅H, H⁆ :=
  (QuotientGroup.mk' ⁅H, H⁆).comp H.subtype

noncomputable def quotientFactorCommutatorSelfMulEquiv (H : Subgroup L) [H.Normal] :
    Abelianization ↥H ≃* ↥(quotientFactor H ⁅H, H⁆) :=
  (QuotientGroup.quotientMulEquivOfEq
    (by rw [← commutator_self_subgroupOf_self (H := H),
      ← ker_mk'_comp_subtype_eq_subgroupOf H ⁅H, H⁆] :
      _root_.commutator ↥H = (mkComp H).ker)).trans
    ((QuotientGroup.quotientKerEquivRange (mkComp H)).trans
      (MulEquiv.subgroupCongr (range_mk'_comp_subtype_eq_quotientFactor H ⁅H, H⁆)))

theorem coe_quotientFactorCommutatorSelfMulEquiv_of [H.Normal] (x : ↥H) :
    ((quotientFactorCommutatorSelfMulEquiv H (Abelianization.of x) :
      ↥(quotientFactor H ⁅H, H⁆)) : L ⧸ ⁅H, H⁆) = ((x : L) : L ⧸ ⁅H, H⁆) := (rfl)

instance isMulCommutative_quotientFactor_commutator_self [H.Normal] :
    IsMulCommutative ↥(quotientFactor H ⁅H, H⁆) :=
  isMulCommutative_of_mulEquiv (quotientFactorCommutatorSelfMulEquiv H).symm

instance isSolvable_quotientFactor_commutator_self [H.Normal] :
    Group.IsSolvable ↥(quotientFactor H ⁅H, H⁆) :=
  isSolvable_of_isMulCommutative

theorem natCard_quotientFactor_commutator_self [H.Normal] :
    Nat.card ↥(quotientFactor H ⁅H, H⁆) = (_root_.commutator ↥H).index := by
  rw [← natCard_abelianization_eq_index_commutator,
    Nat.card_congr (quotientFactorCommutatorSelfMulEquiv H).symm.toEquiv]

section Main

variable [Finite L] [H.Normal] [Group.IsNilpotent ↥H]
  (hL : Odd (Nat.card L)) (hH : H ≠ ⊥)
  (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥)

section CardE

variable (hbd : (⁅H, H⁆).relIndex H ≤ 4 * Nat.card ↥E ^ 2 + 1)

include hL hH hC hbd

theorem exists_prime_pow_natCard_nonempty_mulEquiv_quotientFactor_commutator_self :
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥H = p ^ a ∧
      Nonempty (↥(quotientFactor H ⁅H, H⁆) ≃* Multiplicative (Fin d → ZMod p)) := by
  have hnb : quotientFactor H ⁅H, H⁆ ≠ ⊥ :=
    quotientFactor_ne_bot H _ (commutator_self_lt_self_of_isNilpotent hH)
  obtain ⟨p, d, hp, hd, ⟨e⟩⟩ :=
    exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot hnb
      fun K hK hKlt =>
        eq_bot_of_normal_lt_quotientFactor_commutator_self (E := E) hL hH hC hbd K hK hKlt
  have hfact : Fact p.Prime := ⟨hp⟩
  have hidx : (_root_.commutator ↥H).index = p ^ d := by
    rw [← natCard_quotientFactor_commutator_self, Nat.card_eq_of_bijective e e.bijective]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨a, ha⟩ := exists_natCard_eq_prime_pow_of_index_commutator_eq_prime_pow ↥H hp hidx
  refine ⟨p, a, d, hp, ?_, hd, ha, ⟨e⟩⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · exact absurd (by simpa using ha)
      (Finite.one_lt_card_iff_nontrivial.2 ((Subgroup.nontrivial_iff_ne_bot H).2 hH)).ne'
  · exact ha0

theorem exists_prime_pow_natCard_nonempty_mulEquiv_abelianization :
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥H = p ^ a ∧
      Nonempty (Abelianization ↥H ≃* Multiplicative (Fin d → ZMod p)) := by
  obtain ⟨p, a, d, hp, ha, hd, hcard, ⟨e⟩⟩ :=
    exists_prime_pow_natCard_nonempty_mulEquiv_quotientFactor_commutator_self hL hH hC hbd
  exact ⟨p, a, d, hp, ha, hd, hcard, ⟨(quotientFactorCommutatorSelfMulEquiv H).trans e⟩⟩

theorem exists_prime_natCard_eq_pow_relIndex_commutator_self_eq_pow :
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥H = p ^ a ∧
      (⁅H, H⁆).relIndex H = p ^ d := by
  obtain ⟨p, a, d, hp, ha, hd, hcard, ⟨e⟩⟩ :=
    exists_prime_pow_natCard_nonempty_mulEquiv_quotientFactor_commutator_self hL hH hC hbd
  have hfact : Fact p.Prime := ⟨hp⟩
  refine ⟨p, a, d, hp, ha, hd, hcard, ?_⟩
  rw [relIndex_commutator_self_eq_index_commutator, ← natCard_quotientFactor_commutator_self,
    Nat.card_eq_of_bijective e e.bijective]
  simp [Nat.card_eq_fintype_card]

end CardE

section IndexH

variable (hHE : H.IsComplement' E) (hbd : (⁅H, H⁆).relIndex H ≤ 4 * H.index ^ 2 + 1)

include hL hH hC hHE hbd

theorem nontrivial_quotientFactor_commutator_self_of_isComplement' :
    Nontrivial ↥(quotientFactor H ⁅H, H⁆) := by
  rw [index_eq_natCard_of_isComplement' hHE] at hbd
  exact nontrivial_quotientFactor_commutator_self (E := E) hL hH hC hbd

theorem eq_bot_of_normal_lt_quotientFactor_commutator_self_of_isComplement'
    (K : Subgroup (L ⧸ ⁅H, H⁆)) (hK : K.Normal) (hKlt : K < quotientFactor H ⁅H, H⁆) : K = ⊥ := by
  rw [index_eq_natCard_of_isComplement' hHE] at hbd
  exact eq_bot_of_normal_lt_quotientFactor_commutator_self (E := E) hL hH hC hbd K hK hKlt

theorem exists_prime_pow_natCard_nonempty_mulEquiv_quotientFactor_of_isComplement' :
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥H = p ^ a ∧
      Nonempty (↥(quotientFactor H ⁅H, H⁆) ≃* Multiplicative (Fin d → ZMod p)) := by
  rw [index_eq_natCard_of_isComplement' hHE] at hbd
  exact exists_prime_pow_natCard_nonempty_mulEquiv_quotientFactor_commutator_self
    (E := E) hL hH hC hbd

end IndexH

end Main

end CFSG.FeitThompson

