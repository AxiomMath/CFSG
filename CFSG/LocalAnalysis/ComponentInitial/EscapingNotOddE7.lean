module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockPComponent
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlockOrdinaryRootObstruction
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionComponentPrimes
public import CFSG.LieType.Chevalley.AlgebraicClosurePrimeField

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

variable {G : Type*} [Group G] [Finite G]

theorem commuting_block_E7_ringChar_dvd_card {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (k : Type) [Field k] [Finite k]
    (hk : ringChar k ≠ 2) (e : L ⧸ center L ≃* adjointGroup .E7 k) :
    ringChar k ∣ Nat.card J := by
  classical
  have : Fintype k := Fintype.ofFinite k
  set r := ringChar k with hr_def
  have : CharP k r := ringChar.charP k
  obtain ⟨n, hr, hcard⟩ := FiniteField.card k r
  have : Fact r.Prime := ⟨hr⟩
  have hkodd : Odd (Nat.card k) := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact (hr.odd_of_ne_two hk).pow
  have : CharP (AlgebraicClosure k) r :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective r
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure k) r n c = c ^ Nat.card k := fun c => by
    rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  obtain ⟨-, -, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E7 k hkodd
    (AlgebraicClosure k) _ hFr
  have hR : fixedPointsIn (adjointGroup .E7 (AlgebraicClosure k))
      (frobTwistGL .E7 (AlgebraicClosure k) r n 1) =
      adjointGroup .E7 (AlgebraicClosure k) ⊓
        (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure k) r n))).eqLocus
          (MonoidHom.id _) := by
    ext g
    simp only [fixedPointsIn, Subgroup.mem_inf]
    refine and_congr_right fun _ => ?_
    change frobTwistGL .E7 (AlgebraicClosure k) r n 1 g = g ↔
      Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure k) r n)) g = g
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  set ι := algebraMap k (AlgebraicClosure k)
  let φ : L ⧸ center L →* ModGL .E7 (AlgebraicClosure k) :=
    (baseChangeGL ι).comp ((adjointGroup .E7 k).subtype.comp e.toMonoidHom)
  have hφ : Function.Injective φ :=
    (baseChangeGL_injective ι).comp (Subtype.val_injective.comp e.injective)
  have hrange : φ.range = ⁅fixedPointsIn (adjointGroup .E7 (AlgebraicClosure k))
      (frobTwistGL .E7 (AlgebraicClosure k) r n 1), fixedPointsIn (adjointGroup .E7
        (AlgebraicClosure k)) (frobTwistGL .E7 (AlgebraicClosure k) r n 1)⁆ := by
    rw [hR, hder]
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨(e s : ModGL .E7 k), (e s).2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨e.symm ⟨g, hg⟩, ?_⟩
      change baseChangeGL ι ((e (e.symm ⟨g, hg⟩) : adjointGroup .E7 k) : ModGL .E7 k) =
        baseChangeGL ι g
      rw [MulEquiv.apply_symm_apply]
  obtain ⟨x, hxH, hx2, B, hB, hBc, hBJ⟩ :=
    escaping_block_exists_pComponent_two hq heven hJ hΔ hL hML hLH φ hφ hrange
  have hxR := Subgroup.commutator_le_self _ hxH
  obtain ⟨h7, -, -⟩ := rational_e7_twisted_e6_triality_component_prime_divisibility r
    (AlgebraicClosure k) hk (algebraicClosure_isAlgebraic_zmod r k) n n.pos
  exact (h7 x hxR hx2 2 Nat.prime_two B hB hBc).2.trans hBJ

theorem commuting_block_odd_E7_overgroup_exclusion {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ∀ (k : Type) [Field k] [Finite k], ringChar k ≠ 2 →
      ¬ Nonempty (L ⧸ center L ≃* adjointGroup .E7 k) := by
  intro k _ _ hk ⟨e⟩
  have : CharP k (ringChar k) := ringChar.charP k
  have hr : (ringChar k).Prime := CharP.char_is_prime k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hr⟩
  exact commuting_block_ordinary_root_quotient_prime_divisor_obstruction hq heven hV hJ hΔ hL
    hML hLH (ringChar k) (hr.odd_of_ne_two hk) k .E7 ⟨e⟩
    (commuting_block_E7_ringChar_dvd_card hq heven hJ hΔ hL hML hLH k hk e)

end CFSG.LocalAnalysis.ComponentInitial
