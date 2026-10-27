module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockPComponent
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionComponentPrimes
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlockFixedRootObstruction
public import CFSG.LieType.Chevalley.AlgebraicClosurePrimeField

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

variable {G : Type*} [Group G] [Finite G]

theorem dvd_card_of_mulEquiv_graphFixedRootGroup {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (t : TwistTag) {r e : ℕ} (hr : r.Prime)
    (hrodd : Odd r) (he : 1 ≤ e) (k : Type) [Field k] (hk : Nat.card k = (r ^ e) ^ t.order)
    (σ : k →+* k) (hσ : ∀ c, σ c = c ^ (r ^ e))
    (φe : L ⧸ center L ≃* graphFixedRootGroup t k σ) : r ∣ Nat.card J := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := fun h => by rw [h] at hrodd; exact (Nat.not_even_iff_odd.2 hrodd) even_two
  have ht0 : 0 < t.order := by cases t <;> decide
  have hk' : Nat.card k = r ^ (e * t.order) := by rw [hk, ← pow_mul]
  have : CharP k r := finite_field_prime_power_characteristic hr (Nat.mul_pos he ht0) hk'
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk']; exact (pow_pos hr.pos _).ne')
  have : CharP (AlgebraicClosure k) r :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective r
  set Fr := iterateFrobenius (AlgebraicClosure k) r e with hFrdef
  have hFr : ∀ c, Fr c = c ^ (r ^ e) := fun c => by rw [hFrdef, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group t hr he
    hrodd.pow k hk σ hσ (AlgebraicClosure k) Fr hFr
  set ι := algebraMap k (AlgebraicClosure k)
  let φ : L ⧸ center L →* ModGL t.tag (AlgebraicClosure k) :=
    (baseChangeGL ι).comp ((graphFixedRootGroup t k σ).subtype.comp φe.toMonoidHom)
  have hφ : Function.Injective φ :=
    (baseChangeGL_injective ι).comp (Subtype.val_injective.comp φe.injective)
  have hrange : φ.range = ⁅twistedFixedGroup t (AlgebraicClosure k) Fr,
      twistedFixedGroup t (AlgebraicClosure k) Fr⁆ := by
    rw [hder]
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨(φe s : ModGL t.tag k), (φe s).2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨φe.symm ⟨g, hg⟩, ?_⟩
      change baseChangeGL ι ((φe (φe.symm ⟨g, hg⟩) : graphFixedRootGroup t k σ) :
        ModGL t.tag k) = baseChangeGL ι g
      rw [MulEquiv.apply_symm_apply]
  obtain ⟨x, hxH, hx2, B, hB, hBc, hBJ⟩ :=
    escaping_block_exists_pComponent_two hq heven hJ hΔ hL hML hLH φ hφ hrange
  have hxR : x ∈ twistedFixedGroup t (AlgebraicClosure k) Fr := Subgroup.commutator_le_self _ hxH
  have halg := algebraicClosure_isAlgebraic_zmod r k
  obtain ⟨-, h6, h4⟩ :=
    rational_e7_twisted_e6_triality_component_prime_divisibility r (AlgebraicClosure k) hr2 halg
      e he
  cases t
  · exact (h6 x hxR hx2 2 Nat.prime_two B hB hBc).2.trans hBJ
  · exact (h4 x hxR hx2 2 Nat.prime_two B hB hBc).2.trans hBJ

theorem commuting_block_odd_twisted_E6_triality_overgroup_exclusion {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ∀ (t : TwistTag) (r e : ℕ), r.Prime → Odd r → 1 ≤ e → ∀ (k : Type) [Field k],
      Nat.card k = (r ^ e) ^ t.order → ∀ σ : k →+* k, (∀ c, σ c = c ^ (r ^ e)) →
        ¬ Nonempty (L ⧸ center L ≃* graphFixedRootGroup t k σ) := by
  intro t r e hr hrodd he k _ hk σ hσ ⟨φe⟩
  have : Fact r.Prime := ⟨hr⟩
  have ht0 : 0 < t.order := by cases t <;> decide
  have hk' : Nat.card k = r ^ (e * t.order) := by rw [hk, ← pow_mul]
  have : CharP k r := finite_field_prime_power_characteristic hr (Nat.mul_pos he ht0) hk'
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk']; exact (pow_pos hr.pos _).ne')
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨σ', hσ'⟩ : ∃ σ' : k ≃+* k, ∀ c, σ' c = σ c :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      fun _ => rfl⟩
  have hσσ : σ'.toRingHom = σ := RingHom.ext hσ'
  have hpow : ∀ n : ℕ, ∀ c, (σ' ^ n) c = c ^ ((r ^ e) ^ n) := by
    intro n
    induction n with
    | zero => intro c; rw [pow_zero, pow_zero, pow_one, RingAut.one_apply]
    | succ n ih =>
      intro c
      rw [pow_succ σ' n, RingAut.mul_apply, ih, hσ', hσ, ← pow_mul, ← pow_succ']
  have hσm : σ' ^ t.order = 1 := RingEquiv.ext fun c => by
    rw [hpow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card, RingAut.one_apply]
  exact commuting_block_fixed_root_quotient_prime_divisor_obstruction hq heven hV hJ hΔ hL hML hLH
    r hrodd k t σ' hσm
    ⟨φe.trans (MulEquiv.subgroupCongr (congrArg (fun s => graphFixedRootGroup t k s) hσσ.symm))⟩
    (dvd_card_of_mulEquiv_graphFixedRootGroup hq heven hJ hΔ hL hML hLH t hr hrodd he k hk σ hσ φe)

end CFSG.LocalAnalysis.ComponentInitial
