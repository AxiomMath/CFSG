module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore
public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

@[expose] def QuadraticAutomorphism {G : Type u} [Group G] (automorphism : MulAut G) : Prop :=
  ∀ element : G, automorphism (element⁻¹ * automorphism element) = element⁻¹ * automorphism element

theorem quadratic_automorphism_power_apply {G : Type u} [Group G]
    (automorphism : MulAut G) (hquadratic : QuadraticAutomorphism automorphism)
    (element : G) (exponent : ℕ) :
    (automorphism ^ exponent) element = element * (element⁻¹ * automorphism element) ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hquadratic]
    have heq : automorphism element = element * (element⁻¹ * automorphism element) := by group
    calc
      automorphism element * (element⁻¹ * automorphism element) ^ exponent =
          (element * (element⁻¹ * automorphism element)) *
            (element⁻¹ * automorphism element) ^ exponent :=
        congrArg (fun factor => factor * (element⁻¹ * automorphism element) ^ exponent) heq
      _ = element * (element⁻¹ * automorphism element) ^ (exponent + 1) := by
        rw [mul_assoc, ← pow_succ']

theorem quadratic_automorphism_pow_card_eq_one {G : Type u} [Group G]
    (automorphism : MulAut G) (hquadratic : QuadraticAutomorphism automorphism) :
    automorphism ^ Nat.card G = 1 := by
  ext element
  rw [quadratic_automorphism_power_apply automorphism hquadratic element, pow_card_eq_one', mul_one]
  rfl

theorem quadratic_automorphism_zpowers_isPGroup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hpgroup : IsPGroup prime G) (automorphism : MulAut G)
    (hquadratic : QuadraticAutomorphism automorphism) : IsPGroup prime (Subgroup.zpowers automorphism) := by
  obtain ⟨dimension, hcardDiv⟩ := hpgroup.exists_card_dvd_pow
  apply IsPGroup.of_card_dvd_pow (n := dimension)
  rw [Nat.card_zpowers]
  exact (orderOf_dvd_iff_pow_eq_one.mpr (quadratic_automorphism_pow_card_eq_one automorphism hquadratic)).trans hcardDiv

theorem quadratic_automorphism_pow_eq_one_of_pGroup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G)
    (automorphism : MulAut G) (hquadratic : QuadraticAutomorphism automorphism) :
    ∃ dimension : ℕ, automorphism ^ (prime ^ dimension) = 1 := by
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨dimension, hcard⟩ := hpgroup.exists_card_eq
  exact ⟨dimension, hcard ▸ quadratic_automorphism_pow_card_eq_one automorphism hquadratic⟩

@[expose] noncomputable def actionPrimeCore {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] (prime : ℕ) (action : actor →* MulAut acted) : Subgroup actor :=
  (pCore prime (actor ⧸ action.ker)).comap (QuotientGroup.mk' action.ker)

@[expose] def PrimeStableAction {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    (prime : ℕ) (action : actor →* MulAut acted) : Prop :=
  ∀ member : actor, QuadraticAutomorphism (action member) → member ∈ actionPrimeCore prime action

theorem primeStableAction_of_normal_sylow {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite actor] [Finite acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime acted)
    (action : actor →* MulAut acted) (sylow : Sylow prime actor) (hnormal : (sylow : Subgroup actor).Normal) :
    PrimeStableAction prime action := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : (sylow : Subgroup actor).Normal := hnormal
  let quotient := QuotientGroup.mk' action.ker
  let image := Sylow.mapSurjective (QuotientGroup.mk'_surjective action.ker) sylow
  have himageNormal : (image : Subgroup (actor ⧸ action.ker)).Normal := by
    rw [Sylow.coe_mapSurjective]
    exact hnormal.map quotient (QuotientGroup.mk'_surjective action.ker)
  have : (image : Subgroup (actor ⧸ action.ker)).Normal := himageNormal
  have hcoreEq : pCore prime (actor ⧸ action.ker) = image := by
    apply le_antisymm (pCore_le_sylow prime image)
    exact le_pCore_of_normal prime (image : Subgroup (actor ⧸ action.ker)) himageNormal image.isPGroup'
  intro member hquadratic
  obtain ⟨dimension, hpower⟩ := quadratic_automorphism_pow_eq_one_of_pGroup prime hprime hpgroup
    (action member) hquadratic
  have hmemberPower : quotient member ^ (prime ^ dimension) = 1 := by
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [QuotientGroup.ker_mk']
    apply MonoidHom.mem_ker.mpr
    rw [map_pow]
    exact hpower
  have hcyclicPGroup : IsPGroup prime (Subgroup.zpowers (quotient member)) := by
    apply IsPGroup.of_card_dvd_pow (n := dimension)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hmemberPower
  have hcyclicLe : Subgroup.zpowers (quotient member) ≤ (image : Subgroup (actor ⧸ action.ker)) := by
    obtain ⟨largerSylow, hcontained⟩ := hcyclicPGroup.exists_le_sylow
    have hequal : (largerSylow : Subgroup (actor ⧸ action.ker)) = image :=
      image.is_maximal' largerSylow.isPGroup' (image.isPGroup'.le_sylow_of_normal largerSylow)
    exact hequal ▸ hcontained
  change quotient member ∈ pCore prime (actor ⧸ action.ker)
  rw [hcoreEq]
  exact hcyclicLe (Subgroup.mem_zpowers (quotient member))

end CFSG.RankThreeEvenClassification.Helpers
