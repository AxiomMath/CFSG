module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwReturn
public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcAdjoint
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Model
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Chain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

section Chain

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem d4_card_eq_cross (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.D4.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)))
    (hx2 : x ^ 2 = 1) {L : Subgroup (ModGL TwistTag.D4.tag k)}
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
          Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {x})))
    {Y : Type} [Group Y] (φ₀ : Y ≃* L) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (hodd₂ : Odd (Nat.card F₂))
    (eY : Y ⧸ O ≃* SL(2, F₂)) : Nat.card F₂ = p ^ e ∨ Nat.card F₂ = (p ^ e) ^ 3 := by
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, -, n4⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  obtain ⟨r, hr, D, hDχ, hqD, hDθ, J', O₀, hO₀, hA, hcard⟩ :=
    exists_datum_of_isPComponent_twist_cross p TwistTag.D4 hp hk he d4SignDiagramReps
      (r₀ := 3) symmetrizedCartan_perm_D4 h4.permChar_eq h4.exists_rep (untwistAt_d4 p hp e)
      (fun r hr => h4.theta r hr [] (nil_mem_omegaWords_d4 hr))
      (fun r hr => n4 r hr [] (nil_mem_omegaWords_d4 hr)) hx hx2 hL hLc φ₀ O hO hodd₂ eY
  have hP3 : ∀ β, (permLattice TwistTag.D4.perm)^[3] β = β := by
    intro β
    have h3 : TwistTag.D4.perm * (TwistTag.D4.perm * TwistTag.D4.perm) = 1 := by decide
    have h : (permLattice TwistTag.D4.perm)^[3] β = permLattice (TwistTag.D4.perm *
        (TwistTag.D4.perm * TwistTag.D4.perm)) β := rfl
    rw [h, h3]
    rfl
  have hiter : ∀ (n : ℕ) β, D.θ^[n] (toReal β) = toReal ((permLattice TwistTag.D4.perm)^[n] β) := by
    intro n
    induction n with
    | zero => intro β; rfl
    | succ n ih => intro β; rw [Function.iterate_succ_apply, hDθ, ih, Function.iterate_succ_apply]
  have hd : orbitCard O₀ ∣ 3 := by
    rw [(D.withOrbit J').orbitCard_eq_minimalPeriod hO₀]
    refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
    exact (hiter 3 _).trans (congrArg toReal (hP3 _))
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · left
    rwa [h, pow_one, hqD] at hcard
  · right
    rwa [h, hqD] at hcard

end Chain

variable {p f r e : ℕ} [Fact p.Prime] [Fact r.Prime]

theorem card_eq_of_isClassicalMember_trialityD4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hr2 : r ≠ 2)
    (he : 1 ≤ e) [Finite (twistedGroup (iterateFrobenius (GaloisField r (3 * e)) r e))]
    {L : Subgroup (twistedGroup (iterateFrobenius (GaloisField r (3 * e)) r e))}
    {z : twistedGroup (iterateFrobenius (GaloisField r (3 * e)) r e)}
    (hL : IsClassicalMember p f L z) : p ^ f = r ^ e ∨ p ^ f = (r ^ e) ^ 3 := by
  classical
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  set K0 := GaloisField r (3 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  have hCharK : CharP k r := charP_of_injective_algebraMap (algebraMap K0 k).injective r
  set F := frobTwistGL TwistTag.D4.tag k r e (diagramMap TwistTag.D4 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.D4.tag k) F with hR
  set Φ := trialityD4Phi r e k with hΦ
  have hrange : Φ.range = ⁅R, R⁆ := range_trialityD4Phi r e hr2 he
  have hinj : Function.Injective Φ := trialityD4Phi_injective r e k
  have hΦR : ∀ y, Φ y ∈ R := trialityD4Phi_mem_fixedPointsIn r e hr2 he
  let Φ' : twistedGroup (iterateFrobenius K0 r e) →* ↥⁅R, R⁆ :=
    Φ.codRestrict _ (fun g => by rw [← hrange]; exact ⟨g, rfl⟩)
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have : Finite ↥⁅R, R⁆ := Finite.of_surjective Φ' hΦ'surj
  have hker' : Φ'.ker ≤ Subgroup.center (twistedGroup (iterateFrobenius K0 r e)) := by
    rw [MonoidHom.ker_codRestrict, (MonoidHom.ker_eq_bot_iff Φ).2 hinj]
    exact bot_le
  have hz1 : z ≠ 1 := by
    intro h1
    have := hL.orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  have hz' : Φ' z ≠ 1 := fun h1 => hz1 (hinj ((congrArg Subtype.val h1).trans (map_one Φ).symm))
  have hL' := isClassicalMember_map_central Φ' hΦ'surj hker' hodd hL hz'
  have hL'cent : L.map Φ' ≤ Subgroup.centralizer ({Φ' z} : Set ↥⁅R, R⁆) :=
    isSubnormal_le hL'.subnormal
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by omega
  have hP := isPComponent_two_of_isClassicalMember h4 hL'
  have hPM := isPComponent_inf_centralizer_of_isPComponent ⁅R, R⁆ (Φ' z) hL'cent hP
  set x : ModGL TwistTag.D4.tag k := Φ z with hx_def
  have hxR : x ∈ R := hΦR z
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hL.orderOf_eq_two] at this
  have hx2 : x ^ 2 = 1 := by rw [hx_def, ← map_pow, hz2, map_one]
  set L₁ : Subgroup (ModGL TwistTag.D4.tag k) := (L.map Φ').map (⁅R, R⁆).subtype with hL₁
  have hL₁le : L₁ ≤ ⁅R, R⁆ ⊓ Subgroup.centralizer {x} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hL'cent hy)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1)
  obtain ⟨eY⟩ := hL'.nonempty_equiv
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard := d4_card_eq_cross r hr2 (isAlgebraic_zmod_of_isAlgClosure r K0 k) he hxR hx2
    hL₁le hPM ((L.map Φ').equivMapOfInjective (⁅R, R⁆).subtype (⁅R, R⁆).subtype_injective)
    (classicalInvolutionOddCore (L.map Φ')) (CFSG.ComponentClassification.OddCore.odd_card _)
    hodd eY
  rwa [GaloisField.card p f hf0] at hcard

theorem classicalMemberParametersAt_trialityD4 :
    ClassicalMemberParametersAt p f .trialityD4 := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero e := ⟨by omega⟩
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (Generic.modelUniv .trialityD4 0 r e hr).K :=
    ModelFacts.finite_modelUniv hr2 hr trivial hadm
  have : Finite (twistedGroup (iterateFrobenius (GaloisField r (3 * e)) r e)) := hfin
  rcases card_eq_of_isClassicalMember_trialityD4 hp2 hq hr2 he (L := L) (z := z) hL with h | h
  · have hcard : Nat.card (GaloisField r e) = p ^ f := by
      rw [GaloisField.card r e (by omega)]
      exact h.symm
    obtain ⟨rfl, rfl⟩ := eq_of_card_galoisField_eq hq he hcard
    exact ⟨rfl, Or.inl rfl⟩
  · have hcard : Nat.card (GaloisField r (3 * e)) = p ^ f := by
      rw [GaloisField.card r (3 * e) (by omega), pow_mul']
      exact h.symm
    obtain ⟨rfl, h3⟩ := eq_of_card_galoisField_eq hq (by omega) hcard
    exact ⟨rfl, Or.inr ⟨rfl, h3⟩⟩

end CFSG.ClassicalInvolution.Upgrade
