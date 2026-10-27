module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Model

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.TwistedD4

variable (p e : ℕ) [Fact p.Prime]

theorem exists_torus_mul_of_mem_fixedPointsIn_d4 (hp2 : p ≠ 2) (he : 1 ≤ e)
    {g : ModGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e)))}
    (hg : g ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))))
      (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
        (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e)))))) :
    ∃ u ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))),
      frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
        (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e)))) u = u ∧
      ∃ x : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
        g = u * trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e))) x := by
  classical
  set K0 := GaloisField p (3 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  set σ := iterateFrobenius K0 p e with hσdef
  have hodd : Odd (p ^ e) := (Nat.Prime.eq_two_or_odd' Fact.out |>.resolve_left hp2).pow
  have hK : Nat.card K0 = (p ^ e) ^ TwistTag.D4.order := card_galoisField_three_mul p e he
  have hChark : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  have hFr : ∀ c : k, iterateFrobenius k p e c = c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  have hσ : ∀ c : K0, σ c = c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  obtain ⟨-, -, -, -, hmul, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group
    TwistTag.D4 (Fact.out : p.Prime) he hodd K0 hK σ hσ k (iterateFrobenius k p e) hFr
  have hg' : g ∈ (twistedFixedGroup TwistTag.D4 k (iterateFrobenius k p e) :
      Set (ModGL TwistTag.D4.tag k)) := hg
  rw [hmul] at hg'
  obtain ⟨u, hu, h', hh', rfl⟩ := hg'
  have hrange := range_trialityD4Phi p e hp2 he
  have hh'R : h' ∈ (trialityD4Phi p e k).range := by
    rw [hrange]
    exact hder ▸ hh'
  obtain ⟨x, hx⟩ := hh'R
  obtain ⟨huT, huF⟩ := Subgroup.mem_inf.1 hu
  exact ⟨u, huT, huF.2, x, by rw [hx]⟩

end CFSG.ClassicalInvolution.ModelFacts
