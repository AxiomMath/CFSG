module

public import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairStab
public import CFSG.ClassicalInvolution.ModelFacts.TwistedLeviDescent

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LeviE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi

variable {k : Type} [Field k]

theorem iform_eq_zero_of_rootChar_pairDiagE6_eq_one {δ : Fin (Tag.rank .E6) → ℤ} {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → c ^ j ≠ 1) {σ : Fin (Tag.rank .E6) → ℤ} (hσ : IsRoot .E6 σ)
    (h : rootChar (pairDiagE6 δ c) σ = 1) :
    iform thetaE6 σ = 0 ∧ (-1 : kˣ) ^ iform δ σ = 1 := by
  rw [rootChar_pairDiagE6] at h
  have b := abs_iform_thetaE6_le hσ
  rw [abs_le] at b
  have hpow : ∀ n : ℤ, (c ^ n) ^ 2 = c ^ (2 * n) := fun n => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    norm_cast
  have h2 : ((-1 : kˣ) ^ iform δ σ * c ^ iform thetaE6 σ) ^ 2 = 1 := by rw [h]; simp
  rw [mul_pow, neg_one_zpow_sq', one_mul, hpow] at h2
  have hy : iform thetaE6 σ = 0 := by
    have := eq_zero_of_zpow_eq_one' hc (m := 2 * iform thetaE6 σ) (N := 8) (by
      rw [abs_le]; omega) h2
    omega
  refine ⟨hy, ?_⟩
  rw [hy, zpow_zero, mul_one] at h
  exact h

theorem perm_thetaE6 : permLattice TwistTag.E6.perm thetaE6 = thetaE6 :=
  List.ofFn_injective (by decide : List.ofFn (permLattice TwistTag.E6.perm thetaE6) =
    List.ofFn thetaE6)

section Instance

variable (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]

theorem exists_levi_fixed_conj_E6 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {δ : Fin (Tag.rank .E6) → ℤ} (hδ : IsRoot .E6 δ) (hδθ : iform thetaE6 δ = 0)
    (hδρ : permLattice TwistTag.E6.perm δ = δ) {y v : ModGL TwistTag.E6.tag k}
    (hv : v ∈ parabolicLevi TwistTag.E6.tag k JE6)
    (hFy : frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) y = y)
    (hvy : v * y * v⁻¹ = rootDiagUnit TwistTag.E6.tag (thetaDiag δ (-1 : kˣ))) :
    ∃ h ∈ parabolicLevi TwistTag.E6.tag k JE6,
      frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) h = h ∧
        h * y * h⁻¹ = rootDiagUnit TwistTag.E6.tag (thetaDiag δ (-1 : kˣ)) := by
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  refine exists_twisted_levi_fixed_conj p TwistTag.E6 he (J := JE6) (θ := thetaE6) (δ := δ)
    (c := c) ?_ iform_permLattice_E6 perm_thetaE6 hδρ ?_ ?_ ?_ ?_ ?_ hv hFy hvy
  · intro j hj
    have hj' : j.val ≠ 1 := hj
    show (TwistTag.E6.perm j).val ≠ 1
    revert hj'
    fin_cases j <;> decide
  · intro σ hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagE6_eq_one hc hσ.1 hσ.2
    refine ⟨hσ.1, h1, ?_⟩
    exact (rootChar_thetaDiag δ (-1 : kˣ) σ).trans h2
  · exact fun σ hσ h => mem_parabolicRoots_E6 hσ h
  · intro j hj
    have hj' : j.val ≠ 1 := hj
    exact (iform_thetaE6_single_eq j).trans (by simp [hj'])
  · exact fun w hw => rootCharStabilizer_pairDiagE6_le hk2 hδ hδθ hc hw
  · intro i
    simp only [thetaDiag]
    rcases Int.even_or_odd (iform δ (Pi.single i 1)) with h | h
    · left
      exact h.neg_one_zpow
    · right
      exact h.neg_one_zpow

end Instance

end CFSG.ClassicalInvolution.ModelFacts.LeviE6
