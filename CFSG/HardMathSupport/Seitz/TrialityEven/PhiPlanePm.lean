module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWPlane

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.K128



theorem exists_plane_of_dvd_phi_pm {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    ∃ P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ x ∈ P, x ^ r = 1) ∧ Nat.card P = r ^ 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hℓ : ℓ.Prime := Fact.out
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hshape := sylowShape_D4_36 (ℓ := ℓ) hf K hK σ hσ hε hr hr3 hrd
  have hd0 : d4T36d ε (ℓ ^ f) ≠ 0 := ((d4T36d_odd hε hq1).pos).ne'
  have hdvd : r ∣ d4T36d ε (ℓ ^ f) := by
    have h := d4T36d_cast hε hq1
    rw [← h] at hrd
    exact_mod_cast hrd
  have he : 1 ≤ (d4T36d ε (ℓ ^ f)).factorization r :=
    hr.factorization_pos_of_dvd hd0 hdvd
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := inferInstance
  let S : Sylow r (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := default
  obtain ⟨φ⟩ := hshape ((S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    S.isPGroup' S.not_dvd_index
  obtain ⟨E₁, -, hE₁p, hE₁c⟩ := CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.exists_plane_of_sylowShape_gen
    he (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) φ
  exact ⟨E₁, hE₁p, hE₁c⟩

end CFSG.HardMathSupport.Seitz.TrialityEven
