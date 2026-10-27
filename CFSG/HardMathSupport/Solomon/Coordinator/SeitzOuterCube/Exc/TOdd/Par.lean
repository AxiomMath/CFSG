module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

structure D4ParOdd (ℓ f : ℕ) (X : Type) [Field X] [Finite X] (σ : X ≃+* X) : Prop where
  prime : ℓ.Prime
  ne_two : ℓ ≠ 2
  ne_three : ℓ ≠ 3
  one_le : 1 ≤ f
  card : Nat.card X = (ℓ ^ f) ^ 3
  frob : ∀ c : X, σ c = c ^ (ℓ ^ f)

variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem D4ParOdd.charP (P : D4ParOdd ℓ f X σ) : CharP X ℓ :=
  haveI : Fact ℓ.Prime := ⟨P.prime⟩
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic P.prime
    (k := f * 3) (Nat.mul_pos P.one_le (by norm_num)) (by rw [P.card, ← pow_mul])

theorem D4ParOdd.sigma_cube (P : D4ParOdd ℓ f X σ) (c : X) : σ (σ (σ c)) = c :=
  CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (σ := σ.toRingHom) P.card P.frob c

theorem D4ParOdd.sigma_cube_hom (P : D4ParOdd ℓ f X σ) :
    ∀ c : X, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := fun c => P.sigma_cube c

theorem D4ParOdd.sigma_pow_three (P : D4ParOdd ℓ f X σ) : σ ^ 3 = 1 :=
  RingEquiv.ext fun c => by
    rw [pow_succ, pow_two]
    exact P.sigma_cube c

theorem D4ParOdd.five_le_prime (P : D4ParOdd ℓ f X σ) : 5 ≤ ℓ := by
  have h2 := P.prime.two_le
  have h4 : ℓ ≠ 4 := fun h => by
    have hp := P.prime
    rw [h] at hp
    exact absurd hp (by decide)
  have := P.ne_two
  have := P.ne_three
  omega

theorem D4ParOdd.five_le (P : D4ParOdd ℓ f X σ) : 5 ≤ ℓ ^ f :=
  le_trans P.five_le_prime (Nat.le_self_pow (by have := P.one_le; omega) ℓ)

theorem D4ParOdd.not_three_dvd (P : D4ParOdd ℓ f X σ) : ¬ 3 ∣ ℓ ^ f := by
  intro h
  have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three P.prime).1
    (Nat.prime_three.dvd_of_dvd_pow h)
  exact P.ne_three h3.symm

theorem D4ParOdd.mod_three (P : D4ParOdd ℓ f X σ) : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by
  have := P.not_three_dvd
  omega

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
