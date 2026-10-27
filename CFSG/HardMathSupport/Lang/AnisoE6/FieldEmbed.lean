module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.HardMathSupport.Lang.AnisoE6

theorem nonempty_ringHom_of_card_sq {ℓ f : ℕ} [Fact ℓ.Prime] {k K : Type} [Field k] [Field K]
    [Finite k] [Finite K] [CharP k ℓ] [CharP K ℓ] (hk : Nat.card k = ℓ ^ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) : Nonempty (k →+* K) := by
  letI : Algebra (ZMod ℓ) k := ZMod.algebra k ℓ
  letI : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  have h1 := FiniteField.pow_finrank_eq_natCard ℓ k
  have h2 := FiniteField.pow_finrank_eq_natCard ℓ K
  rw [hk] at h1
  rw [hK, ← pow_mul] at h2
  have e1 : Module.finrank (ZMod ℓ) k = f := Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le h1
  have e2 : Module.finrank (ZMod ℓ) K = f * 2 :=
    Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le h2
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod ℓ) (K := k) (L := K)
    (by rw [e1, e2]; exact dvd_mul_right _ _)
  exact ⟨φ.toRingHom⟩

end CFSG.HardMathSupport.Lang.AnisoE6
