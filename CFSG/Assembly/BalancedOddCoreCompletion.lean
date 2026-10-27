module

public import CFSG.Assembly.CompletedOddCoreSpan
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.SignalizerFunctorTheorem.Solvable.SmallPrimes

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type} [Group G] [Finite G]

theorem odd_card_involutionOddCore (a : G) : Odd (Nat.card (involutionOddCore a)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [involutionOddCore, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem isSolvableSignalizerFunctor_involutionOddCore (A : Subgroup G) (hA : IsMulCommutative A)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G) ≤ involutionOddCore b) :
    CFSG.Open.IsSolvableSignalizerFunctor 2 A involutionOddCore where
  le_centralizer _ _ _ := Subgroup.map_subtype_le _
  coprime a _ _ := Nat.coprime_two_left.mpr (odd_card_involutionOddCore a)
  invariant a ha _ x hx := by
    rw [involutionOddCore_map (MulAut.conj x) a, MulAut.conj_apply]
    have hxa : x * a = a * x :=
      congrArg Subtype.val (hA.is_comm.comm (⟨x, hx⟩ : A) ⟨a, ha⟩)
    rw [hxa, mul_inv_cancel_right]
  balance := hbal
  solvable a _ _ := CFSG.Milestones.odd_order_solvable (odd_card_involutionOddCore a)

theorem balanced_oddCoreSpan_completed (A : Subgroup G) (hA : IsElemAbelian 2 A)
    (hcard : 8 ≤ Nat.card A)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G) ≤ involutionOddCore b) :
    OddCoreSpanCompleted A ∧ Group.IsSolvable (oddCoreSpan A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x.1 x.2)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h8 : 2 ^ 3 ∣ Nat.card A := by
    rw [hk]
    refine pow_dvd_pow 2 ?_
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hcop, hsolv, hfix⟩ := CFSG.SignalizerFunctorTheorem.Solvable.glauberman_of_le_three G 2
    Nat.prime_two (by norm_num) A hA.1 hA.2 h8 involutionOddCore
    (isSolvableSignalizerFunctor_involutionOddCore A hA.1 hbal)
  refine ⟨⟨(Subgroup.le_normalizer).trans (normalizer_le_oddCoreSpan_normalizer A),
    Nat.coprime_two_left.mp hcop, fun a ha hne => (hfix a ha hne).symm⟩, hsolv⟩

end CFSG.Assembly.Dichotomy
