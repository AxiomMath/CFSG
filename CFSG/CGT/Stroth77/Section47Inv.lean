module

public import CFSG.CGT.Stroth77.Section47Fus
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Thompson

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

theorem false_of_t200_inv_of_noConj [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {U : Subgroup G} {e : G}
    (hUS : U ≤ (S : Subgroup G)) (hUidx : U.relIndex (S : Subgroup G) = 2)
    (heS : e ∈ (S : Subgroup G)) (heU : e ∉ U)
    (hpow : ∀ (g : G) (k : ℕ), g⁻¹ * e ^ (2 * k) * g ∈ (S : Subgroup G) →
      g⁻¹ * e ^ (2 * k) * g ∈ U)
    (hconj : ∀ g : G, g⁻¹ * e * g ∉ U) : False :=
  CFSG.EvenSporadicStandard.TwoHS.false_of_thompson_pow hnonab S.isPGroup' S.not_dvd_index
    hUS hUidx heS heU hpow hconj

theorem H47Inv_c₁_pow {D : Subgroup G} {m : ℕ}
    (dD : StrothWeakTypeData D (.t200 m)) (hm : 1 ≤ m) (k : ℕ) :
    ((dD.c : G) ^ 2 ^ (m - 1)) ^ k = 1 ∨ ((dD.c : G) ^ 2 ^ (m - 1)) ^ k =
      (dD.c : G) ^ 2 ^ (m - 1) := by
  have hsq : (dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1) = 1 :=
    Stroth47Fus.t200_c₁_mul_self dD hm
  rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left
    rw [show t + t = 2 * t by ring, pow_mul, pow_two, hsq, one_pow]
  · right
    rw [pow_add, pow_mul, pow_two, hsq, one_pow, one_mul, pow_one]

end CFSG.CGT.Stroth77
