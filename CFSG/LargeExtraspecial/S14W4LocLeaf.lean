module

public import CFSG.Sporadic.Co2
public import CFSG.LargeExtraspecial.S14W4SetPi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G]

theorem factorization_card_Co2 :
    (Nat.card CFSG.Blueprint.NativeSporadic.Co2).factorization 2 = 18 := by
  rw [CFSG.Sporadic.Co2.card_Co2, show (42305421312000 : ℕ) = 2 ^ 18 * 161382375 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

namespace W4Hyp

variable {S : Setting G} {g : G} {t : S.O} {c : Config} (h : W4Hyp S g t c)
include h

theorem exists_R₀_ker {k : ↥(h.S₀.M)} {r' : S.O} (hr' : r' ∈ Rbar S g t)
    (hv : ∀ v ∈ Vt S g t, ((r'⁻¹ * ι S k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ∃ r : ↥(h.S₀.M), (r : ↥(Mbar0 S)) ∈ h.R₀ ∧ h.π (r⁻¹ * k) = 1 := by
  have hr := h.exists_R₀ hr'
  cases hr with
  | intro r₀ hr₀ =>
    cases hr₀ with
    | intro hr₀R hr₀e =>
      subst hr₀e
      refine ⟨⟨r₀, h.R₀_le_M hr₀R⟩, hr₀R, (h.π_eq_one_iff _).mpr fun v hvV => ?_⟩
      have e : ι S ((⟨r₀, h.R₀_le_M hr₀R⟩ : ↥(h.S₀.M))⁻¹ * k : ↥(h.S₀.M)) =
          (ι S r₀)⁻¹ * ι S k :=
        (map_mul (ι S) _ _).trans (congrArg (· * ι S k) (map_inv (ι S) r₀))
      exact (congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) e).trans (hv v hvV)

end W4Hyp

end CFSG.LargeExtraspecial.S14
