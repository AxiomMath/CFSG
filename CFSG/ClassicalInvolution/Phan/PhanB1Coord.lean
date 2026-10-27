module

public import CFSG.ClassicalInvolution.Asc77.AscB3C1

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

structure B2Coord (hK : Nat.card K = (p ^ f) ^ 2) (F : Type) [Field F] (h2 : (2 : F) ≠ 0) where
  ℓ : Su K p f 2 →* StatedSp 2 F
  s : Su K p f 2 →* StatedSp 2 F
  ℓ_inj : Function.Injective ℓ
  s_inj : Function.Injective s
  ℓ_range : ℓ.range = (longBlock F 2 1).range
  s_range : s.range = (twShort h2).range
  comm_tor : ∀ x y : normOne (unitaryInvolution K p f),
    ℓ (torusTwo (unitaryInvolution K p f) x) * s (torusTwo (unitaryInvolution K p f) y) =
      s (torusTwo (unitaryInvolution K p f) y) * ℓ (torusTwo (unitaryInvolution K p f) x)
  conj_ℓ_s : ∀ (x : normOne (unitaryInvolution K p f)) (A : Su K p f 2),
    ℓ (torusTwo (unitaryInvolution K p f) x) * s A *
        (ℓ (torusTwo (unitaryInvolution K p f) x))⁻¹ = s (conjDiag hK ![x⁻¹, 1] A)
  conj_s_ℓ : ∀ (y : normOne (unitaryInvolution K p f)) (A : Su K p f 2),
    s (torusTwo (unitaryInvolution K p f) y) * ℓ A *
        (s (torusTwo (unitaryInvolution K p f) y))⁻¹ = ℓ (conjDiag hK ![y⁻¹ * y⁻¹, 1] A)
  cent : ∀ (x₀ : normOne (unitaryInvolution K p f)), x₀ * x₀ ≠ 1 → ∀ g : StatedSp 2 F,
    g * ℓ (torusTwo (unitaryInvolution K p f) x₀) = ℓ (torusTwo (unitaryInvolution K p f) x₀) * g →
    g * s (torusTwo (unitaryInvolution K p f) x₀) = s (torusTwo (unitaryInvolution K p f) x₀) * g →
      ∃ y w : normOne (unitaryInvolution K p f),
        g = ℓ (torusTwo (unitaryInvolution K p f) y) * s (torusTwo (unitaryInvolution K p f) w)
  center_le : ∀ z ∈ Subgroup.center (StatedSp 2 F), z ∈ s.range

end CFSG.ClassicalInvolution.PhanB3
