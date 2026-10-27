module

public import Certificates.Certificate41504

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34TwoSig

open CFSG.ComponentClassification.PSL3Four

theorem l34TwoSig_check :
    ∃ B₀ : Subgroup (Equiv.Perm (Fin 42)), B₀ ≤ S ∧ Nat.card B₀ = 9 ∧
      ∀ r ∈ R, r ^ 256 = 1 → (∀ b ∈ B₀, b * r = r * b) ∨
        ∃ w ∈ Subgroup.closure {x | ∃ c ∈ B₀, x = c * r * c⁻¹}, w ^ 256 ≠ 1 :=
  Certificates.certificate41504

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34TwoSig
