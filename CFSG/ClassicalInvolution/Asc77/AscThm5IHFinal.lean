module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHAssembly
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4Odd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

structure T5ResidualsFinal (p f : ℕ) [Fact p.Prime] : Prop where
  twinSmall : TwinSmallInner p
  ntSp : ∀ k e : ℕ, k ≠ 2 → T5BaseAt p f .PSp k e Not
  ntOrth : ∀ (t : StatedLieTag) (k e : ℕ),
    (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → T5BaseAt p f t k e Not
  ntExc : ∀ (t : StatedLieTag) (k e : ℕ),
    (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) → T5BaseAt p f t k e Not

variable {p f : ℕ} [Fact p.Prime]

theorem ih8Thm5_of_residuals_final (h : T5ResidualsFinal p f) : Ih8Thm5 p f :=
  ih8Thm5_of_residuals ⟨h.twinSmall, td4OddCoreAll_proved, td4GenerateAll_proved, h.ntSp, h.ntOrth,
    h.ntExc⟩

end CFSG.ClassicalInvolution.Asc77
