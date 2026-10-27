module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHFinal
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHSp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

structure T5ResidualsFinal2 (p f : ℕ) [Fact p.Prime] : Prop where
  twinSmall : TwinSmallInner p
  ntOrth : ∀ (t : StatedLieTag) (k e : ℕ),
    (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → T5BaseAt p f t k e Not
  ntExc : ∀ (t : StatedLieTag) (k e : ℕ),
    (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) → T5BaseAt p f t k e Not

variable {p f : ℕ} [Fact p.Prime]

theorem ih8Thm5_of_residuals_final2 (h : T5ResidualsFinal2 p f) : Ih8Thm5 p f :=
  ih8Thm5_of_residuals_final ⟨h.twinSmall, fun _ _ _ => t5BaseAt_nt_psp, h.ntOrth, h.ntExc⟩

end CFSG.ClassicalInvolution.Asc77
