module

public import Certificates.Certificate517508
public import Certificates.Data.AE6CertF5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open Certificates.AE6Model

theorem fLetterHat_spec : ∀ x : Fin 7, (fLetterHat.getD x.val []).length = 12 ∧
    ∀ i : Fin 12, (fLetterHat.getD x.val []).getD i.val 0 = (ae6LetterHat x i).val := by
  decide

theorem fGammaHat_spec : ∀ c : Fin 2, (fGammaHat.getD c.val []).length = 12 ∧
    ∀ i : Fin 12, (fGammaHat.getD c.val []).getD i.val 0 = (ae6GammaHat c i).val := by
  decide


theorem ae6F5_holds : ∀ σ : Equiv.Perm (Fin 12),
    (∀ m n : Fin 12, ae6Blk m = ae6Blk n ↔ ae6Blk (σ m) = ae6Blk (σ n)) →
    σ ∉ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm) →
    ∃ τ ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)), orderOf τ = 3 ∧
      (∀ n, ae6Blk (τ n) = ae6Blk n) ∧
      (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1 :=
  Certificates.certificate517508

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
