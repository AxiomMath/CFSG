module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Sec
public import CFSG.ClassicalInvolution.Q3.Q3TSetup

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem e4CoverOddFree_proved : E4CoverOddFree := by
  intro X _ _ hX v hv
  have key : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t →
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
      ∀ ψ : (CompData.model t n).G →* X, Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center _ →
          classicalInvolutionOddCore ↥(Subgroup.centralizer ({v} : Set X)) = ⊥ := by
    intro t n hft hadm ψ hψ hker
    have h := modelOddCentralizerFree3_proved t n Nat.prime_three hft hadm X ψ hψ hker v hv
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h
  rcases hX with ⟨ψ, hψ, hker, -⟩ | ⟨ψ, hψ, hker, -⟩
  · exact key .PSp 2 trivial ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩ ψ hψ hker
  · exact key .PSL 4 trivial ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩ ψ hψ
      hker

end CFSG.ClassicalInvolution.Q3.TL4
