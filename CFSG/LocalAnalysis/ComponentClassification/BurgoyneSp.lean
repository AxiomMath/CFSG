module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpInner
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.Blueprint

theorem burgoynePropA_PSp (X : Type) [Group X] [Finite X] (hX : IsM4 X) {r p f : ℕ}
    (hp2 : p ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .PSp r p f) (t : X)
    (ht : orderOf t = 2) (Y : Subgroup X) (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨hp, hf, hr, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have hψ := socleAction_injective hsimple hnab θ
    have hInn : (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K))).range ≤ (socleAction θ).range := by
      rintro _ ⟨x, rfl⟩
      exact conj_mem_range_socleAction θ x
    have hinj := conj_injective_of_mulEquiv hsimple hnab θ
    obtain ⟨A, τ, hα⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr
      (socleAction θ t)
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hα
      exact inner_propAConclusion_Sp hp hp2 hf hKc hr hinj hψ hInn ht hα hY hYO
    · exact absurd (field_eq_bot hp hp2 hf hKc hr hinj hψ hInn ht hτ hα hYO) hY
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.Sp
