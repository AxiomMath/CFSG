module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def S267FactBadExcCore : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ (S B : Subgroup Ω), S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        catalogIs (PSimple p S) (onLie fun d => d.characteristic = q ∧ S2019.S2019ExcCoreIdx d) →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
        Nat.card ↥(B ⊓ centModSubgroup p S) = p → ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B

theorem s267FactBadExcLie_of_core (h : S267FactBadExcCore) : S267FactBadExcLie :=
  fun p q hp hp2 hq hq2 hqp Ω _ _ hK S B hSn hperf hcore hcat _ =>
    h p q hp hp2 hq hq2 hqp Ω hK S B hSn hperf hcore hcat

end CFSG.LocalAnalysis.GLTheoremA.S267

end
