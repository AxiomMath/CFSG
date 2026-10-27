module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigBound
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwap
public import CFSG.LocalAnalysis.ComponentClassification.Sol78HPump

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem dichotomy (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hSwap : SignalizerSwapAltExclusion)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hW : Sol78.signalizerCompletion E E ≠ ⊥) :
    ∃ (M : Subgroup X) (m : ℕ), M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ∧
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) ∧
      J ≤ M ∧ normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) ∧
      Odd m ∧ n ≤ m ∧ m ≤ n + 4 ∧
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)) ∧
      (m = n → J ⊔ FooteLit.oddCoreIn M = M) ∧
      (n < m → normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M ≤
          (pPrimeCore 2 ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).map
            (normalizer (Sol78.signalizerCompletion E E : Set X)).subtype) := by
  obtain ⟨M, hMH, hMpc, htM, hJM⟩ :=
    S.exists_fixed_component h33 h35 hT13 hML hSch hSwap hN1
  obtain ⟨m, hm, hnm, ⟨eM⟩⟩ :=
    S.exists_pumped_component h33 h35 hT13 hML hSch hPump hW hMH hMpc htM hJM
  have hCH := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    hCH (mem_centralizer_singleton_iff.mpr rfl)
  rcases hnm.lt_or_eq with hlt | heq
  · have hZ := S.exact_of_pumped hT13 hML hSch hMH hMpc htM hJM hnm eM
    refine ⟨M, m, hMH, hMpc, hJM,
      S.normalizer_of_pumped hT13 hML hSch hMH hMpc htH htM hJM hlt eM, hm, hnm,
      S.le_add_four_of_pumped hT13 hML hSch hMH hMpc htM hJM hm hlt eM,
      ⟨(QuotientGroup.quotientMulEquivOfEq hZ).symm.trans eM⟩, fun h => absurd h hlt.ne', fun _ =>
      S.kernel_le_core_of_pumped hT13 hML hSch hMH hMpc htH htM hJM hlt eM⟩
  · subst heq
    obtain ⟨hsup, hM, hHN⟩ :=
      S.normal_of_trivial_pump_of_member hT13 hML hSch hMH hMpc hJM eM hCH htM
    exact ⟨M, n, hMH, hMpc, hJM, hHN, hm, le_rfl, by omega, hM, fun _ => hsup,
      fun h => absurd h (lt_irrefl n)⟩

end Sig36

end CFSG.ComponentClassification.SolMax
