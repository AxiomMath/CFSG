module

public import CFSG.ClassicalInvolution.Asc77.AscT8T1
import CFSG.ClassicalInvolution.Asc77.AscT8T2Eng
public import CFSG.ClassicalInvolution.Asc77.WP3Layer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T8T

section Consequences

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G}


theorem TriFrame.xMem (hF : TriFrame Ω M x R) (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (i j : Fin 3) : T8.XMem Ω (x j) (M i) := by
  refine ⟨hF.mem i, ?_, R i, hF.syl i, fun r hr => ?_⟩
  · exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hF.mem i) (hnt _ (hF.mem i))
      (hF.inv i) (Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm hp hΩ j i))
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hF.cent i j hr)

theorem TriFrame.le_trivialOnQuot (hF : TriFrame Ω M x R) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (i : Fin 3) :
    Subgroup.closure ({x 0, x 1, x 2} : Set G) ≤ trivialOnQuot (M i) := by
  exact le_trivialOnQuotE i fun j =>
    ((hF.xMem hp hΩ hnt i j).zpowers_le_trivialOnQuot hp hq hΩ (hF.sq j)) (Subgroup.mem_zpowers _)

theorem TriFrame.mem_tqMembers (hF : TriFrame Ω M x R) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (i : Fin 3) {c : G}
    (hc : c ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G)) : M i ∈ tqMembers Ω c :=
  ⟨hF.mem i, hF.le_trivialOnQuot hp hq hΩ hnt i hc⟩

end Consequences

end T8T

end CFSG.ClassicalInvolution.Asc77
