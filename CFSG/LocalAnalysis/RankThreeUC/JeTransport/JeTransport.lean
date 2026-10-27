module


public import CFSG.LocalAnalysis.RankThreeUC.Section3.OmegaOneCenter.OmegaOneZ
import all CFSG.LocalAnalysis.RankThreeUC.Section3.OmegaOneCenter.OmegaOneZ

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankThreeUC

namespace JeTransport

open Section3.OmegaOneCenter

variable {G : Type} [Group G]

section OmegaOneZ

variable {H : Type} [Group H]

theorem mem_omegaOneZ_gen (p : ℕ) (P : Subgroup G) :
    omegaOneZ p P = closure {x : G | x ∈ P ∧ x ∈ centralizer (P : Set G) ∧ x ^ p = 1} := by
  unfold omegaOneZ; rfl

theorem omegaOneZ_le (p : ℕ) (P : Subgroup G) : omegaOneZ p P ≤ P :=
  (closure_le P).2 fun _ hx => hx.1

end OmegaOneZ

end JeTransport

end CFSG.LocalAnalysis.RankThreeUC
