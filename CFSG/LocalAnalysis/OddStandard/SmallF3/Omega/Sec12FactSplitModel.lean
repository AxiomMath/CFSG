module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Split
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0
public import Certificates.Certificate442009

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace MoSplit

open Certificates.OmegaSplit

theorem mem_b0Elems {g : P45} : g ∈ b0Elems () ↔ g ∈ B0 :=
  mem_B0_iff.symm

end MoSplit

theorem asc82FactSplitModel_of_cert :
    Asc82FactSplitModel := by
  obtain ⟨X, hle, hmeet, hcov⟩ := Certificates.certificate442009
  have hS : Certificates.OmegaSplit.bSet = (B0 : Set P45) :=
    Set.ext fun _ => MoSplit.mem_b0Elems
  rw [hS] at hle hmeet hcov
  refine ⟨X, hle, eq_bot_iff.2 fun g hg => ?_, fun a ha => ?_⟩
  · obtain ⟨hgX, hgB⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_bot.2 (hmeet g hgX hgB)
  · obtain ⟨x, hx, b, hb, e⟩ := hcov a ha
    exact ⟨x, hx, b, hb, e⟩

theorem asc82FactSplit5_of_cert :
    Asc82FactSplit5 :=
  asc82FactSplit5_of_model asc82FactSplitModel_of_cert

end CFSG.OddStandard.SmallF3.Omega
