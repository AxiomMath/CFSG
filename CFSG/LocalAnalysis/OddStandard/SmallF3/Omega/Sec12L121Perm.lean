module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec121_exists_perm (F : Sec12Frame t L S) :
    ∃ φ : (Fin 5 → ZMod 2) → G,
      IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)) := by
  obtain ⟨φ, hφ, -⟩ := F.bdata.2.2.2.2.2
  exact ⟨φ, by rw [F.bdata.2.2.2.2.1]; exact hφ⟩

end CFSG.OddStandard.SmallF3.Omega
