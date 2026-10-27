module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Entry
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)
open CFSG.Sporadic.Schreier (j3P j3PermEquiv card_j3P)
open CFSG.Sporadic.SmallOddCore (ctuc_j3_full_automorphism_permutation_model)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_sylow_containing {T P : Subgroup G} {x : G} (hP : IsPGroup 2 P) (hTP : T ≤ P)
    (hx : x ∈ P) : ∃ Q : Sylow 2 G, T ≤ (Q : Subgroup G) ∧ x ∈ (Q : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  exact ⟨Q, hTP.trans hQ, hQ hx⟩

end CFSG.EvenSporadicStandard.Fin76b
