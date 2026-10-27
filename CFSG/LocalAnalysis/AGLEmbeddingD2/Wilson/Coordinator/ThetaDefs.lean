module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc

@[expose] noncomputable def L0 : Subgroup J :=
  Subgroup.centralizer ({z0} : Set J) ⊓ Subgroup.centralizer ({cE} : Set J)

theorem L0_le_M2 : L0 ≤ M2 := inf_le_left

theorem L0_le_centralizer_cE : L0 ≤ Subgroup.centralizer ({cE} : Set J) := inf_le_right

theorem mem_L0_iff {g : J} : g ∈ L0 ↔ g * z0 = z0 * g ∧ g * cE = cE * g := by
  simp only [L0, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
