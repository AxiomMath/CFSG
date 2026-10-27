module

public import CFSG.ClassicalInvolution.Asc77.AscT3Z1
public import CFSG.ClassicalInvolution.Asc77.AscT3XSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.z_exists_swap (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) :
    ∃ s ∈ (S : Subgroup G), conjSub s K = K' ∧ s * b = b * s := by
  obtain ⟨hbN, -⟩ := d.x_fieldData c9 h8 hb
  obtain ⟨u, k, hk, hu, huo, hact⟩ := hb.modular
  have hat : b * t * b⁻¹ = t := by
    calc b * t * b⁻¹ = t * b * b⁻¹ := by rw [hb.comm_t]
      _ = t := by group
  have hbK : conjSub b K = K := mem_normalizer_iff_conjSub_eq.mp hbN
  rcases hact with h | h
  · exact d.z_swap_comm c7 hb.mem hb.sq hbK hat hk hu huo (Or.inl rfl) h
  · exact d.z_swap_comm c7 hb.mem hb.sq hbK hat hk hu huo (Or.inr rfl) h

theorem Std20.z_not_dEdgeless [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    (h9 : p ^ f ≠ 9) {b : G} (hb : FieldInv20 S K K' W z t b) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({b} : Set G),
      IsClassicalMember p e₀ (perfectCoreIn K b) ⟨z, hzA⟩ ∧
        ¬ Disconnected.DEdgeless (conjFamily (perfectCoreIn K b)) := by
  obtain ⟨e₀, hfe, h5, hzA, hmem, -, -⟩ := d.x_sectionData c9 h8 h9 hb
  obtain ⟨s, hsS, hsK, hsb⟩ := d.z_exists_swap c7 c9 h8 hb
  refine ⟨e₀, hfe, h5, hzA, hmem, d.x_not_dEdgeless_of_swap hzA hmem hsb ?_ hsK⟩
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hsS)
  exact h1

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
