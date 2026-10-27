module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M0

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.T7C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem inf_mem_USet_of_le_sylow (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) :
    L ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, rfl⟩ := hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans hWS
  have hR8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hL hR)
  have hcard : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) ((Subgroup.card_le_of_le (le_inf hR.1 hRS)).trans' hR8)
  have h611 := l6_11_proved G Ω hΩ S η hη hηS L hL hcard
  obtain ⟨S₀, hηS₀, -⟩ := hη
  exact (hηS₀.1 h611).1

theorem inf_data_of_le_sylow (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) :
    IsPGroup 2 ↥(L ⊓ W) ∧ IsCyclic ↥(L ⊓ W) ∧ 4 ≤ Nat.card ↥(L ⊓ W) := by
  have hU := inf_mem_USet_of_le_sylow hΩ hW hWS hL hR hRS
  obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
  exact ⟨hΩ.isPGroup_of_mem_USet hU, hcyc, h4⟩

theorem exists_orderOf_four_mem_inf (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) {z : G}
    (hz : IsUniqueInvolution L z) : ∃ x ∈ L ⊓ W, orderOf x = 4 := by
  obtain ⟨h2, -, h4⟩ := inf_data_of_le_sylow hΩ hW hWS hL hR hRS
  exact AscP1Nine3.exists_orderOf_four_of_four_le hz inf_le_left h2 h4

end CFSG.ClassicalInvolution.Q8P.Asc77.T7C
