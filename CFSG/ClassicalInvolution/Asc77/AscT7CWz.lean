module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7c
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscT7ASetup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7C

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem inf_mem_USet_of_le_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) :
    L ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, rfl⟩ := hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans hWS
  have hR8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hL hR)
  have hcard : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) ((Subgroup.card_le_of_le (le_inf hR.1 hRS)).trans' hR8)
  have h611 := l6_11_proved p f hp hq G Ω hΩ S η hη hηS L hL hcard
  obtain ⟨S₀, hηS₀, -⟩ := hη
  exact (hηS₀.1 h611).1

theorem inf_data_of_le_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) :
    IsPGroup 2 ↥(L ⊓ W) ∧ IsCyclic ↥(L ⊓ W) ∧ 4 ≤ Nat.card ↥(L ⊓ W) := by
  have hU := inf_mem_USet_of_le_sylow hp hq hΩ hW hWS hL hR hRS
  obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hU
  exact ⟨hΩ.isPGroup_of_mem_USet hp hU, hcyc, h4⟩

theorem exists_orderOf_four_mem_inf (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G))
    {L R : Subgroup G} (hL : L ∈ Ω) (hR : IsSylow2In R L) (hRS : R ≤ (S : Subgroup G)) {z : G}
    (hz : IsUniqueInvolution L z) : ∃ x ∈ L ⊓ W, orderOf x = 4 := by
  obtain ⟨h2, -, h4⟩ := inf_data_of_le_sylow hp hq hΩ hW hWS hL hR hRS
  exact AscP1Nine3.exists_orderOf_four_of_four_le hz inf_le_left h2 h4

end T7C

variable (p f : ℕ) [Fact p.Prime]

theorem wz : Wz p f := by
  intro G _ _ _ Ω K hs z hz
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ : HypOmegaMod p f Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨S, hRS⟩ := hR.2.1.exists_le_sylow
  obtain ⟨η, hη, hinv⟩ := exists_invariant_mem_etaSet hp hq hΩ S
  have hηG : η ∈ etaG Ω := ⟨S, hη, hinv⟩
  have hW : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, hηG, rfl⟩
  have hWS : (⨆ U ∈ η, U) ≤ (S : Subgroup G) := iSup₂_le fun U hU => (hη.1 hU).2
  obtain ⟨x, hx, hx4⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hW hWS hK hR hRS hz
  refine ⟨_, hW, ?_⟩
  rw [← T7A.sq_eq_of_orderOf_four hz hx.1 hx4]
  exact Subgroup.mul_mem _ hx.2 hx.2

end CFSG.ClassicalInvolution.Asc77
