module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.TL4Conn278ANMu

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_conj_mem_wset (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ∃ g : G, z ∈ conjSub g W ∧ conjSub g W ∈ WSet Ω := by
  have hWc : ∀ g : G, conjSub g W ∈ WSet Ω := fun g => WSet.conj hΩ.conjInvariant hW g
  obtain ⟨η, ⟨S, hη, hinv⟩, rfl⟩ := hW
  have hηG : η ∈ etaG Ω := ⟨S, hη, hinv⟩
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : ⊥ ≤ K)
  obtain ⟨S₀, hRS₀⟩ := hR.2.1.exists_le_sylow
  obtain ⟨c, hc⟩ := exists_conjSub_eq_of_sylow S₀ S
  have hR8 : 8 ≤ Nat.card R := eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  have hK' : conjSub c K ∈ Ω := hΩ.conjInvariant c K hK
  have hRc : conjSub c R ≤ conjSub c K ⊓ (S : Subgroup G) := by
    refine le_inf (conjSub_mono hR.1) ?_
    rw [← hc]
    exact conjSub_mono hRS₀
  have hcard : 2 < Nat.card ↥(conjSub c K ⊓ (S : Subgroup G)) := by
    have h1 := Subgroup.card_le_of_le hRc
    rw [natCard_conjSub] at h1
    omega
  have h611 := l6_11Gen G Ω hΩ S η hηG hηS (conjSub c K) hK' hcard
  have hU : conjSub c K ⊓ (⨆ V ∈ η, V) ∈ USet Ω := (hη.1 h611).1
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := exists_data_of_mem_USet hΩ hU
  have h2 : IsPGroup 2 ↥(conjSub c K ⊓ (⨆ V ∈ η, V)) := isPGroup_of_mem_USet hΩ hU
  have hz' := hz.conj c
  obtain ⟨x, hx, hx4⟩ := AscP1Nine3.exists_orderOf_four_of_four_le hz' inf_le_left h2 h4
  have hxz : c * z * c⁻¹ ∈ ⨆ V ∈ η, V := by
    rw [← sq_eq_of_orderOf_four hz' hx.1 hx4]
    exact Subgroup.mul_mem _ hx.2 hx.2
  refine ⟨c⁻¹, ?_, hWc _⟩
  rw [mem_conjSub_iff]
  simpa using hxz

theorem muIsoE4_of_conj (hΩ : HypOmegaGen Ω) {W : Subgroup G} (g : G)
    (h : MuIsoE4 Ω W) : MuIsoE4 Ω (conjSub g W) := by
  obtain ⟨e⟩ := h
  exact ⟨(Q3.TL4.muGroupConjEquivGen hΩ g W).symm.trans e⟩

theorem muIsoE4_all (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) (h : ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W) :
    ∀ W ∈ WSet Ω, MuIsoE4 Ω W := by
  intro W hW
  obtain ⟨g, hzg, hWg⟩ := exists_conj_mem_wset hΩ hK hz hW
  have h1 := h _ hWg hzg
  have h2 := muIsoE4_of_conj hΩ g⁻¹ h1
  rwa [conjSub_inv_conjSub] at h2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
