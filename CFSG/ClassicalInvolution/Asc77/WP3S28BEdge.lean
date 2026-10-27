module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnConj
public import CFSG.ClassicalInvolution.Balance.Q27FuzzyLinkFrames
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedQuaternion


public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.Q27 CFSG.ClassicalInvolution.Disconnected

section Edge

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem frameAdj_of_fuzzy (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G))
    (hfz : ∃ A₀ : Subgroup G, Theorem5.FuzzyFrameOn p f (CoreAssembly.conjClass K) A₀)
    {M N : Subgroup G}
    (hM : M ∈ CoreAssembly.conjClass K) (hN : N ∈ CoreAssembly.conjClass K) {zM zN : G}
    (hMc : IsClassicalMember p f M zM) (hNc : IsClassicalMember p f N zN)
    (hE : ActsTrivOnQuot N zM) (hne : zM ≠ zN) :
    Theorem5.FrameAdj (Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K))
      (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) zM zN := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hK : CoreAssembly.conjClass K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  rw [hK] at hM hN ⊢
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  have haN : zM ∈ trivialOnQuot N := mem_trivialOnQuot_iff_actsTrivOnQuot.mpr hE
  have hua : zN ≠ zM := hne.symm
  obtain ⟨ld⟩ := exists_linkDataFree hnab hp2 hq hBelow hinv hM hMc
  obtain ⟨A₀, hA₀⟩ := hfz
  rw [hK] at hA₀
  obtain ⟨z₀, hz₀⟩ := Theorem5.FuzzyFrameOn.exists_vertex hA₀
  have hz₀' := hz₀
  obtain ⟨-, J₀, hJ₀𝒞, hJ₀, -⟩ := hz₀'
  obtain ⟨h, hh⟩ := exists_conj_of_mem_canonClass hp2 hf hJ₀𝒞 hJ₀ hM hMc
  have hA₁ := Theorem5.FuzzyFrameOn.map hinv hA₀ h
  have haA₁ := Theorem5.mem_fuzzyVertices_map hinv hz₀ h
  rw [hh] at haA₁
  obtain ⟨J, t, N₁, u₁, hb⟩ := exists_frameBasis hA₁ haA₁
  have ha2 : zM * zM = 1 := hb.sq hb.aB
  obtain ⟨cJ, hcJ⟩ := ld.sec.exists_comp ld.D hb.linkJ
  obtain ⟨c₁, hc₁⟩ := ld.sec.exists_comp ld.D hb.linkN
  obtain ⟨c₀, hc₀⟩ := ld.sec.exists_comp ld.D (triangleResidual_mem_linkFamily hN hNc haN)
  by_cases h0J : c₀ = cJ
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp_free ld hp2 hq hinv hb hN hNc haN
      (j := cJ) hcJ (by rw [← h0J]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases h0N : c₀ = c₁
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp_free ld hp2 hq hinv hb.swap hN hNc haN
      (j := c₁) hc₁ (by rw [← h0N]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases hcl : SameClass zM t zN
  · have hcl' : ¬ SameClass zM u₁ zN := fun h => hb.not_sameClass (hcl.trans ha2 (h.symm ha2))
    obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross_free ld hp2 hq hinv hcan hM hMc hb.memN
      hb.clsN (hb.tqN hb.aB) hb.u_ne_a hN hNc haN hua (j₁ := c₁) (j₂ := c₀) (Ne.symm h0N) hc₁
      hc₀ hcl'
    exact ⟨B, hB, haB, huB⟩
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross_free ld hp2 hq hinv hcan hM hMc hb.memJ
      hb.clsJ (hb.tqJ hb.aB) hb.ta hN hNc haN hua (j₁ := cJ) (j₂ := c₀) (Ne.symm h0J) hcJ hc₀
      hcl
    exact ⟨B, hB, haB, huB⟩

end Edge

end CFSG.ClassicalInvolution.Asc77.S28B
