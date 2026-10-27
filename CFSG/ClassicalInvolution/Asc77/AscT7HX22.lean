module

public import CFSG.ClassicalInvolution.Asc77.AscT7HLayer
public import CFSG.ClassicalInvolution.Asc77.AscT7BChain
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp51
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_8X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) ∧
        (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤

@[expose] def C22_chainX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
          ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
            (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
            (∀ i j : Fin 4, edgeD 4 i j →
              ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) ∧ ⨆ k, U k = ⊤

@[expose] def C22_chainSettingX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
          ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
            (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
            (∀ i j : Fin 4, edgeD 4 i j →
              ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) ∧ ⨆ k, U k = ⊤

variable {p f}

theorem c22_chain_of_settingX (h : C22_chainSettingX p f) : C22_chainX p f :=
  fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hyp => h G Ω K K' K₃ z u₁ u₂ u₃ hyp.setting

theorem c22_9_ofX (h4 : C22_4 p f) (h8 : C22_8X p f) (hchain : C22_chainX p f) : C22_9 p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  obtain ⟨U, hUΩ, hcomm, hpair, hgen⟩ := hchain G Ω K K' K₃ z u₁ u₂ u₃ h
    (h4 G Ω K K' K₃ z u₁ u₂ u₃ h) (h8 G Ω K K' K₃ z u₁ u₂ u₃ h)
  have hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U (zeroD (n := 4) (by omega))) := by
    intro J hJ
    obtain ⟨g, hg⟩ := (h.std.stand.of_mem (hUΩ (zeroD (n := 4) (by omega)))).trans J hJ
    exact ⟨g, hg.symm⟩
  have hK : K ∈ Ω := h.std.stand.mem
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ := (h.std.stand.hyp.isQuatSub_of_mem_RSet h.std.stand.odd
    (mem_RSet_of_isSylow2In hK hV)).exists_not_commute
  exact Or.inl (Or.inl (oddLieType_of_chain_plus h.std.stand.odd h.std.stand.five (by norm_num)
    h.std.stand.hyp.conjInvariant U hUΩ hcls hcomm hpair hgen ⟨x, y, hxy⟩))

theorem c22_1_of_inputsX (hE : ThmEWithSylow p f) (hz51 : Hyp22Hyp51z p f)
    (hu51 : Hyp22Hyp51u p f) (hsig : C22_4_sigma p f) (hcent : C22_4_cent p f)
    (h8 : C22_8X p f) (hchain : C22_chainSettingX p f) : C22_1 p f :=
  c22_1_of_steps (c22_setup p f)
    (c22_9_ofX (c22_4_of hE (c22_2_of hz51 hu51) hsig hcent) h8 (c22_chain_of_settingX hchain))

end CFSG.ClassicalInvolution.Asc77
