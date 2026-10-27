module

public import CFSG.ClassicalInvolution.Asc77.AscT7BExit22

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_chainSetting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (SectionOrthType p f Ω (rLayer Ω (u₁ * u₂)) 6 (piSign p f) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
          ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
            (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
            (∀ i j : Fin 4, edgeD 4 i j →
              ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) ∧ ⨆ k, U k = ⊤

variable {p f}

theorem c22_chain_of_setting (h : C22_chainSetting p f) : C22_chain p f :=
  fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hyp => h G Ω K K' K₃ z u₁ u₂ u₃ hyp.setting

theorem c22_1_of_inputs' (hE : ThmEWithSylow p f) (hz51 : Hyp22Hyp51z p f)
    (hu51 : Hyp22Hyp51u p f) (hsig : C22_4_sigma p f) (hcent : C22_4_cent p f)
    (h8 : C22_8 p f) (hchain : C22_chainSetting p f) : C22_1 p f :=
  c22_1_of_inputs hE hz51 hu51 hsig hcent h8 (c22_chain_of_setting hchain)

end CFSG.ClassicalInvolution.Asc77
