module

public import CFSG.ClassicalInvolution.Asc77.AscC22P9
import CFSG.ClassicalInvolution.Asc77.AscS22E

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

set_option linter.unusedSectionVars false

namespace C22P

section Named

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_normY : Prop :=
  p ^ f % 4 = 1 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
        rLayer Ω (u₁ * u₂) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)

end Named

section Reduction

variable {p f : ℕ} [Fact p.Prime]


theorem c22_alpha_of_normY (h : C22_normY p f) : C22_alpha p f := by
  intro hq1 G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs hW hLG
  obtain ⟨K₄, hK₄, h41, h42, h43, -⟩ := fourTwins_S hs hW
  have hbig : S22.Big Ω K := S22.Big.of_four hs hK₄ h41 h42 h43
  have h2 := S22.c22_2S p f G Ω K K' K₃ z u₁ u₂ u₃ hs hbig
  have hCz := S22.centralizer_le_normalizer_alpha (S22.c22_2S p f) hs hbig
  have hY := h hq1 G Ω K K' K₃ z u₁ u₂ u₃ hs hW hLG
  have hle : (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
    refine sup_le (iSup₂_le fun M hM m hm => ?_) hY
    apply hCz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (e189_commute_of_mem (isUniqueInvolution_of_mem_twinSet hs.hz hM) hm).symm
  rw [hLG.2] at hle
  exact T7B.eq_bot_of_normalizer_eq_top h2.1 (top_le_iff.mp hle) (T7B.two_dvd_natCard hs.hz)

end Reduction

end C22P

section Final

variable {p f : ℕ} [Fact p.Prime]


theorem c22_chainPos_of_normY (h : C22P.C22_normY p f) : R31.C22_chainPos p f :=
  c22_chainPos_of_alpha (C22P.c22_alpha_of_normY h)

end Final

end CFSG.ClassicalInvolution.Asc77
