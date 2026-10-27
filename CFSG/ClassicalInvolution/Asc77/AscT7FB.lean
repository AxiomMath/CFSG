module

public import CFSG.ClassicalInvolution.Asc77.AscT7FA
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKD
public import CFSG.ClassicalInvolution.Asc77.AscIHSectH

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_13_N_ne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      dComp Ω K ≠ dstarComp Ω K →
        Subgroup.centralizer ({t * z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_N_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      ¬ (dComp Ω K = dstarComp Ω K ∧ SectionConnected Ω u) →
        Subgroup.centralizer ({u} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_alt_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ →
        ¬ (dComp Ω K = dstarComp Ω K ∧ SectionConnected Ω u) →
          rLayer Ω u ≤ sigmaGen Ω K ∨
            Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)

variable {p f}

theorem c21_13_N_of_ne (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (hC3 : C21_3 p f)
    (h : C21_13_N_ne p f) : C21_13_N p f := by
  intro G _ _ _ Ω K K' z u J t W hh
  by_cases heq : dComp Ω K = dstarComp Ω K
  · exact hh.centralizer_tz_le_normalizer_alpha hMF h3s ⟨hC3, twinNormAlpha_of p f hC3⟩ heq
  · exact h G Ω K K' z u J t W hh heq

theorem c21_14_N_of_rest (hC3 : C21_3 p f) (h : C21_14_N_rest p f) : C21_14_N p f := by
  intro G _ _ _ Ω K K' z u J t W hh
  by_cases hgood : dComp Ω K = dstarComp Ω K ∧ SectionConnected Ω u
  · exact hh.centralizer_u_le_normalizer_alpha ⟨hC3, twinNormAlpha_of p f hC3⟩ hgood.1 hgood.2
  · exact h G Ω K K' z u J t W hh hgood

theorem c21_14_alt_of_rest (h : C21_14_alt_rest p f) : C21_14_alt p f := by
  intro G _ _ _ Ω K K' z u J t W hh hα
  by_cases hgood : dComp Ω K = dstarComp Ω K ∧ SectionConnected Ω u
  · exact Or.inl (hh.rLayer_u_le_sigmaGen hα hgood.1 hgood.2)
  · exact h G Ω K K' z u J t W hh hα hgood

variable (p f) in
theorem c21_2_final_F (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (h13 : C21_13_N_ne p f) (h14 : C21_14_N_rest p f)
    (h14a : C21_14_alt_rest p f) (h15 : C21_15 p f) (hWyl : C21_WylTrans' p f) :
    C21_2 p f := by
  by_cases hpq : p ≠ 2 ∧ 5 ≤ p ^ f
  · have hMF : DStarConnectedTwinGen p f :=
      dstarConnectedTwinGen_of smallNoThree G2D4Models.ih8G2D4_unconditional ih8D4Star hpq.1 hpq.2
    have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
      G2D4Models.h3s_of_nonToral_free hNT
    have hC3 : C21_3 p f := c21_3_of p f (twinFrameHyp51_of_cases (twinFrameHyp51z p f) hHt hHu)
    exact c21_2_final_H p f hNT hHt hHu ih8D4Star (c21_13_N_of_ne hMF h3s hC3 h13)
      (c21_14_N_of_rest hC3 h14) (c21_14_alt_of_rest h14a) h15 hWyl
  · intro G _ _ _ Ω K K' z hs
    exact absurd ⟨hs.stand.odd, hs.stand.five⟩ hpq

end CFSG.ClassicalInvolution.Asc77
