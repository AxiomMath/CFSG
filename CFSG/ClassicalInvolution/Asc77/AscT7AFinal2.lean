module

public import CFSG.ClassicalInvolution.Asc77.AscT7AWeak

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_13_star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        dComp Ω K ≠ dstarComp Ω K

variable {p f}

theorem C21_13_wyl_of_star (h12 : C21_12 p f) (h : C21_13_star p f) : C21_13_wyl p f := by
  intro G _ _ _ Ω K K' z u J t W hh hα hD
  rcases h12 G Ω K K' z u J t W hh with heq | hmu
  · exact absurd heq (h G Ω K K' z u J t W hh hα hD)
  · exact hmu

variable (p f) in
theorem c21_2_final_star (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (h1 : ThompsonCube p f)
    (h2 : ThompsonStar p f) (h3 : ThompsonClique p f) (h752 : L7_5_2 p f)
    (h5 : ThompsonGraph p f) (h13N : C21_13_N p f) (h13s : C21_13_star p f)
    (h14N : C21_14_N p f) (h14a : C21_14_alt p f) (h15 : C21_15 p f) (hWyl : C21_WylTrans p f)
    (hY : C21_YSigma p f) (h17t : C21_17_tz p f) (hEs : C21_E_star p f) : C21_2 p f :=
  c21_2_final_primitive p f hE hHz hHt hHu h1 h2 h3 h752 h5 h13N
    (C21_13_wyl_of_star (c21_12_of_inputs p f h1 h2 h3 h752 h5) h13s) h14N h14a h15 hWyl hY h17t
    hEs

end CFSG.ClassicalInvolution.Asc77
