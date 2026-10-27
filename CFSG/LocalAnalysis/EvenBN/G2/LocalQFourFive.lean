module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourThree

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFourB

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_centralizer_yamadaU₁_of_le_yamadaB (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4)
    (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) {P : Subgroup G}
    (hPB : P ≤ yamadaB d) (hP : IsPGroup 2 P)
    (hXP : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ P) :
    P ≤ centralizer (yamadaU₁ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := yamadaB d)).exists_le_sylow
  set V := (Q : Subgroup (yamadaB d)).map (yamadaB d).subtype with hV
  have hPV : P ≤ V := fun x hx => ⟨⟨x, hPB hx⟩, hQ hx, rfl⟩
  have hVsyl : IsSylowOf 2 V (yamadaB d) := ⟨Q, rfl⟩
  obtain ⟨hU, -⟩ := h.yamada_5_10_4 d hK hK4 hcat hVsyl (hXP.trans hPV)
  have hUV : yamadaU₁ d t ≤ centralizer (V : Set G) := hU ▸ inf_le_right
  exact hPV.trans (Subgroup.le_centralizer_iff.1 hUV)

end QFourB

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
