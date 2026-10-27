module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GEBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GKData
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_E_data (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : A10Facts) (hXe : A10Ext)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    {S : Sylow 5 Q} (hSyl : (S : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ)
    {Λ₁ Λ₂ : Subgroup Q} (hΛ : A10GammaStructAt Q (S : Subgroup Q) Λ₁ Λ₂) :
    ∃ N D : Subgroup G, A10EData (M ⊓ Subgroup.centralizer ({x} : Set G)) (rankThreePrimeCore 5 J) N D
      (a10E J ψ Λ₁) (a10E J ψ Λ₂) := by
  obtain ⟨N, D, hkd, hKND⟩ := a10_K_data hS hX hc hP
  refine ⟨N, D, ⟨a10_E_base hS hD1 hU0 hX hXe hc ψ hψ hker hQ hSyl hΛ, hkd, ?_⟩⟩
  intro w hw hw5
  exact (sup_le_sup_left hKND _) (a10_five_EK hS hD1 hU0 hX hXe hc ψ hψ hker hQ hSyl hΛ w hw hw5)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
