module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeHubFix

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.ToralCensus CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg

@[expose] def HubCases {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) : Prop :=
  ∀ (I : Set (Fin r)) (i : Fin r), i ∈ I → (∃ k, k ∉ I) →
    (I = {i} ∨ ∃ j : Fin r, j ≠ i ∧ I = {i, j} ∧ A i j * A j i = 1) →
    (∃ k, k ∉ I ∧ i ≠ k ∧ A i k = 0) ∨
    (∃ a b k : Fin r, a ≠ b ∧ A a i = -1 ∧ A i a = -1 ∧ A a b = 0 ∧ k ∉ I ∧
      0 < (Pi.single b 1 - A i b • Pi.single i 1 - A i b • Pi.single a 1 : Fin r → ℤ) k) ∨
    (∃ s : Fin r, i ≠ s ∧ A i s = -1 ∧ A s i = -2 ∧ s ∉ I)

theorem hubWitnesses_of_hubCases {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hD : D.divisible = ∅) (h : HubCases D.cartan) :
    HubWitnesses D := by
  intro I i hi hex hI
  rcases h I i hi hex hI with ⟨k, hk, hik, h0⟩ | ⟨a, b, k, hab, h1, h2, h3, hk, hpos⟩ |
    ⟨s, his, h1, h2, hs⟩
  · exact hubWitness_of_cartan_eq_zero hext hik hk h0
  · exact hubWitness_of_three hct hext hab h1 h2 h3 hk hpos
  · exact hubWitness_of_bTwo hct hext hD his h1 h2 hs

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses
