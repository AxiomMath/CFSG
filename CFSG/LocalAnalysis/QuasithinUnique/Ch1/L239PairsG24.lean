module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsG24Good
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6

theorem pairsFor_G24
    : PairsFor TypeG24 := by
  intro G _ _ L R _ hty hR hRN hS
  have hmod : ChevalleyExceptionalModel (↥L ⧸ CFSG.pCore 2 ↥L) .G2 2 2 := hty
  obtain ⟨hf2, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  obtain ⟨Q₁, Q₂, h1, h2, hsup, hinv, ⟨R₁, hF₁⟩, ⟨R₂, hF₂⟩⟩ := G2.hasParabolicPair hK hf2
  have : Finite ↥(adjointGroup Tag.G2 K) := Finite.of_equiv _ e.toEquiv
  let θ0 : ↥L →* ↥(adjointGroup Tag.G2 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hθ0 : Function.Surjective θ0 := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : θ0.ker = CFSG.pCore 2 ↥L := by
    ext x
    simp [θ0]
  have hS₀i : ¬ 2 ∣ ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).index := by
    have h : ¬ 2 ∣ ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).relIndex ⊤ :=
      hU₀.2.2
    rwa [Subgroup.relIndex_top_right] at h
  exact pairConclusion_of_local_pair hRN hS θ0 hθ0 hker _ hU₀.2.1 hS₀i Q₁ Q₂
    (fun α hα => (hinv α hα).1) (fun α hα => (hinv α hα).2) h1 h2 hsup hF₁.goodLocal
    hF₂.goodLocal

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
