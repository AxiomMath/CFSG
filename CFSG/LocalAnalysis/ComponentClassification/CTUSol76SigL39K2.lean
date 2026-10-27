module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39Pt
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigInvSp4

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G]

theorem isInvolutionCoreFreeInv_coreQuot_of_pRank_le_two
    (hS : R12.QuasisimpleRankTwoSymplecticInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hKK : KStarKProper G) {N K : Subgroup G} (hK : K ∈ kStarComponents N)
    (h2K : CFSG.Open.pRank 2 K ≤ 2) (hZ : center (coreQuot K) ≠ ⊥) :
    IsInvolutionCoreFreeInv (coreQuot K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (coreQuot K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2
  obtain ⟨τ, hτ, hτ2⟩ := exists_orderOf_eq_two_mem_center hO hZ
  have hr : CFSG.pRank 2 (coreQuot K) = 2 := by
    rw [FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
    have := two_le_pRank_of_mem_solomonKStar hK.2
    omega
  obtain ⟨F, _, _, hF, ⟨ι⟩⟩ := exists_mulEquiv_statedSp_of_symplectic hS hGA
    (isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2) hO
    (catalog_coreQuotient_of_mem_solomonKStar hKK hK.1 hK.2) hr hτ hτ2
  exact isInvolutionCoreFreeInv_of_mulEquiv ι.symm (isInvolutionCoreFreeInv_statedSp_two hF)

@[expose] def Lemma39TwoDiscK2At (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (∃ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
        orderOf z = 2) →
      IsInvolutionCoreFreeInv (coreQuot K) → ¬ IsInvolutionCoreFreeInv (coreQuot K') →
      ¬ IsSolomonI (coreQuot K') → 2 < CFSG.Open.pRank 2 K' →
      ¬ IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') →
      center (coreQuot K') ≠ ⊥ →
      (center (coreQuot K) ≠ ⊥ → ∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
        ∀ b : G, orderOf b = 2 → b ∈ coreActionKernel K → b ∈ coreActionKernel K' →
          b ∈ centralizer (V : Set G) → b ∈ centralizer (E : Set G) → b ∈ K) →
      K' ≤ normalizer (wGroup B V : Set G) →
        ((IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K)) ∨
            CFSG.Open.pRank 2 K ≤ 2) →
        (center (coreQuot K) ≠ ⊥ ∨ ¬ (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)

theorem lemma39TwoDiscKPAt_of_K2
    (hS : R12.QuasisimpleRankTwoSymplecticInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hI : ∀ (X : Type) [Group X] [Finite X], IsSolomonI X → IsInvolutionCoreFree (X ⧸ center X))
    {R : SigOrientation}
    (hRle : ∀ (G : Type) [Group G] [Finite G] (N K K' : Subgroup G), R G N K K' →
      solRestricted G N K K')
    (h : Lemma39TwoDiscK2At R) : Lemma39TwoDiscKPAt R := by
  intro G _ _ hG N hN hr K K' V B hP hR hW hz _ hnboth hZ' hhub hK'H hcase hdisc hconn
  have hK : K ∈ kStarComponents N := hP.1
  have hK' : K' ∈ kStarComponents N := hP.2.1
  have hKK := kStarKProper_of_simpleAmbient hG
  have hKP : IsInvolutionCoreFreeInv (coreQuot K) := by
    by_cases hKI : IsSolomonI (coreQuot K)
    · exact isInvolutionCoreFreeInv_of_quot (hI _ hKI)
    have h2K : CFSG.Open.pRank 2 K ≤ 2 := by
      rcases hcase with ⟨-, h1⟩ | h1
      · exact absurd h1 hKI
      · exact h1
    by_cases hZ : center (coreQuot K) = ⊥
    · exfalso
      rcases hdisc with h1 | h1
      · exact h1 hZ
      · exact hKI (isSolomonI_of_not_preconnected
          (isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2) hZ h1)
    · exact isInvolutionCoreFreeInv_coreQuot_of_pRank_le_two hS hGA hKK hK h2K hZ
  have hK'P : ¬ IsInvolutionCoreFreeInv (coreQuot K') := fun h' => hnboth ⟨hKP, h'⟩
  have hK'I : ¬ IsSolomonI (coreQuot K') := fun h' =>
    hK'P (isInvolutionCoreFreeInv_of_quot (hI _ h'))
  have hK'r : 2 < CFSG.Open.pRank 2 K' := by
    by_contra hle
    exact hK'P (isInvolutionCoreFreeInv_coreQuot_of_pRank_le_two hS hGA hKK hK' (by omega) hZ')
  have hQ' : ¬ IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') :=
    fun hd => (hRle G N K K' hR hr).1 ⟨hd, hK'r, hK'I⟩
  exact h G hG N hN hr K K' V B hP hR hW hz hKP hK'P hK'I hK'r hQ' hZ' hhub hK'H hcase hdisc
    hconn

end CFSG.ComponentClassification.Sol76.Sig
