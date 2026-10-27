module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFSingle
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ConstraintQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFFamily

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def ffC (M T : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) M : Set G) ⊓ M

@[expose] def FFRankTwoCase (M T : Subgroup G) : Prop :=
  ¬ 3 ∣ Nat.card ↥(ffC M T) →
  ∀ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
    (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)))),
    M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) →
    2 ≤ I.card → (∀ L ∈ I, Nat.card L = 6) →
      autI hU (thompsonJ M) = ⨆ L ∈ I, L →
      IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) →
      (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) → S3Family I → False

theorem exists_normal_order_three_of_coprime_centralizer {M T : Subgroup G} (hK : IsKGroup ↥M)
    (hF : CharTwo M) (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) (hI59 : AGL81I59)
    (hT : IsSylowTwoOf T M)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T))
    (hr2 : FFRankTwoCase M T) :
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal := by
  set V := conjClosure (quasithinOmegaOneCenter T) M with hV
  obtain ⟨hU, -⟩ := B2_15 hF hT
  have hMN : M ≤ Subgroup.normalizer (V : Set G) :=
    (conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)).2.2.2.1
  have hconAut : CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M V) :=
    isPConstrained_autI_of_coprime hU hMN hC3 hcon
  have hFF : FFConclusion M T V := by
    by_cases hs : Group.IsSolvable ↥(autOn M V)
    · exact ffConclusion_of_solvable hF hs hT hV hJ
    · exact hI59 G M T V hK hF hT hV hconAut hJ
  obtain ⟨hU', hMN', I, hne, hcard, hI, hSyl, hperm, hfam⟩ := exists_family_of_ffConclusion hT hJ hFF
  by_cases hI1 : I.card = 1
  · exact exists_normal_order_three_of_family_card_one hU' hMN' hcard hI hperm hI1 hC3
  · exact (hr2 hC3 hU' I hMN' (by have := hne.card_pos; omega) hcard hI hSyl hperm hfam).elim

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
