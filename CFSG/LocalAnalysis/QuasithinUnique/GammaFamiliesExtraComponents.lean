module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtra
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Open.StatedDefs
public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Chapter1

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma0.component_normalized_commutator_not_le (h : UniqueSetting G T M)
    {H S T' : Subgroup G} {z : G} (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M))
    (hT' : IsSylowTwoOf T' M) (hST' : S ≤ T')
    (hz : z ∈ T' ⊓ Subgroup.centralizer (T' : Set G)) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    {L : Subgroup G} (hL : IsComponentIn L H) :
    z ∈ Subgroup.normalizer (L : Set G) ∧ ⁅L, Subgroup.zpowers z⁆ = L ∧ ¬ L ≤ M ∧
      CharTwo (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨hcentre, -, -⟩ := hH.center_le_of_le_sylow h hS hT' hST'
  exact (hH.lemma115Hyp h hS (hcentre hz) hz1 hz2 ⟨T', hT', hz⟩).component_action hL

end Chapter1

section ComponentStatements

variable {G : Type} [Group G]

@[expose] def InducesOuter (g : G) (L : Subgroup G) : Prop :=
  g ∈ Subgroup.normalizer (L : Set G) ∧ ¬ Ch1.InducesInner g L

@[expose] def CentralQuotientAlt (L : Subgroup G) (m : ℕ) : Prop :=
  Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin m))

@[expose] def IsThreeFoldCoverAlt (L : Subgroup G) (m : ℕ) : Prop :=
  CFSG.Open.IsQuasisimple ↥L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧ CentralQuotientAlt L m

@[expose] def IsAltOverElemAbelian (X : Subgroup G) (n m : ℕ) : Prop :=
  ∃ (E : Subgroup G) (α : ↥X →* alternatingGroup (Fin m)), E ≤ X ∧ IsElemAbelian 2 E ∧
    Nat.card E = 2 ^ n ∧ Function.Surjective α ∧ α.ker = E.subgroupOf X

@[expose] def IsPartitionStabilizerImage (L X : Subgroup G) : Prop :=
  ∃ (φ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 7)) (τ : Equiv.Perm (Fin 7)),
    τ ^ 2 = 1 ∧ Nat.card {i : Fin 7 // τ i = i} = 1 ∧
      ((X.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map φ.toMonoidHom =
        (Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 7)))).comap
          (alternatingGroup (Fin 7)).subtype

@[expose] def IsProjectionOn (z zL : G) (L : Subgroup G) : Prop :=
  zL ∈ L ∧ ∀ x ∈ L, z⁻¹ * x * z = zL⁻¹ * x * zL

@[expose] def IsRankTwoCharTwoType (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel ↥L .PSL 3 2 n) ∨
    (∃ n : ℕ, 2 ≤ n ∧ StatedClassicalModel ↥L .PSp 2 2 n) ∨
    Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨
    StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 2 ∨
    IsThreeFoldCoverAlt L 6

@[expose] def IsListedComponentType (S L : Subgroup G) : Prop :=
  fusionIsBenderGroup ↥L ∨ IsRankTwoCharTwoType L ∨
  (Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ IsThreeFoldCoverAlt L 7) ∨
  (StatedClassicalModel ↥L .PSL 3 3 1 ∨ Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∨
  (∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧ StatedClassicalModel ↥L .PSL 2 p 1) ∨
  (Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
    Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23)) ∨
  (StatedClassicalModel ↥L .PSL 4 2 1 ∧ ∃ s ∈ S, InducesOuter s L)

@[expose] def IsListedComponent (M S L : Subgroup G) (z : G) : Prop :=
  fusionIsBenderGroup ↥L ∨ IsRankTwoCharTwoType L ∨
  ((Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ IsThreeFoldCoverAlt L 7) ∧
    IsPartitionStabilizerImage L (L ⊓ M)) ∨
  ((StatedClassicalModel ↥L .PSL 3 3 1 ∨ Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∧
    ∃ zL : G, IsProjectionOn z zL L ∧ L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G)) ∨
  ((∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧ StatedClassicalModel ↥L .PSL 2 p 1) ∧
    L ⊓ M = S ⊓ L) ∨
  ((Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧ IsAltOverElemAbelian (L ⊓ M) 4 6) ∨
    (Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) ∧ IsAltOverElemAbelian (L ⊓ M) 4 7)) ∨
  (StatedClassicalModel ↥L .PSL 4 2 1 ∧ (∃ s ∈ S, InducesOuter s L) ∧
    ∃ zL : G, IsProjectionOn z zL L ∧ L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G))

theorem IsListedComponent.type {M S L : Subgroup G} {z : G} (h : IsListedComponent M S L z) :
    IsListedComponentType S L := by
  rcases h with h | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, h', -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (h.imp (fun h => h.1) (fun h => h.1)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, h'⟩)))))

end ComponentStatements

@[expose] def Lemma2_3_9_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ (H S T' : Subgroup G) (z : G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
      IsSylowTwoOf T' M → S ≤ T' → z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) → z ≠ 1 →
      z ^ 2 = 1 → ∀ L : Subgroup G, IsComponentIn L H →
        ⁅L, Subgroup.zpowers z⁆ = L ∧ ¬ L ≤ M ∧
          ∃ LQ : Subgroup G, IsComponentIn LQ (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
            L ≤ LQ

@[expose] def Lemma2_3_9_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ (H S T' : Subgroup G) (z : G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
      IsSylowTwoOf T' M → S ≤ T' → z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) → z ≠ 1 →
      z ^ 2 = 1 → ∀ L : Subgroup G, IsComponentIn L H →
        ((¬ CentralQuotientAlt L 6 ∧ ¬ CentralQuotientAlt L 7) → Ch1.InducesInner z L) ∧
          IsListedComponent M S L z

@[expose] def Lemma2_3_9_7_types : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ (H S T' : Subgroup G) (z : G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
      IsSylowTwoOf T' M → S ≤ T' → z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) → z ≠ 1 →
      z ^ 2 = 1 → ∀ L : Subgroup G, IsComponentIn L H →
        ((¬ CentralQuotientAlt L 6 ∧ ¬ CentralQuotientAlt L 7) → Ch1.InducesInner z L) ∧
          IsListedComponentType S L

theorem Lemma2_3_9_7.types (h : Lemma2_3_9_7) : Lemma2_3_9_7_types := by
  intro G _ _ T M hset H S T' z hH hS hT' hST' hz hz1 hz2 L hL
  obtain ⟨hinn, hlist⟩ := h G T M hset H S T' z hH hS hT' hST' hz hz1 hz2 L hL
  exact ⟨hinn, hlist.type⟩

@[expose] def Lemma2_3_9_6_embedding : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ (H S : Subgroup G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
      ∀ L : Subgroup G, IsComponentIn L H →
        ∃ LQ : Subgroup G, IsComponentIn LQ (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧ L ≤ LQ

theorem lemma2_3_9_6_of_embedding (hemb : Lemma2_3_9_6_embedding) : Lemma2_3_9_6 := by
  intro G _ _ T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL
  obtain ⟨-, hcomm, hLM, -⟩ :=
    hH.component_normalized_commutator_not_le h hS hT' hST' hz hz1 hz2 hL
  exact ⟨hcomm, hLM, hemb G T M h H S hH hS L hL⟩

end CFSG.QuasithinUnique
