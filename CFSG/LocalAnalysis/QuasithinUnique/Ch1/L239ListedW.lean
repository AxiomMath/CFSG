module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedPSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section ListedW

variable {G : Type} [Group G]

@[expose] def IsListedComponentW (M S L : Subgroup G) (z : G) : Prop :=
  fusionIsBenderGroup ↥L ∨ IsRankTwoCharTwoType L ∨
  ((Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ IsThreeFoldCoverAlt L 7) ∧
    IsPartitionStabilizerImage L (L ⊓ M)) ∨
  ((StatedClassicalModel ↥L .PSL 3 3 1 ∨ Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∧
    ∃ zL : G, IsProjectionOn z zL L ∧ L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G)) ∨
  ((∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧ StatedClassicalModel ↥L .PSL 2 p 1) ∧
    L ⊓ M = S ⊓ L) ∨
  ((Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧ IsAltOverElemAbelian (L ⊓ M) 4 6) ∨
    (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      Subgroup.center ↥L ≠ ⊥) ∨
    (Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) ∧
      IsAltOverElemAbelian (L ⊓ M) 4 7)) ∨
  (StatedClassicalModel ↥L .PSL 4 2 1 ∧ (∃ s ∈ S, InducesOuter s L) ∧
    ∃ zL : G, IsProjectionOn z zL L ∧ L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G))

variable {M S L : Subgroup G} {z : G}

theorem IsListedComponent.toW (h : IsListedComponent M S L z) : IsListedComponentW M S L z := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem IsListedComponentW.toOld (h : IsListedComponentW M S L z)
    (hnc : ¬ (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      Subgroup.center ↥L ≠ ⊥)) : IsListedComponent M S L z := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases h with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))
    · exact absurd h hnc
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem IsListedComponentW.old_or_cover (h : IsListedComponentW M S L z) :
    IsListedComponent M S L z ∨
      (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
        Subgroup.center ↥L ≠ ⊥) := by
  by_cases hc : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      Subgroup.center ↥L ≠ ⊥
  · exact Or.inr hc
  · exact Or.inl (h.toOld hc)

end ListedW

@[expose] def Lemma2_3_9_7W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ (H S T' : Subgroup G) (z : G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
      IsSylowTwoOf T' M → S ≤ T' → z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) → z ≠ 1 →
      z ^ 2 = 1 → ∀ L : Subgroup G, IsComponentIn L H →
        ((¬ CentralQuotientAlt L 6 ∧ ¬ CentralQuotientAlt L 7) → Ch1.InducesInner z L) ∧
          IsListedComponentW M S L z

end CFSG.QuasithinUnique

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_3_9_7_listedW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ (H S T' : Subgroup G) (z : G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
      IsSylowTwoOf T' M → S ≤ T' → z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) → z ≠ 1 →
      z ^ 2 = 1 → ∀ L : Subgroup G, IsComponentIn L H → IsListedComponentW M S L z

theorem lemma2_3_9_7W_of_listedW (hlist : Lemma115_3_List) (hlisted : Lemma2_3_9_7_listedW) :
    Lemma2_3_9_7W := by
  intro G _ _ T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL
  exact ⟨lemma2_3_9_7_inner_of_list hlist G T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL,
    hlisted G T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL⟩

theorem lemma2_3_9_7_listedW_of_inspections
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hl42 : L239.L239L42Overgroups)
    (ha7 : L239.L239A7Overgroups) (hl33 : L239.L239L33Overgroups)
    (hm11 : L239.L239M11Overgroups) (hm22 : L239.L239M22Parabolic)
    (hm23 : L239.L239M23Parabolic) (hl2p : L239.L239Sylow2PSL2) (hcov : L239.L239Covers) :
    Lemma2_3_9_7_listedW := by
  intro G _ _ T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL
  by_cases hc : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧ Subgroup.center ↥L ≠ ⊥
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hc)))))))
  · refine IsListedComponent.toW ?_
    exact lemma2_3_9_7_listed_component h37 h38 h238 hlist hnot hpairs hl42 ha7 hl33 hm11 hm22 hm23
      hl2p hcov h hH hS hT' hST' hz hz1 hz2 hL (fun hq => Classical.byContradiction fun hne => hc ⟨hq, hne⟩)

theorem lemma2_3_9_7_listedW_of_inputs
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hl42 : L239.L239L42Overgroups)
    (hl33 : L239.L239L33Overgroups) (hm11 : L239.L239M11Overgroups)
    (hm22 : L239.L239M22Parabolic) (hm23 : L239.L239M23Parabolic) (hcov : L239.L239Covers) :
    Lemma2_3_9_7_listedW :=
  lemma2_3_9_7_listedW_of_inspections h37 h38 h238 hlist hnot hpairs hl42 L239.l239A7Overgroups hl33
    hm11 hm22 hm23 L239.l239Sylow2PSL2 hcov

end CFSG.QuasithinUnique.Vol2Native
