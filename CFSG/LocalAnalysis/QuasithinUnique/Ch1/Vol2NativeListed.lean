module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_3_9_7_listed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ (H S T' : Subgroup G) (z : G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
      IsSylowTwoOf T' M → S ≤ T' → z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) → z ≠ 1 →
      z ^ 2 = 1 → ∀ L : Subgroup G, IsComponentIn L H → IsListedComponent M S L z

theorem inducesInner_of_inducesTwoCentralInner {G : Type} [Group G] {z : G} {L : Subgroup G}
    (h : Ch1.InducesTwoCentralInner z L) : Ch1.InducesInner z L := by
  obtain ⟨l, hl, hact, -⟩ := h
  exact ⟨l, hl, hact⟩

theorem lemma2_3_9_7_inner_of_list (hlist : Lemma115_3_List) :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      ∀ (H S T' : Subgroup G) (z : G), IsGamma0 M H → IsSylowTwoOf S (H ⊓ M) →
        IsSylowTwoOf T' M → S ≤ T' → z ∈ T' ⊓ Subgroup.centralizer (T' : Set G) → z ≠ 1 →
        z ^ 2 = 1 → ∀ L : Subgroup G, IsComponentIn L H →
          (¬ CentralQuotientAlt L 6 ∧ ¬ CentralQuotientAlt L 7) → Ch1.InducesInner z L := by
  intro G _ _ T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL hnot
  obtain ⟨hcentre, -, -⟩ := hH.center_le_of_le_sylow h hS hT' hST'
  have hyp := hH.lemma115Hyp h hS (hcentre hz) hz1 hz2 ⟨T', hT', hz⟩
  rcases hlist G h.simple h.nonabelian h.qtke H S M z hyp L hL with
    hA | hB | ⟨φ, -⟩ | ⟨φ, -⟩ | hE | hF
  · exact hA.2.2
  · exact hB.2.2.2
  · exact absurd ⟨φ⟩ hnot.1
  · exact absurd ⟨φ⟩ hnot.2
  · exact hE.2
  · exact inducesInner_of_inducesTwoCentralInner hF.2

theorem lemma2_3_9_7_of_listed (hlist : Lemma115_3_List) (hlisted : Lemma2_3_9_7_listed) :
    Lemma2_3_9_7 := by
  intro G _ _ T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL
  exact ⟨lemma2_3_9_7_inner_of_list hlist G T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL,
    hlisted G T M h H S T' z hH hS hT' hST' hz hz1 hz2 L hL⟩

end CFSG.QuasithinUnique.Vol2Native
