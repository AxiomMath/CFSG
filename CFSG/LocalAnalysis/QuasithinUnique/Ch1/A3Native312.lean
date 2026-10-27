module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.Quasithin.Background.A3Structure312

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem a312_refined_of_list {G : Type} [Group G] [Finite G] (hSL2 : A312SL2Fact)
    (hlist : ∀ L ∈ cComp (⊤ : Subgroup G), CFSG.IsQuasisimple ↥L →
      ∀ T' : Subgroup ↥L, IsSylowTwoOf T' ⊤ → ∀ B' ∈ lFamily T', B' ≠ ⊤ → A312Case B' ⊤)
    (hnq : ∀ L ∈ cComp (⊤ : Subgroup G), ¬ CFSG.IsQuasisimple ↥L → A36Strong L)
    (h37 : A37Statement G) (h39 : A39Statement G) : A312Refined G := by
  intro T hT B hB
  obtain ⟨L, hL, hBL⟩ := A312.exists_le_cComp hT hB h37 h39
  have hBne : B ≠ ⊥ := ne_bot_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)
  have hperf : ⁅B, B⁆ = B := perfect_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)
  refine ⟨L, hL, hBL, fun L' hL' hBL' => A312.eq_of_le_of_le h37 hBne hperf hL hL' hBL hBL', ?_⟩
  by_cases hq : CFSG.IsQuasisimple ↥L
  · by_cases hBeq : B = L
    · exact Or.inl hBeq
    · right
      left
      refine ⟨hq, A312Case.of_subgroupOf hBL ?_⟩
      obtain ⟨hT', hB'⟩ := A312.isSylowTwoOf_lFamily_subgroupOf hT hL hBL hB
      have hne : B.subgroupOf L ≠ ⊤ := by
        intro h
        apply hBeq
        exact le_antisymm hBL (fun x hx => by
          have : (⟨x, hx⟩ : ↥L) ∈ B.subgroupOf L := by rw [h]; trivial
          exact this)
      exact hlist L hL hq _ hT' _ hB' hne
  · right
    right
    exact ⟨hq, A312.nonquasi_of_lFamily hSL2 hT hL hBL hB (hnq L hL hq) hq⟩

theorem a312ForSQTKCat_of_facts (hList : A312ListFactsCat) (hSL2 : A312SL2Fact)
    (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat) : A312ForSQTKCat :=
  fun Q _ hQ => by
  have := hQ.finite
  refine (a312_refined_of_list hSL2 (fun L hL hq T' hT' B' hB' hne => ?_)
    (fun L hL hnq => (h36 Q hQ L hL).toStrong hnq) (h37 Q hQ) (h39 Q hQ)).statement
  have hL' : SQTKHypCat ↥L := hQ.of_subnormal (subnormal_of_mem_cComp hL)
  exact hList ↥L hq hL'.isSQTKCat hL'.o2 T' hT' B' hB' hne

end CFSG.QuasithinUnique.Vol2Native
