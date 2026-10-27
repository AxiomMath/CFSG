
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourNorm

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.SectionRank
open scoped commutatorElement

namespace L238

variable {G : Type} [Group G] [Finite G]

@[expose] def AltBlockStatementJCat : Prop :=
  ∀ X T L : Subgroup G, CharTwo X → IsSQTKCat X → IsSylowTwoOf T X → IsBlock2 X L →
    blockU L ≤ VZ T X → thompsonJ T ≤ Subgroup.normalizer (L : Set G) →
    ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G) →
    (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m) →
      IsChiBlock X L ∨ IsExcA7Block L

theorem exists_chiBlock_of_chi0Block_catJ
    (h127 : C127StatementCat (G := G)) (h123 : C123TwoCgsStatement (G := G))
    (hB42 : AltBlockStatementJCat (G := G))
    {X T U K M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M)
    (hU : U ∈ uFamHat X T) (hK : IsChi0Block U K) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hUK : U = T ⊔ conjClosure K T) (hKM : ¬ K ≤ M) :
    ∃ L : Subgroup G, IsChiBlock X L ∧ ⁅L, thompsonJ T⁆ = L ∧ K ≤ L ∧ ¬ L ≤ M := by
  have hKU : K ≤ U := hUK ▸ (le_conjClosure K T).trans le_sup_right
  obtain ⟨L, hLblock, hKL, -, hULV, hcases⟩ :=
    h127 X T U K hX hT hSQ hU hK (fun hUC => hKM ((hKU.trans hUC).trans hcgs)) hKJ hUK
  rcases hcases with hKL' | ⟨m, n, hm, hn, hm3, hn3, hmL, hnK⟩
  · subst hKL'
    exact ⟨K, C1GN.isChiBlock_of_isChi0Block hLblock hK, hKJ, le_rfl, hKM⟩
  · have hnotKC : ¬ K ≤ Subgroup.centralizer (VZ T X : Set G) :=
      C1GN.not_le_of_isAltQuotient hnK hn3
    have hKLJ : K ≤ ⁅L, thompsonJ T⁆ :=
      calc K = ⁅K, thompsonJ T⁆ := hKJ.symm
        _ ≤ ⁅L, thompsonJ T⁆ := Subgroup.commutator_mono hKL le_rfl
    have hnotLJ : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G) := fun h =>
      hnotKC (hKLJ.trans h)
    have hJT : thompsonJ T ≤ T := (C1GN.thompsonJ_le_baum T).trans (C1GN.baum_le T)
    have hJN : thompsonJ T ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_isAltQuotient hX h38 hT hLblock hULV hm hm3 hmL hKL
        (not_isPGroup_two_of_isShort2 hK.1.1) hJT (hKJ.le.trans hKL)
    have hLchi : IsChiBlock X L := by
      rcases hB42 X T L hX hSQ hT hLblock hULV hJN hnotLJ ⟨m, hm, hm3, hmL⟩ with h | hexc
      · exact h
      · exact absurd (hKL.trans (le_of_isExceptionalA7Block_cat h123 hX hSQ h38 hT hcgs hLblock hexc))
          hKM
    have hNL : ⁅L, thompsonJ T⁆ ≤ L := C1GN.commutator_le_of_le_normalizer hJN
    have hLN : L ≤ Subgroup.normalizer ((⁅L, thompsonJ T⁆ : Subgroup G) : Set G) :=
      A3.le_normalizer_commutator_left L (thompsonJ T)
    have hEq : ⁅L, thompsonJ T⁆ = L :=
      C1GN.isShort2_eq_of_isAltQuotient hLblock.1 hm hm3 hmL hNL hLN hnotLJ
    exact ⟨L, hLchi, hEq, hKL, fun hLM => hKM (hKL.trans hLM)⟩

end L238

end CFSG.QuasithinUnique
