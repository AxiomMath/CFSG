module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockExclusionT
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.ParabolicFacts
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Escape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenGlue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.MinPar

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
theorem pElementSubgroup_le_over {P R S' : Subgroup (X ⧸ gnC T)} {H₁ : Subgroup X}
    (hmap : gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P R)) S' ⊔ S') :
    pElementSubgroup 2 P ≤ gnImg T H₁ := by
  rw [hmap]
  exact ((Subgroup.closure_mono fun x hx => ⟨le_conjClosure P R hx.1, hx.2⟩ :
    pElementSubgroup 2 P ≤ pElementSubgroup 2 (conjClosure P R)).trans
      (le_conjClosure _ S')).trans le_sup_left

theorem false_of_blocks_over (hK : KFactChevMinParabolic) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hch : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P) {S : Subgroup X} (hST : S ≤ T)
    (hLS : gnImg T T ⊓ L ≤ gnImg T S) {H₁ : Subgroup X}
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H₁)
    (hmap : gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
      (gnImg T S ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T S) ⊔ gnImg T S)
    {r : ℕ} {K : Fin r → Subgroup X} (hKb : ∀ i, IsChiBlockGN H₁ (K i))
    (hKK : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) (hres : twoResidual H₁ = ⨆ i, K i) : False := by
  set T' : Subgroup (X ⧸ gnC T) := gnImg T T with hT'
  set S' : Subgroup (X ⧸ gnC T) := gnImg T S with hS'
  set R : Subgroup (X ⧸ gnC T) := S' ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T)) with hR
  set W : Subgroup (X ⧸ gnC T) := pElementSubgroup 2 (conjClosure P R) with hW
  have hS2 : IsPGroup 2 S' := (hX.sylow.2.1.to_le hST).map _
  have hS'T' : S' ≤ T' := Subgroup.map_mono hST
  obtain ⟨hWL, hRW, hS⟩ := pElementSubgroup_conjClosure_facts hX hL hPb (R := R) inf_le_right
  by_cases hQL : conjClosure P R = L
  · have hLW : L ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) := by
      have hWL' : W = pElementSubgroup 2 L := by rw [hW, hQL]
      rw [hWL']
      exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_pElementSubgroup 2 L)
    exact false_of_blocks_of_normal_S hX hL hWL hLW hS (not_le_normalizer_of_isMinOverBorel hPb)
      hS2 hQH hmap hKb hres
  · exact false_of_blocks_of_ne_S hX hL hWL hRW hS2
      ((kFact_of_le hK hX hL hch hPb (inf_le_left.trans hS'T') inf_le_right
        fun x hx => ⟨hLS hx, Subgroup.le_normalizer hx.2⟩).2 hQL) hQH hmap hKb hKK hres

theorem escape_over (hK : KFactChevMinParabolic) (hX : GNSetting X T) {C₁ C₂ : Subgroup X}
    {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hch : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P) {S : Subgroup X} (hST : S ≤ T)
    (hLS : gnImg T T ⊓ L ≤ gnImg T S) {H₁ : Subgroup X}
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H₁)
    (hmap : gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
      (gnImg T S ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T S) ⊔ gnImg T S)
    (hc : C₁ ≤ centerOf H₁ ∨ H₁ ≤ Subgroup.normalizer (C₂ : Set X) ∨
      ∃ (r : ℕ) (K : Fin r → Subgroup X), (∀ i, IsChiBlockGN H₁ (K i)) ∧
        (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧ twoResidual H₁ = ⨆ i, K i) :
    pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  rcases hc with h1 | h2 | ⟨r, K, hKb, hKK, hres⟩
  · exact escape_of_le_gnImg (pElementSubgroup_le_over hmap) (Or.inl h1)
  · exact escape_of_le_gnImg (pElementSubgroup_le_over hmap) (Or.inr h2)
  · exact (false_of_blocks_over hK hX hL hch hPb hST hLS hQH hmap hKb hKK hres).elim

theorem escape_over_of_concl1Gen (hK : KFactChevMinParabolic) (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hch : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P) {S : Subgroup X} (hST : S ≤ T)
    (hLS : gnImg T T ⊓ L ≤ gnImg T S) {H₁ : Subgroup X}
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H₁)
    (hmap : gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
      (gnImg T S ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T S) ⊔ gnImg T S)
    (hSH : IsSylowTwoOf S H₁) (hF : CharTwo H₁) (hc : Concl1Gen C₁ C₂ H₁ S) :
    pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  refine escape_over hK hX hL hch hPb hST hLS hQH hmap ?_
  rcases hc with h1 | h2 | hblk
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨r, K, -, hKb, hKK, hres, -, -⟩ := blocksGen_of_oneBlock hF hSH hblk
    exact Or.inr (Or.inr ⟨r, K, fun i => ⟨(hKb i).1.1, (hKb i).1.2⟩, hKK, hres⟩)

end CFSG.AGLEmbeddingD2.Tits.GN516
