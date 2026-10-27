
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourJNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourCount
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank

namespace L238

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjJoin_eq_conjClosure (S L : Subgroup G) : conjJoin S L = conjClosure L S := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mem_conjClosure s.2 hy
  · refine conjClosure_le fun h hh z hz => ?_
    exact Subgroup.mem_iSup_of_mem (⟨h, hh⟩ : S) (⟨z, hz, rfl⟩ : _ ∈ L.map (MulAut.conj h).toMonoidHom)

theorem uFamHat_le_sup_chiBlocks_of_blocks
    (h127 : C127StatementCat (G := G)) (h123 : C123TwoCgsStatement (G := G))
    (hB42 : AltBlockStatementJCat (G := G))
    {X T M U : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M)
    (hTM : T ≤ M) (hU : U ∈ uFamHat X T)
    (hblk : ¬ U ≤ M → ∃ L : Subgroup G, IsChi0Block U L ∧ ⁅L, thompsonJ T⁆ = L ∧ ¬ L ≤ M ∧
      U = conjJoin T L ⊔ T) :
    U ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L := by
  by_cases hUM : U ≤ M
  · exact hUM.trans le_sup_left
  obtain ⟨L, hL, hLJ, hLM, hUL⟩ := hblk hUM
  have hUK : U = T ⊔ conjClosure L T := by
    rw [hUL, sup_comm, conjJoin_eq_conjClosure]
  obtain ⟨L', hL'chi, hL'J, hLL', hL'M⟩ :=
    exists_chiBlock_of_chi0Block_catJ h127 h123 hB42 hX hSQ h38 hT hcgs hU hL hLJ hUK hLM
  have hΩ : ∀ s ∈ T, L'.map (MulAut.conj s).toMonoidHom ∈ C1GN.chiBlocksOutside X T M :=
    fun s hs => mem_chiBlocksOutside_conj hT.1 hTM ⟨hL'chi, hL'J, hL'M⟩ hs
  rw [hUL]
  refine sup_le (le_sup_of_le_right ?_) (hTM.trans le_sup_left)
  refine iSup_le fun s => ?_
  refine (Subgroup.map_mono hLL').trans ?_
  exact le_iSup₂_of_le _ (hΩ s s.2) le_rfl

theorem lemma_C129_of_blocks
    (h127 : C127StatementCat (G := G)) (h123 : C123TwoCgsStatement (G := G))
    (hB42 : AltBlockStatementJCat (G := G)) (hA7 : C129A7StatementCat (G := G))
    {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (h37 : A37Statement (↥X ⧸ CFSG.pCore 2 ↥X))
    (hT : IsSylowTwoOf T X) (hT0 : T ≠ ⊥)
    (hcgs : cgsIn X T ≤ M) (hMX : M ≤ X)
    (hblk : ∀ U ∈ uFamHat X T, ¬ U ≤ M → ∃ L : Subgroup G, IsChi0Block U L ∧
      ⁅L, thompsonJ T⁆ = L ∧ ¬ L ≤ M ∧ U = conjJoin T L ⊔ T) :
    X = M ∨ ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
      (∀ i, IsChi0Block X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i ∧ ¬ L i ≤ M) ∧
      (∀ L' : Subgroup G, IsChi0Block X L' → ⁅L', thompsonJ T⁆ = L' → ¬ L' ≤ M →
        ∃ i, L' = L i) ∧
      X = M ⊔ ⨆ i, L i := by
  classical
  have hcharT : (T.subgroupOf T).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hNTM : X ⊓ Subgroup.normalizer (T : Set G) ≤ M := by
    refine le_trans ?_ hcgs
    exact le_iSup_of_le T (le_iSup_of_le le_rfl (le_iSup_of_le hT0 (le_iSup_of_le hcharT le_rfl)))
  have hTM : T ≤ M := fun t ht => hNTM ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hXle : X ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L := by
    obtain ⟨-, -, hXeq⟩ := uHat_normal_and_eq_sup hT.1
    calc X = uHat X T ⊔ (X ⊓ Subgroup.normalizer (T : Set G)) := hXeq
      _ ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L := by
        refine sup_le (iSup₂_le fun U hU => ?_) (hNTM.trans le_sup_left)
        exact uFamHat_le_sup_chiBlocks_of_blocks h127 h123 hB42 hX hSQ h38 hT hcgs hTM hU
          (hblk U hU)
  have hBX : ∀ L ∈ C1GN.chiBlocksOutside X T M, L ≤ X := fun L hL => hL.1.1.2.1
  have htwo : ∀ A ∈ C1GN.chiBlocksOutside X T M, ∀ B ∈ C1GN.chiBlocksOutside X T M,
      ∀ C ∈ C1GN.chiBlocksOutside X T M, A = B ∨ A = C ∨ B = C := by
    intro A hA B hB C hC'
    by_contra hcon
    push Not at hcon
    obtain ⟨hAB, hAC, hBC⟩ := hcon
    exact not_three_chiBlocks hX (rank_le_of_isSQTKCat hSQ Nat.prime_three (by norm_num))
      (rank_quotient_le_of_isSQTKCat hSQ 3 Nat.prime_three (by norm_num)) h37 hA.1 hB.1 hC'.1
      hAB hAC hBC
  have hchi0 : ∀ L ∈ C1GN.chiBlocksOutside X T M, IsChi0Block X L := fun L hL =>
    isChi0Block_of_isChiBlock_cat hA7 hX hSQ hT hcgs hMX hL.1 hL.2.1 hL.2.2
  have hcomplete : ∀ L' : Subgroup G, IsChi0Block X L' → ⁅L', thompsonJ T⁆ = L' → ¬ L' ≤ M →
      L' ∈ C1GN.chiBlocksOutside X T M := fun L' h1 h2 h3 =>
    ⟨C1GN.isChiBlock_of_isChi0Block h1.1 h1, h2, h3⟩
  by_cases hne : ∃ A, A ∈ C1GN.chiBlocksOutside X T M
  · right
    obtain ⟨A, hA⟩ := hne
    by_cases hB : ∃ B ∈ C1GN.chiBlocksOutside X T M, B ≠ A
    · obtain ⟨B, hB, hBA⟩ := hB
      have hall : ∀ C ∈ C1GN.chiBlocksOutside X T M, C = A ∨ C = B := fun C hC' => by
        rcases htwo A hA B hB C hC' with h | h | h
        · exact absurd h.symm hBA
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      refine ⟨2, ![A, B], by norm_num, le_rfl, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · exact ⟨hchi0 A hA, hA.2.1, hA.2.2⟩
        · exact ⟨hchi0 B hB, hB.2.1, hB.2.2⟩
      · intro L' h1 h2 h3
        rcases hall L' (hcomplete L' h1 h2 h3) with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      · refine le_antisymm (hXle.trans (sup_le_sup_left ?_ M)) ?_
        · refine iSup₂_le fun C hC' => ?_
          rcases hall C hC' with h | h
          · rw [h]
            exact le_iSup (fun i => (![A, B] : Fin 2 → Subgroup G) i) 0
          · rw [h]
            exact le_iSup (fun i => (![A, B] : Fin 2 → Subgroup G) i) 1
        · refine sup_le hMX (iSup_le fun i => ?_)
          fin_cases i
          · exact hBX A hA
          · exact hBX B hB
    · push Not at hB
      refine ⟨1, fun _ => A, le_rfl, by norm_num, fun _ => ⟨hchi0 A hA, hA.2.1, hA.2.2⟩, ?_, ?_⟩
      · intro L' h1 h2 h3
        exact ⟨0, hB L' (hcomplete L' h1 h2 h3)⟩
      · refine le_antisymm (hXle.trans (sup_le_sup_left ?_ M)) ?_
        · refine iSup₂_le fun C hC' => ?_
          rw [hB C hC']
          exact le_iSup (fun _ : Fin 1 => A) 0
        · exact sup_le hMX (iSup_le fun _ => hBX A hA)
  · left
    refine le_antisymm (hXle.trans (sup_le le_rfl (iSup₂_le fun L hL => absurd ⟨L, hL⟩ hne))) ?_
    exact hMX

end L238

@[expose] def Lemma2_3_8_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G), UniqueSetting G T M →
    IsGamma0 M H → CharTwo H → IsSylowTwoOf S (H ⊓ M) →
    CFSG.Quasithin.cgsIn H S ≤ H ⊓ M ∧
      ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
        (∀ i, IsChi0Block H (L i) ∧ ¬ L i ≤ M ∧ ⁅L i, CFSG.Quasithin.thompsonJ S⁆ = L i) ∧
        H = (H ⊓ M) ⊔ ⨆ i, L i

structure Lemma246Inputs : Prop where
  c127 : ∀ (G : Type) [Group G] [Finite G], L238.C127StatementCat (G := G)
  c123 : ∀ (G : Type) [Group G] [Finite G], L238.C123TwoCgsStatement (G := G)
  b42 : ∀ (G : Type) [Group G] [Finite G], L238.AltBlockStatementJCat (G := G)
  a7 : ∀ (G : Type) [Group G] [Finite G], L238.C129A7StatementCat (G := G)
  a38 : Vol2Native.A38ForSQTKCat

abbrev Lemma238Inputs : Prop := Lemma246Inputs

namespace L238

variable {G : Type} [Group G] [Finite G]

theorem lemma2_3_8_4_strong (hMB : MinParabolicBlocks)
    (h127 : C127StatementCat (G := G)) (h123 : C123TwoCgsStatement (G := G))
    (hB42 : AltBlockStatementJCat (G := G)) (hA7 : C129A7StatementCat (G := G))
    {T M H S : Subgroup G} (h : UniqueSetting G T M)
    (hH : IsGamma0 M H) (hc : CharTwo H) (hS : IsSylowTwoOf S (H ⊓ M))
    (h38 : A38Part3 (↥H ⧸ CFSG.pCore 2 ↥H)) (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) :
    cgsIn H S ≤ H ⊓ M ∧ ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
      (∀ i, IsChi0Block H (L i) ∧ ¬ L i ≤ M ∧ ⁅L i, thompsonJ S⁆ = L i) ∧
      (∀ L' : Subgroup G, IsChi0Block H L' → ¬ L' ≤ M → ⁅L', thompsonJ S⁆ = L' →
        ∃ i, L' = L i) ∧
      H = (H ⊓ M) ⊔ ⨆ i, L i := by
  obtain ⟨hSH, -, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  have hcgs := cgsIn_le_inf h hH hc hS
  have hS0 := ne_bot_of_isGamma0 h hH hS
  have hSQ : IsSQTKCat H := positiveTwoCoreSQTK G T M h H hH.isGamma.1
  have hblk : ∀ U ∈ uFamHat H S, ¬ U ≤ H ⊓ M → ∃ L : Subgroup G, IsChi0Block U L ∧
      ⁅L, thompsonJ S⁆ = L ∧ ¬ L ≤ H ⊓ M ∧ U = conjJoin S L ⊔ S := by
    intro U hU hUM
    obtain ⟨L, hL, hLJ, hLM, hUL⟩ := exists_block_of_mem_uFamHat hMB h hH hc hS hU
      (fun hUM' => hUM (le_inf hU.1.1 hUM'))
    exact ⟨L, hL, hLJ, fun hle => hLM (hle.trans inf_le_right), hUL⟩
  refine ⟨hcgs, ?_⟩
  rcases lemma_C129_of_blocks h127 h123 hB42 hA7 hc hSQ h38 h37 hSH hS0 hcgs
      inf_le_left hblk with hHeq | ⟨s, L, hs1, hs2, hL, hcomp, hHL⟩
  · exact absurd (hHeq ▸ inf_le_right) hH.isGamma.not_le
  · refine ⟨s, L, hs1, hs2, fun i => ⟨(hL i).1, fun hle => (hL i).2.2 (le_inf (hL i).1.1.2.1 hle),
      (hL i).2.1⟩, fun L' h1 h2 h3 => hcomp L' h1 h3 (fun hle => h2 (hle.trans inf_le_right)),
      hHL⟩

theorem lemma2_3_8_4_of_inputs (hMB : MinParabolicBlocks) (h37 : Vol2Native.A37ForSQTKCat)
    (hin : Lemma246Inputs) : Lemma2_3_8_4 := by
  intro G _ _ T M H S h hH hc hS
  have hsq : IsSQTKCat H := positiveTwoCoreSQTK G T M h H hH.isGamma.1
  have hQ := Vol2Native.SQTKHypCat.quotient_pCore ↥H hsq
  obtain ⟨hcgs, s, L, hs1, hs2, hL, -, hHL⟩ := lemma2_3_8_4_strong hMB (hin.c127 G) (hin.c123 G)
    (hin.b42 G) (hin.a7 G) h hH hc hS (hin.a38 _ hQ) (h37 _ hQ)
  exact ⟨hcgs, s, L, hs1, hs2, hL, hHL⟩

end L238

end CFSG.QuasithinUnique
