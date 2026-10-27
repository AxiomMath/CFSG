module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourBlocks

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank

namespace L246A7

variable {G : Type} [Group G] [Finite G]

theorem isSQTKCat_of_le {H L : Subgroup G} (hLH : L ≤ H) (hH : IsSQTKCat ↥H) :
    IsSQTKCat ↥L :=
  CFSG.SectionRank.IsSQTKCat.of_le hLH hH

theorem pushUpObstruction_of_mem_uFamHat_gen {X T M U : Subgroup G} (hX : CharTwo X)
    (hSQ : IsSQTKCat ↥X) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M) (hU : U ∈ uFamHat X T)
    (hUM : ¬ U ≤ M) : PushUpObstruction T U := by
  have hUX : U ≤ X := hU.1.1
  have hTU : T ≤ U := hU.1.2.1.le
  have hmin := L238.isMinimalParabolic_of_mem_uFamHat hT hU
  refine ⟨C1GN.isSylowTwoOf_of_le hT hTU hUX, C1GN.charTwo_of_le hX hT hTU hUX, hmin,
    isSQTKCat_of_le hUX hSQ, ?_⟩
  intro R hR1 hRT hRc hUN
  apply hUM
  refine le_trans ?_ hcgs
  refine le_trans (le_inf hUX hUN) ?_
  exact le_iSup_of_le R (le_iSup_of_le hRT (le_iSup_of_le hR1 (le_iSup_of_le hRc le_rfl)))

theorem exists_block_of_mem_uFamHat_gen (hMB : MinParabolicBlocks) {X T M U : Subgroup G}
    (hX : CharTwo X) (hSQ : IsSQTKCat ↥X) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M)
    (hTM : T ≤ M) (hU : U ∈ uFamHat X T) (hUM : ¬ U ≤ M) :
    ∃ L : Subgroup G, IsChi0Block U L ∧ ⁅L, thompsonJ T⁆ = L ∧ ¬ L ≤ M ∧
      U = conjJoin T L ⊔ T := by
  obtain ⟨L, hL, hLJ, hPL, -⟩ :=
    hMB G T U (pushUpObstruction_of_mem_uFamHat_gen hX hSQ hT hcgs hU hUM)
  refine ⟨L, hL, hLJ, ?_, hPL⟩
  intro hLM
  apply hUM
  rw [hPL]
  refine sup_le (iSup_le fun s => ?_) hTM
  rintro _ ⟨y, hy, rfl⟩
  have hsM : (s : G) ∈ M := hTM s.2
  show (s : G) * y * (s : G)⁻¹ ∈ M
  exact M.mul_mem (M.mul_mem hsM (hLM hy)) (M.inv_mem hsM)

theorem le_of_no_chiBlock (hMB : MinParabolicBlocks) (h127 : L238.C127StatementCat (G := G))
    (h123 : L238.C123TwoCgsStatement (G := G)) (hB42 : L238.AltBlockStatementJCat (G := G))
    {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat ↥X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hT0 : T ≠ ⊥)
    (hcgs : cgsIn X T ≤ M) (hno : ∀ L : Subgroup G, ¬ IsChiBlock X L) : X ≤ M := by
  have hcharT : (T.subgroupOf T).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hNTM : X ⊓ Subgroup.normalizer (T : Set G) ≤ M := by
    refine le_trans ?_ hcgs
    exact le_iSup_of_le T (le_iSup_of_le le_rfl (le_iSup_of_le hT0 (le_iSup_of_le hcharT le_rfl)))
  have hTM : T ≤ M := fun t ht => hNTM ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  obtain ⟨-, -, hXeq⟩ := uHat_normal_and_eq_sup hT.1
  have hbot : (⨆ L ∈ C1GN.chiBlocksOutside X T M, L) = ⊥ := by
    refine iSup₂_eq_bot.2 fun L hL => ?_
    exact absurd hL.1 (hno L)
  rw [hXeq]
  refine sup_le (iSup₂_le fun U hU => ?_) hNTM
  have := L238.uFamHat_le_sup_chiBlocks_of_blocks h127 h123 hB42 hX hSQ h38 hT hcgs hTM hU
    (fun hUM => exists_block_of_mem_uFamHat_gen hMB hX hSQ hT hcgs hTM hU hUM)
  rwa [hbot, sup_bot_eq] at this

end L246A7

end CFSG.QuasithinUnique
