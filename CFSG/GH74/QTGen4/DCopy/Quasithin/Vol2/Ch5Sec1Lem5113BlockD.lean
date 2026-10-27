module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113BlockA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_13_four_block_bc_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n →
      (C126Third (L ⊔ T) T ∨ C126Third H T) →
      ¬ C126Third H T ∧ 2 < n

theorem stmt5_1_13_four_block_bcd_of_F4 (hbc : Stmt5_1_13_four_block_bc_F4) :
    Stmt5_1_13_four_block_bcd_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' hZV' hnat C _ hCB
    hCch hdich _ _
  obtain ⟨hnb, hn⟩ := hbc G T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' hZV' hnat
    hdich
  refine ⟨hnb, hn, ?_⟩

  have hBC : Subgroup.normalizer (baum T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := baum T)
      (C.subgroupOf (baum T))
    rwa [Subgroup.map_subgroupOf_eq_of_le hCB] at this
  refine sup_le ((m.le_normalizer_baum_of_nat hV' hZV' hnat hZL).trans hBC) ?_
  exact (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)).trans hBC

end CFSG.Quasithin.H13
