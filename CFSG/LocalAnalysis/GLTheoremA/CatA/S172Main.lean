module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Finish

variable {G : Type} [Group G] [Finite G]

theorem finish172 (hb : CatDistinct.OrderBridge) {p : ℕ} (hp : p.Prime) {B L D K J D₁ K₁ : Subgroup G}
    {x : G} (hBel : IsElemAbelian p B) (hx1 : x ≠ 1) (hstd : GLAStdSubPre p B x L D K)
    (hpre : GLAStdSubPre p B x L D₁ K₁) (h126 : Type126 p L K J)
    (hT : Type172 p L K J K₁ (GLALayer (L ⊓ cs (D ⊔ D₁)))) :
    ∃ D₁ K₁ KE : Subgroup G, GLAStdSub p B x L D₁ K₁ ∧ IsE3 p B (D ⊔ D₁) ∧
      KE = GLALayer (L ⊓ cs (D ⊔ D₁)) ∧ Type172 p L K J K₁ KE ∧ ∀ J' : Subgroup G, ¬ Type126 p L K₁ J' := by
  have hKne : K₁ ≠ K := fun h => not_type126_of_type172 hb hT J (by rw [h]; exact h126)
  have hDne : D ≠ D₁ := by
    intro h
    apply hKne
    rw [hpre.2.2.2.2.1, hstd.2.2.2.2.1, h]
  exact ⟨D₁, K₁, _, ⟨hpre, fun _ => not_small_of_type172 hb hT⟩,
    isE3_sup_of_ne hp hBel hstd.1 hpre.1 hstd.2.2.1 hpre.2.2.1 hstd.2.2.2.1 hpre.2.2.2.1 hx1 hDne, rfl, hT,
    not_type126_of_type172 hb hT⟩

end Finish

section Main

theorem i172_of_facts_bridge (hb : CatDistinct.OrderBridge) (hA : S172FactA) (hB : S172FactB)
    (hC : S172FactC) (G : Type) [Group G] [Finite G] : I172At G := by
  classical
  intro p B x L D K hp hp2 hS h4 hq hchev hsplit hstd h121 h126
  have hid : InnerDiagMarking B L := innerDiagMarking_of_split16 hsplit
  have he3 : ∃ E : Subgroup G, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (K ⊓ cs E) ≠ ⊥ := by
    rcases h121 with ⟨hU, -, -, -, hL'⟩ | ⟨-, -, E, hE, hDE, -, hKE⟩
    · exact (not_concl121_first hb h126 hU hL').elim
    · exact ⟨E, hE, hDE, hKE⟩
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, L ⊔ B = H := ⟨_, rfl⟩
  have hLH : L ≤ H := hH ▸ le_sup_left
  have hBH : B ≤ H := hH ▸ le_sup_right
  have hDB : D ≤ B := hstd.1.1
  have hDH : D ≤ H := hDB.trans hBH
  have hKL : K ≤ L := by
    rw [hstd.1.2.2.2.2.1]
    exact (Y10F.glaLayer_le _).trans inf_le_left
  have hKH : K ≤ H := hKL.trans hLH
  have hxH : x ∈ H := hBH (IsSStarMax.essential hS).1
  have hcfg := cfg172_of_field hp hp2 hS h4 hq hid hstd.1 he3 hH (⟨x, hxH⟩ : ↥H) rfl
  have hBel : IsElemAbelian p B := (IsSStarMax.bmax hS).1
  have hx1 : x ≠ 1 := (IsSStarMax.essential hS).2.1
  have h126' := h126
  rcases h126 with ⟨hp3, n, hn, hL, hK, hJ⟩ | ⟨hp3, n, hn, hL, hK, hJ⟩ |
    ⟨n, k, hn, hk, hpk, hL, hK, hJ⟩
  · subst hp3
    obtain ⟨D₁', K₁', hpre, hK₁, hKE⟩ := hA n hn ↥H _ _ _ _ _ hcfg
      ((catalogIs_pSimple_subgroupOf_iff hLH _).2 hL) ((catalogIs_pSimple_subgroupOf_iff hKH _).2 hK)
    obtain ⟨hpre', hKE'⟩ := lift_conclusion hBH hLH hDH (⟨x, hxH⟩ : ↥H) rfl D₁' K₁' hpre
    refine finish172 hb hp hBel hx1 hstd.1 hpre' h126' (Or.inl ⟨rfl, n, hn, hL, hK, hJ, ?_, ?_⟩)
    · exact (catalogIs_pSimple_map_iff K₁' _).2 hK₁
    · rw [hKE']
      exact (catalogIs_pSimple_map_iff _ _).2 hKE
  · subst hp3
    obtain ⟨D₁', K₁', hpre, hK₁, hKE⟩ := hB n hn ↥H _ _ _ _ _ hcfg
      ((catalogIs_pSimple_subgroupOf_iff hLH _).2 hL) ((catalogIs_pSimple_subgroupOf_iff hKH _).2 hK)
    obtain ⟨hpre', hKE'⟩ := lift_conclusion hBH hLH hDH (⟨x, hxH⟩ : ↥H) rfl D₁' K₁' hpre
    refine finish172 hb hp hBel hx1 hstd.1 hpre' h126' (Or.inr (Or.inl ⟨rfl, n, hn, hL, hK, hJ, ?_, ?_⟩))
    · exact (catalogIs_pSimple_map_iff K₁' _).2 hK₁
    · rw [hKE']
      exact (catalogIs_pSimple_map_iff _ _).2 hKE
  · obtain ⟨D₁', K₁', hpre, hK₁, hKE⟩ := hC p n k hn hk hpk ↥H _ _ _ _ _ hcfg
      ((catalogIs_pSimple_subgroupOf_iff hLH _).2 hL) ((catalogIs_pSimple_subgroupOf_iff hKH _).2 hK)
    obtain ⟨hpre', hKE'⟩ := lift_conclusion hBH hLH hDH (⟨x, hxH⟩ : ↥H) rfl D₁' K₁' hpre
    refine finish172 hb hp hBel hx1 hstd.1 hpre' h126' (Or.inr (Or.inr ⟨n, k, hn, hk, hpk, hL, hK, hJ, ?_, ?_⟩))
    · exact (catalogIs_pSimple_map_iff K₁' _).2 hK₁
    · rw [hKE']
      exact (catalogIs_pSimple_map_iff _ _).2 hKE

end Main

end CFSG.LocalAnalysis.GLTheoremA.S172

end
