module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusJoin

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

variable {G : Type} [Group G]

theorem noNormal3_of_normal (h3 : pCore 3 G = ⊥) (N : Subgroup G) [N.Normal] : NoNormal3 N := by
  intro P hPN hPp hPn
  have hQ0 : (pCore 3 N).map N.subtype = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← h3]
    refine le_sSup ⟨?_, ?_⟩
    · refine ⟨fun x hx g => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      have hinv : (pCore 3 N).map (MulAut.conjNormal g).toMonoidHom = pCore 3 N :=
        pCore_map_iso 3 (MulAut.conjNormal g)
      have hmem : (MulAut.conjNormal g : MulAut N) y ∈ pCore 3 N := by
        have : (MulAut.conjNormal g : MulAut N) y ∈
            (pCore 3 N).map (MulAut.conjNormal g).toMonoidHom := ⟨y, hy, rfl⟩
        rwa [hinv] at this
      exact ⟨_, hmem, by simp⟩
    · exact (pCore_isPGroup (p := 3) (G := N)).map N.subtype
  have hPnorm : (P.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr hPn
  have hP3 : IsPGroup 3 (P.subgroupOf N) := hPp.comap_of_injective N.subtype N.subtype_injective
  have hle : P.subgroupOf N ≤ pCore 3 N := le_sSup ⟨hPnorm, hP3⟩
  have : P ≤ (pCore 3 N).map N.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPN]
    exact Subgroup.map_mono hle
  rw [hQ0] at this
  exact le_bot_iff.mp this

variable [Finite G]

theorem exists_max_commProd {Q : Type} [Group Q] (hQ : GoodQ Q) (h3 : pCore 3 G = ⊥) :
    ∃ M : Subgroup G, M.Normal ∧ IsCommProd Q M ∧
      ∀ N : Subgroup G, N.Normal → IsCommProd Q N → N ≤ M := by
  classical
  let C : Set (Subgroup G) := {N | N.Normal ∧ IsCommProd Q N}
  have hCne : C.Nonempty := ⟨⊥, inferInstance, isCommProd_bot Q⟩
  obtain ⟨M, hMC, hMmax⟩ := Set.exists_max_image C (fun N => Nat.card N) (Set.toFinite C) hCne
  refine ⟨M, hMC.1, hMC.2, fun N hN hNc => ?_⟩
  have hM := hMC.1
  have hMN : M ⊔ N ∈ C := by
    refine ⟨Subgroup.sup_normal M N, ?_⟩
    exact isCommProd_sup hQ hMC.2 hNc Subgroup.le_normalizer_of_normal
      Subgroup.le_normalizer_of_normal (noNormal3_of_normal h3 _)
  have hcard := hMmax _ hMN
  have heq : M = M ⊔ N := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  rw [heq]
  exact le_sup_right

theorem lemma_2_4_one (h3 : pCore 3 G = ⊥) :
    (NOne G).Normal ∧ IsCommProd SL23 (NOne G) ∧
      ∀ N : Subgroup G, N.Normal → IsCommProd SL23 N → N ≤ NOne G := by
  obtain ⟨M, hM, hMc, hmax⟩ := exists_max_commProd goodQ_SL23 h3
  have hNOne : NOne G = M :=
    le_antisymm (sSup_le fun N hN => hmax N hN.1 hN.2) (le_sSup ⟨hM, hMc⟩)
  rw [hNOne]
  exact ⟨hM, hMc, hmax⟩

theorem lemma_2_4_two (h3 : pCore 3 G = ⊥) :
    (NTwo G).Normal ∧ IsCommProd A4 (NTwo G) ∧
      ∀ N : Subgroup G, N.Normal → IsCommProd A4 N → N ≤ NTwo G := by
  obtain ⟨M, hM, hMc, hmax⟩ := exists_max_commProd goodQ_A4 h3
  have hNTwo : NTwo G = M :=
    le_antisymm (sSup_le fun N hN => hmax N hN.1 hN.2) (le_sSup ⟨hM, hMc⟩)
  rw [hNTwo]
  exact ⟨hM, hMc, hmax⟩

end CFSG.OddStandard.Solomon75
