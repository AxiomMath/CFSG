module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row26W

variable {G : Type} [Group G] [Finite G]

@[expose] def Row1526W (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      ∀ U : Subgroup ↥M, U = ⁅L, gnV (T.subgroupOf M)⁆ →
        (∃ N₁ N₂ : Subgroup ↥M, IsNaturalLThreeTwo L N₁ ∧ N₁ ⊔ N₂ = U ∧
            (N₂ = ⊥ ∨ (IsNaturalLThreeTwo L N₂ ∧ N₁ ⊓ N₂ = ⊥ ∧
              ∃ f : ↥N₁ ≃* ↥N₂, ∀ l ∈ L, ∀ a b : ↥N₁,
                (b : ↥M) = l * (a : ↥M) * l⁻¹ → (f b : ↥M) = l * (f a : ↥M) * l⁻¹))) ∧
        pElementSubgroup 7 (cMLStar (T.subgroupOf M) Ls) ≤ Subgroup.centralizer (U : Set ↥M) ∧
        CFSG.CGT.Timmesfeld75.IsTI (U.map M.subtype) ∧
        ((∀ I ∈ CY (T.subgroupOf M) T₁ T₂,
            Nat.card ↥⁅I, gnV (T.subgroupOf M)⁆ ≤ Nat.card ↥U) →
          wSub G M T U ≤ (Subgroup.centralizer
            ((⁅gnV (T.subgroupOf M), yLifts (T.subgroupOf M) T₁ T₂⁆ : Subgroup ↥M) :
              Set ↥M)).map M.subtype)

theorem wSub_map_conj_le {M T : Subgroup G} (U : Subgroup ↥M) {n : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    (wSub G M T U).map (MulAut.conj n).toMonoidHom ≤ wSub G M T U := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold wSub
  refine iSup₂_le fun A hA => ?_
  obtain ⟨⟨g, rfl⟩, hAT⟩ := hA
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_iSup₂_of_le
    (((U.map M.subtype).map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom)
    ⟨⟨n * g, ?_⟩, ?_⟩ le_rfl
  · rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  · rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hn _).1 (hAT ha)

theorem normalizer_le_normalizer_wSub (M T : Subgroup G) (U : Subgroup ↥M) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer ((wSub G M T U : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge (wSub_map_conj_le U hn) ?_
  exact (Subgroup.card_map_of_injective (MulAut.conj n).injective).ge

theorem T_le_normalizer_wSub (M T : Subgroup G) (U : Subgroup ↥M) :
    T ≤ Subgroup.normalizer ((wSub G M T U : Subgroup G) : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_wSub M T U)

theorem wSub_props (M T : Subgroup G) (hT : IsPGroup 2 T) (U : Subgroup ↥M)
    (hUT : U.map M.subtype ≤ T) (hU : U ≠ ⊥) :
    IsPGroup 2 (wSub G M T U) ∧ wSub G M T U ≠ ⊥ := by
  have hle : wSub G M T U ≤ T := by
    unfold wSub
    exact iSup₂_le fun A hA => hA.2
  refine ⟨hT.to_le hle, ?_⟩
  intro hW
  apply hU
  have hUW : U.map M.subtype ≤ wSub G M T U := by
    unfold wSub
    refine le_iSup₂_of_le (U.map M.subtype) ⟨⟨1, ?_⟩, hUT⟩ le_rfl
    ext x
    simp [MulAut.conj_apply]
  rw [hW, le_bot_iff] at hUW
  exact (Subgroup.map_eq_bot_iff_of_injective U M.subtype_injective).1 hUW

end Row26W

end CFSG.LocalAnalysis.RankThreeUC.S15
