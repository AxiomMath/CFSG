module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

theorem normalizer_inf_le_map_of_le {A : Type} [Group A] {K : Subgroup A} {S P : Subgroup ↥K}
    (h : normalizer (S : Set ↥K) ≤ P) :
    normalizer ((S.map K.subtype : Subgroup A) : Set A) ⊓ K ≤ P.map K.subtype := by
  rintro a ⟨ha, haK⟩
  have h1 : (⟨a, haK⟩ : ↥K) ∈ (normalizer ((S.map K.subtype : Subgroup A) : Set A)).subgroupOf K :=
    ha
  rw [Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le S)] at h1
  have h2 : (S.map K.subtype).subgroupOf K = S :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective S
  rw [h2] at h1
  exact ⟨⟨a, haK⟩, h h1, rfl⟩

theorem kFact131_of_holds
    (h : ∀ (S : Type) [Group S] [Finite S], IsChevSimple 2 S →
      CFSG.LieType.BorelTits.Holds S 2) : KFact131 := by
  intro A _ _ K Q hK hQK hQ2 hQ1
  have hQ' : Q.subgroupOf K ≠ ⊥ := by
    intro hbot
    apply hQ1
    have h1 := Subgroup.subgroupOf_map_subtype Q K
    rw [hbot, Subgroup.map_bot, inf_eq_left.mpr hQK] at h1
    exact h1.symm
  obtain ⟨S, P', hP', hN, -, hQP, hSP⟩ :=
    h ↥K hK (Q.subgroupOf K) hQ' hQ2.comap_subtype
  have h2 : (Q.subgroupOf K).map K.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQK]
  refine ⟨P'.map K.subtype, ⟨Subgroup.map_subtype_le P', (S : Subgroup ↥K).map K.subtype,
    ⟨S, rfl⟩, normalizer_inf_le_map_of_le hSP⟩, ?_, ?_⟩
  · rw [← h2, ← CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype]
    exact Subgroup.map_mono hQP
  · have h3 := normalizer_inf_le_map_of_le (K := K) (S := Q.subgroupOf K) (P := P') hN
    rwa [h2] at h3

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
