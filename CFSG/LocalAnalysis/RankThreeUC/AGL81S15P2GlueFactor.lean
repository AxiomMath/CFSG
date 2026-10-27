module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15C118Sub
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin

theorem exists_mul_of_gnFactor_of_ystar_eq_bot {X : Type} [Group X] [Finite X]
    {T T₁ T₂ M : Subgroup X} (hTM : T ≤ M) (hc : IsC118Pair T T₁ T₂)
    (hfac : GNFactor (T.subgroupOf M) (T₁.subgroupOf M) (T₂.subgroupOf M))
    (hY : Ystar (T.subgroupOf M) (T₁.subgroupOf M) (T₂.subgroupOf M) = ⊥) :
    ∀ x ∈ M, ∃ a ∈ Subgroup.centralizer (T₁ : Set X) ⊓ M,
      ∃ b ∈ Subgroup.normalizer (T₂ : Set X) ⊓ M, x = a * b := by
  intro x hx
  obtain ⟨a, ha, y, hy, b, hb, hxy⟩ := hfac ⟨x, hx⟩
  have hT₁T : T₁ ≤ T := hc.2.1.trans (C1GN.omegaOneCenterOf_le_self T)
  have hT₂T : T₂ ≤ T := hc.2.2.2.2.1.trans (C1GN.baum_le T)
  have hT₁M : T₁ ≤ M := hT₁T.trans hTM
  have hT₂M : T₂ ≤ M := hT₂T.trans hTM
  have hY0 : Y0 (T.subgroupOf M) (T₁.subgroupOf M) (T₂.subgroupOf M) =
      gnC (T.subgroupOf M) := by
    rw [Y0, hY, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hyC : y ∈ gnC (T.subgroupOf M) := hY0 ▸ hy
  have hT₁' : T₁.subgroupOf M ≤ gnV (T.subgroupOf M) :=
    (hc.subgroupOf hTM).2.1.trans Subgroup.subset_normalClosure
  have hyc : y ∈ Subgroup.centralizer ((T₁.subgroupOf M) : Set ↥M) := by
    have h := hyC
    rw [gnC, Subgroup.mem_centralizer_iff] at h
    exact Subgroup.mem_centralizer_iff.mpr fun t ht => h t (hT₁' ht)
  have hay : a * y ∈ Subgroup.centralizer ((T₁.subgroupOf M) : Set ↥M) :=
    Subgroup.mul_mem _ ha hyc
  refine ⟨((a * y : ↥M) : X), ⟨?_, (a * y).2⟩, (b : X), ⟨?_, b.2⟩, ?_⟩
  · change ((a * y : ↥M) : X) ∈ Subgroup.centralizer (T₁ : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : (⟨t, hT₁M ht⟩ : ↥M) ∈ T₁.subgroupOf M := Subgroup.mem_subgroupOf.mpr ht
    have h := Subgroup.mem_centralizer_iff.mp hay ⟨t, hT₁M ht⟩ ht'
    simpa using congrArg (fun z : ↥M => (z : X)) h
  · have hmap : (b : X) ∈ (Subgroup.normalizer ((T₂.subgroupOf M) : Set ↥M)).map M.subtype :=
      ⟨b, hb, rfl⟩
    have h := Subgroup.le_normalizer_map M.subtype hmap
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT₂M] at h
  · have h := congrArg (fun z : ↥M => (z : X)) hxy
    simpa using h

end CFSG.LocalAnalysis.RankThreeUC.S15

end
