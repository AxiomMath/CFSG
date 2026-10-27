module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fzl_R_le_N2 (t x₁ x₂ : G) : fzR t x₁ x₂ ≤ fzN2 t x₁ x₂ := by
  unfold fzR CFSG.Open.pCoreOf
  exact Subgroup.map_subtype_le _

theorem fzl_R_isPGroup (t x₁ x₂ : G) : IsPGroup 2 (fzR t x₁ x₂) := by
  unfold fzR CFSG.Open.pCoreOf
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(fzN2 t x₁ x₂))).map _

theorem fzl_R_normal (t x₁ x₂ : G) :
    ∀ n ∈ fzN2 t x₁ x₂, ∀ r ∈ fzR t x₁ x₂, n * r * n⁻¹ ∈ fzR t x₁ x₂ := by
  intro n hn r hr
  unfold fzR CFSG.Open.pCoreOf at hr ⊢
  rw [Subgroup.mem_map] at hr ⊢
  obtain ⟨x, hx, rfl⟩ := hr
  refine ⟨⟨n, hn⟩ * x * ⟨n, hn⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥(fzN2 t x₁ x₂))).conj_mem x hx ⟨n, hn⟩
  · simp

theorem fzl_R_le_T {t x₁ x₂ : G} {S T₂ : Subgroup G} (hT : IsFzT2 t x₁ x₂ S T₂) :
    fzR t x₁ x₂ ≤ T₂ := by
  set N : Subgroup G := fzN2 t x₁ x₂ with hN
  have hR : fzR t x₁ x₂ = (CFSG.pCore 2 ↥N).map N.subtype := by
    unfold fzR CFSG.Open.pCoreOf
    rw [hN]
  rw [hR]
  let T' : Subgroup ↥N := T₂.subgroupOf N
  have hT'p : IsPGroup 2 T' := hT.isPGroup.comap_subtype
  have hT'index : ¬ 2 ∣ T'.index := by
    show ¬ 2 ∣ (T₂.comap N.subtype).index
    rw [Subgroup.index_comap, Subgroup.range_subtype]
    simpa only [hN] using hT.odd_relIndex
  have hcore_le : CFSG.pCore 2 ↥N ≤ (hT'p.toSylow hT'index : Subgroup ↥N) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥N)).le_sylow_of_normal _
  calc
    (CFSG.pCore 2 ↥N).map N.subtype
        ≤ (hT'p.toSylow hT'index : Subgroup ↥N).map N.subtype :=
          Subgroup.map_mono hcore_le
    _ = T'.map N.subtype := by simp only [IsPGroup.toSylow_coe]
    _ = T₂ := by
      show (T₂.comap N.subtype).map N.subtype = T₂
      rw [Subgroup.comap_subtype T₂ N]
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT.le_N2]

end CFSG.OddStandard.SmallF3.FritzII
