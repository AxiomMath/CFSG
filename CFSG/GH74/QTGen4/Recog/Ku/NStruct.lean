module

public import CFSG.GH74.QTGen4.Recog.Ku.HGlueC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem H_le_kuN (h : KuHyp G T M H P z) : H ≤ kuN P H :=
  h.H_le_normalizer_kuA

theorem T_le_kuN (h : KuHyp G T M H P z) : T ≤ kuN P H :=
  h.tH.trans h.H_le_kuN

theorem M_inf_normalizer_V2_le_kuN [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ≤ kuN P H :=
  h.M_inf_normalizer_V2_le_normalizer_kuA

theorem kuA_comm [KuLeaf LeafIsMulCommutativeKuA]
    (h : KuHyp G T M H P z) {x y : G} (hx : x ∈ kuA P H) (hy : y ∈ kuA P H) :
    x * y = y * x := by
  have hc : ∀ a b : ↥(kuA P H), a * b = b * a :=
    fun a b => h.isMulCommutative_kuA.is_comm.comm a b
  exact congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)

theorem M_inf_kuN_eq [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    M ⊓ kuN P H = M ⊓ Subgroup.normalizer (kuV2 T M : Set G) := by
  apply le_antisymm
  · rintro g ⟨hgM, hgN⟩
    have hgN' : g ∈ Subgroup.normalizer (kuA P H : Set G) := hgN
    have hgV : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
      have := hgM
      rw [h.mNorm] at this
      exact this
    refine ⟨hgM, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩
    rw [← h.kuA_inf_pCore_M]
    simp only [Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp hgN' x)
      (Subgroup.mem_normalizer_iff.mp hgV x)
  · intro g hg
    exact ⟨hg.1, h.M_inf_normalizer_V2_le_kuN hg⟩

theorem centralizer_kuA_eq [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafHInfCentralizerKuA]
    (h : KuHyp G T M H P z) :
    Subgroup.centralizer (kuA P H : Set G) = kuA P H := by
  apply le_antisymm
  · intro g hg
    have hzA : z ∈ kuA P H := h.z_mem_kuA
    have hgz : g ∈ H := by
      rw [h.hCz]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hg z hzA).symm)
    have hmem : g ∈ H ⊓ Subgroup.centralizer (kuA P H : Set G) := ⟨hgz, hg⟩
    rwa [h.H_inf_centralizer_kuA] at hmem
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h.kuA_comm hy hx)

end KuHyp

end CFSG.GH74.QTGen4.Ku
