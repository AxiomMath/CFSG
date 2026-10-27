module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem inf_pCoreOf_le_pCoreOf (p : ℕ) {X H : Subgroup G} (hXH : X ≤ H) :
    X ⊓ CFSG.Open.pCoreOf p H ≤ CFSG.Open.pCoreOf p X := by
  set N : Subgroup G := X ⊓ CFSG.Open.pCoreOf p H with hN
  have hNX : N ≤ X := inf_le_left
  have hNp : IsPGroup p N :=
    IsPGroup.to_le ((CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype) inf_le_right
  have hconjN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    refine ⟨X.mul_mem (X.mul_mem hx hn.1) (X.inv_mem hx), ?_⟩
    obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.mp hn.2
    exact Subgroup.mem_map.mpr
      ⟨_, (inferInstance : (CFSG.pCore p ↥H).Normal).conj_mem n' hn' (⟨x, hXH hx⟩ : ↥H), rfl⟩
  have hNnormal : (N.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNX]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hconjN x hx n
    · intro hn
      have h := hconjN x⁻¹ (X.inv_mem hx) (x * n * x⁻¹) hn
      rwa [show x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n from by group] at h
  have hNsubp : IsPGroup p ↥(N.subgroupOf X) :=
    hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNX).symm
  have hcore : N.subgroupOf X ≤ CFSG.pCore p ↥X := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (N.subgroupOf X) (le_iSup_of_le hNnormal (le_iSup_of_le hNsubp le_rfl))
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hcore

end CFSG.GroupTheory
