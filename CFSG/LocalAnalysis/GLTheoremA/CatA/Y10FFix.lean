module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {G : Type} [Group G]

theorem mem_fixSubgroup_conjAut' (K : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (k : K) : k ∈ fixSubgroup (conjAut' K y hy) ↔ (k : G) ∈ Subgroup.centralizer ({y} : Set G) := by
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [coe_conjAut'] at h'
    have : y * (k : G) = (k : G) * y := by
      calc y * (k : G) = y * (k : G) * y⁻¹ * y := by group
        _ = (k : G) * y := by rw [h']
    exact this.symm
  · intro h
    apply Subtype.ext
    rw [coe_conjAut']
    calc y * (k : G) * y⁻¹ = (y * (k : G)) * y⁻¹ := rfl
      _ = ((k : G) * y) * y⁻¹ := by rw [← h]
      _ = k := by group

theorem map_fixSubgroup_conjAut' (K : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G)) :
    (fixSubgroup (conjAut' K y hy)).map K.subtype = K ⊓ Subgroup.centralizer ({y} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.coe_subtype]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, (mem_fixSubgroup_conjAut' K hy k).1 hk⟩
  · rintro ⟨hxK, hx⟩
    exact ⟨⟨x, hxK⟩, (mem_fixSubgroup_conjAut' K hy ⟨x, hxK⟩).2 hx, rfl⟩

theorem conjAut'_pow (K : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G)) {p : ℕ}
    (hyp : y ^ p = 1) : conjAut' K y hy ^ p = 1 := by
  unfold conjAut'
  rw [← map_pow]
  have : (⟨y, hy⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := Subtype.ext (by simpa using hyp)
  rw [this, map_one]

theorem glaPComponent_fixSubgroup_conjAut' [Finite G] {p : ℕ} (hp : p.Prime) (K : Subgroup G) {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) {J : Subgroup G}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J) :
    J ≤ K ∧ GLAPComponent p (fixSubgroup (conjAut' K y hy)) (J.subgroupOf K) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  refine ⟨hJK, ?_⟩
  rw [← glaPComponent_map_iff hp K.subtype_injective, subgroupOf_map_subtype_of_le hJK,
    map_fixSubgroup_conjAut']
  exact hJ

end CFSG.LocalAnalysis.GLTheoremA.Y10F
