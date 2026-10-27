module

public import Mathlib.Algebra.Group.Subgroup.Basic

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

@[expose] def conjClosure {G : Type} [Group G] (Y : Subgroup G) : Subgroup G :=
  Subgroup.closure (⋃ g : G, ((Y.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))

theorem conj_mem_conjClosure {G : Type} [Group G] (Y : Subgroup G) (g x : G)
    (hx : x ∈ conjClosure Y) : g * x * g⁻¹ ∈ conjClosure Y := by
  have hle : conjClosure Y ≤ (conjClosure Y).comap (MulAut.conj g).toMonoidHom := by
    unfold conjClosure
    rw [Subgroup.closure_le]
    intro x hxS
    obtain ⟨h, hxh⟩ := Set.mem_iUnion.mp hxS
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxh
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine Set.mem_iUnion.mpr ⟨g * h, Subgroup.mem_map.mpr ⟨y, hy, ?_⟩⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact hle hx

theorem conjClosure_eq_top_of_normalClosure {G : Type} [Group G] {Y : Subgroup G}
    (hgen : Subgroup.normalClosure (Y : Set G) = ⊤) : conjClosure Y = ⊤ := by
  have hnorm : (conjClosure Y).Normal := ⟨fun n hn g => conj_mem_conjClosure Y g n hn⟩
  have hYle : (Y : Set G) ⊆ conjClosure Y := by
    intro y hy
    apply Subgroup.subset_closure
    refine Set.mem_iUnion.mpr ⟨1, Subgroup.mem_map.mpr ⟨y, hy, ?_⟩⟩
    simp
  have h :=Subgroup.normalClosure_le_normal (N := conjClosure Y) hYle
  rw [hgen] at h
  exact top_le_iff.mp h

end CFSG.HardMathSupport.RichardWeiss.Proving
