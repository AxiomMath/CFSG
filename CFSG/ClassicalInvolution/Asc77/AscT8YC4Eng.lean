module

public import CFSG.ClassicalInvolution.Asc77.AscT8YB2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace T8YY

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {W : Subgroup G} {z t : G}

namespace FrameData

@[expose] def vGroupE (F : FrameData Ω W K J z t) : Subgroup G :=
  Subgroup.closure ({F.zz 0 * F.zz 1, F.zz 0 * F.zz 2} : Set G)

theorem zz_comm_of (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (F : FrameData Ω W K J z t)
    (i j : Fin 4) : F.zz i * F.zz j = F.zz j * F.zz i :=
  hc _ (F.hW i) _ (F.hW j)

theorem zz0_mul_mem_vGroupE_of (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (F : FrameData Ω W K J z t) (j : Fin 4) : F.zz 0 * F.zz j ∈ F.vGroupE := by
  have h01 : F.zz 0 * F.zz 1 ∈ F.vGroupE :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h02 : F.zz 0 * F.zz 2 ∈ F.vGroupE :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  fin_cases j
  · show F.zz 0 * F.zz 0 ∈ F.vGroupE
    rw [(F.hz 0).sq]
    exact F.vGroupE.one_mem
  · exact h01
  · exact h02
  · show F.zz 0 * F.zz 3 ∈ F.vGroupE
    have c01 := F.zz_comm_of hc 0 1
    have c02 := F.zz_comm_of hc 0 2
    have c12 := F.zz_comm_of hc 1 2
    have s0 := (F.hz 0).sq
    have s1 := (F.hz 1).sq
    have s2 := (F.hz 2).sq
    have hd : F.zz 3 = F.zz 0 * F.zz 1 * F.zz 2 := by
      have h := eq_inv_of_mul_eq_one_right F.hprod
      rw [h, mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right s0,
        inv_eq_of_mul_eq_one_right s1, inv_eq_of_mul_eq_one_right s2]
      calc F.zz 2 * (F.zz 1 * F.zz 0) = F.zz 2 * F.zz 1 * F.zz 0 := by rw [mul_assoc]
        _ = F.zz 1 * F.zz 2 * F.zz 0 := by rw [← c12]
        _ = F.zz 1 * (F.zz 2 * F.zz 0) := by rw [mul_assoc]
        _ = F.zz 1 * (F.zz 0 * F.zz 2) := by rw [← c02]
        _ = (F.zz 1 * F.zz 0) * F.zz 2 := by rw [mul_assoc]
        _ = F.zz 0 * F.zz 1 * F.zz 2 := by rw [← c01]
    have e : F.zz 0 * F.zz 3 = (F.zz 0 * F.zz 1) * (F.zz 0 * F.zz 2) := by
      rw [hd]
      calc F.zz 0 * (F.zz 0 * F.zz 1 * F.zz 2)
          = (F.zz 0 * F.zz 0) * F.zz 1 * F.zz 2 := by simp only [mul_assoc]
        _ = F.zz 1 * F.zz 2 := by rw [s0, one_mul]
        _ = (F.zz 0 * F.zz 0) * (F.zz 1 * F.zz 2) := by rw [s0, one_mul]
        _ = F.zz 0 * (F.zz 0 * F.zz 1) * F.zz 2 := by simp only [mul_assoc]
        _ = F.zz 0 * (F.zz 1 * F.zz 0) * F.zz 2 := by rw [c01]
        _ = (F.zz 0 * F.zz 1) * (F.zz 0 * F.zz 2) := by simp only [mul_assoc]
    rw [e]
    exact F.vGroupE.mul_mem h01 h02

theorem mul_mem_vGroupE_of (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (F : FrameData Ω W K J z t) (i j : Fin 4) : F.zz i * F.zz j ∈ F.vGroupE := by
  have hi := F.zz0_mul_mem_vGroupE_of hc i
  have hj := F.zz0_mul_mem_vGroupE_of hc j
  have e : F.zz i * F.zz j = (F.zz 0 * F.zz i) * (F.zz 0 * F.zz j) := by
    have c0i := F.zz_comm_of hc 0 i
    have s0 := (F.hz 0).sq
    calc F.zz i * F.zz j = (F.zz 0 * F.zz 0) * F.zz i * F.zz j := by rw [s0, one_mul]
      _ = F.zz 0 * (F.zz 0 * F.zz i) * F.zz j := by simp only [mul_assoc]
      _ = F.zz 0 * (F.zz i * F.zz 0) * F.zz j := by rw [c0i]
      _ = (F.zz 0 * F.zz i) * (F.zz 0 * F.zz j) := by simp only [mul_assoc]
  rw [e]
  exact F.vGroupE.mul_mem hi hj

theorem vGroupE_eq_of_members_of {W' K' J' : Subgroup G} {z' t' : G}
    (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hc' : ∀ x ∈ W', ∀ y ∈ W', x * y = y * x)
    (F : FrameData Ω W K J z t) (F' : FrameData Ω W' K' J' z' t')
    (hmem : ∀ j, ∃ i, (F'.ρ j).K = (F.ρ i).K) : F'.vGroupE = F.vGroupE := by
  choose σ hσ using hmem
  have hzz : ∀ j, F'.zz j = F.zz (σ j) := fun j =>
    (F'.hz j).eq (by rw [hσ j]; exact F.hz (σ j))
  have hinj : Function.Injective σ := by
    intro j j' h
    by_contra hne
    exact F'.hne j j' hne (by rw [hσ j, hσ j', h])
  have hsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hinj
  refine le_antisymm ?_ ?_
  · unfold FrameData.vGroupE
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · rw [hzz 0, hzz 1]
      exact F.mul_mem_vGroupE_of hc _ _
    · rw [hzz 0, hzz 2]
      exact F.mul_mem_vGroupE_of hc _ _
  · unfold FrameData.vGroupE
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨j0, hj0⟩ := hsurj 0
    obtain ⟨j1, hj1⟩ := hsurj 1
    obtain ⟨j2, hj2⟩ := hsurj 2
    rcases hy with rfl | rfl
    · have e0 : F.zz 0 = F'.zz j0 := by rw [hzz j0, hj0]
      have e1 : F.zz 1 = F'.zz j1 := by rw [hzz j1, hj1]
      rw [e0, e1]
      exact F'.mul_mem_vGroupE_of hc' _ _
    · have e0 : F.zz 0 = F'.zz j0 := by rw [hzz j0, hj0]
      have e2 : F.zz 2 = F'.zz j2 := by rw [hzz j2, hj2]
      rw [e0, e2]
      exact F'.mul_mem_vGroupE_of hc' _ _

end FrameData

end T8YY

end CFSG.ClassicalInvolution.Asc77
