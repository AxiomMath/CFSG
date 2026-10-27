module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCAdaptModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane longBlock
  longInv coords stdPlane)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Central

variable {F : Type} [Field F]

theorem planeGroup_central_eq_one {P : Submodule F (Fin 2 ⊕ Fin 2 → F)} (hP : IsHyperbolicPlane P)
    {r : StatedSp 2 F} (hr : r ∈ planeGroup P) (hc : r ∈ Subgroup.center (StatedSp 2 F)) :
    r = 1 := by
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP (0 : Fin 2)
  rw [hg] at hr
  obtain ⟨y, ⟨B, rfl⟩, rfl⟩ := hr
  have hc' : g * longBlock F 2 0 B * g⁻¹ ∈ Subgroup.center (StatedSp 2 F) := hc
  have h1 := Models.SymplecticPairs.mem_center_of_conj_mem_center hc'
  have h2 : longBlock F 2 0 B = 1 :=
    Models.SymplecticPairs.eq_one_of_mem_center_of_mem_suppGroup h1
      (Models.SymplecticPairs.isSupp_longBlock _ B) (t := Sum.inl (1 : Fin 2)) (by
        rintro (h | h)
        · have := Sum.inl_injective h
          simp at this
        · exact Sum.inl_ne_inr h)
  simp [h2]

theorem longInv_mul_self {n : ℕ} (k : Fin n) : longInv F n k * longInv F n k = 1 := by
  rw [longInv, ← map_mul]
  simp

theorem longInv_ne_one (h2 : (2 : F) ≠ 0) {n : ℕ} (k : Fin n) : longInv F n k ≠ 1 := by
  intro h
  have h1 := congrArg (fun x => mat n F x (Sum.inl k) (Sum.inl k)) h
  simp only [Models.SymplecticPairs.mat_longInv, map_one, Matrix.diagonal_apply_eq,
    Matrix.one_apply_eq] at h1
  simp [coords] at h1
  exact h2 (by linear_combination -h1)

theorem map_longInv_ne_one (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 2 ≤ n) {Y : Type*} [Group Y]
    (φ : StatedSp n F →* Y) (hφ : φ.ker ≤ Subgroup.center (StatedSp n F)) (k : Fin n) :
    φ (longInv F n k) ≠ 1 := by
  intro h
  obtain ⟨l, hl⟩ : ∃ l : Fin n, l ≠ k := by
    by_cases hk : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
    · exact ⟨⟨0, by omega⟩, fun h => hk (by rw [← h])⟩
  refine longInv_ne_one h2 k (Models.SymplecticPairs.injOn_suppGroup_of_ker_le_center φ hφ
    (S := coords k) (t := Sum.inl l) ?_ _ ?_ h)
  · rintro h'
    rcases Models.SymplecticPairs.mem_coords.1 h' with h'' | h''
    · exact hl (Sum.inl_injective h'')
    · exact Sum.inl_ne_inr h''
  · rw [← Models.SymplecticPairs.range_longBlock]
    exact ⟨-1, rfl⟩

theorem commutes_planeGroup_stdPlane :
    ∀ x ∈ planeGroup (stdPlane F 2 0), ∀ y ∈ planeGroup (stdPlane F 2 1), x * y = y * x := by
  rw [Models.SymplecticPairs.planeGroup_stdPlane, Models.SymplecticPairs.planeGroup_stdPlane]
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact (Models.SymplecticPairs.commute_longBlock_longBlock (by decide) A B).eq

end Central

end CFSG.ClassicalInvolution.Q3.Q3Z
