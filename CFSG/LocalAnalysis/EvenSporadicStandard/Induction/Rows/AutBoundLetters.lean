module

public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.EvenSporadicStandard.Co1Cent

@[expose] def letterM {M : Type*} [Group M] (gs : List M) (j : ℤ) : M :=
  if 0 < j then gs.getD (j.toNat - 1) 1 else (gs.getD ((-j).toNat - 1) 1)⁻¹

@[expose] def wordM {M : Type*} [Group M] (gs : List M) (w : List ℤ) : M :=
  w.foldl (fun x j => x * letterM gs j) 1

theorem map_getD {M M' : Type*} [Group M] [Group M'] (φ : M →* M') (gs : List M) (k : ℕ) :
    φ (gs.getD k 1) = (gs.map φ).getD k 1 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases gs[k]? <;> simp

theorem map_letterM {M M' : Type*} [Group M] [Group M'] (φ : M →* M') (gs : List M) (j : ℤ) :
    φ (letterM gs j) = letterM (gs.map φ) j := by
  unfold letterM
  split_ifs
  · exact map_getD φ gs _
  · rw [map_inv, map_getD]

theorem map_wordM {M M' : Type*} [Group M] [Group M'] (φ : M →* M') (gs : List M) (w : List ℤ) :
    φ (wordM gs w) = wordM (gs.map φ) w := by
  unfold wordM
  suffices ∀ x : M, φ (w.foldl (fun x j => x * letterM gs j) x) =
      w.foldl (fun x j => x * letterM (gs.map φ) j) (φ x) by simpa using this 1
  induction w with
  | nil => intro x; rfl
  | cons j w ih =>
    intro x
    rw [List.foldl_cons, List.foldl_cons, ih, map_mul, map_letterM]

theorem wordM_mem {M : Type*} [Group M] (H : Subgroup M) (gs : List M) (h : ∀ g ∈ gs, g ∈ H)
    (w : List ℤ) : wordM gs w ∈ H := by
  have hl : ∀ j, letterM gs j ∈ H := by
    intro j
    unfold letterM
    split_ifs
    · rw [List.getD_eq_getElem?_getD]
      cases hk : gs[(j.toNat - 1)]? with
      | none => simp [H.one_mem]
      | some g => simpa using h g (List.mem_of_getElem? hk)
    · rw [List.getD_eq_getElem?_getD]
      cases hk : gs[((-j).toNat - 1)]? with
      | none => simp [H.one_mem]
      | some g => simpa using H.inv_mem (h g (List.mem_of_getElem? hk))
  unfold wordM
  suffices ∀ x ∈ H, w.foldl (fun x j => x * letterM gs j) x ∈ H from this 1 H.one_mem
  induction w with
  | nil => exact fun x hx => hx
  | cons j w ih =>
    intro x hx
    rw [List.foldl_cons]
    exact ih _ (H.mul_mem hx (hl j))

end CFSG.EvenSporadicStandard.Co1Cent
