module

public import CFSG.GH74.Uniqueness.Section12Basic
public import CFSG.GH74.Uniqueness.Theorem4

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem zHull_zHull (F : Subgroup X) : zHull Z (zHull Z F) = zHull Z F := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr Set.inter_subset_right
  · exact Subgroup.closure_mono (fun x hx => ⟨hx.1, Subgroup.subset_closure hx⟩)

omit [Finite X] in
theorem subgroupOf_inf_eq_comap (M F : Subgroup X) :
    (M ⊓ F).subgroupOf F = M.comap F.subtype := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem ZDSetup.not_solvable_zHull_of_ne
    (S : ZDSetup X Z M) {F : Subgroup X}
    (hF : F ≠ ⊤) (hFM : ¬ F ≤ M) {a b : X} (ha : a ∈ Z ∩ ((F ⊓ M : Subgroup X) : Set X))
    (hb : b ∈ Z ∩ ((F ⊓ M : Subgroup X) : Set X)) (hab : a ≠ b) :
    ¬ Group.IsSolvable ↥(zHull Z F) := by
  intro hsol
  obtain ⟨-, h | h⟩ := S.corollary713 F hF hFM ⟨a, ha⟩
  · obtain ⟨-, u, -, hu, -⟩ := h
    have h1 : a = u := by
      have : a ∈ ({u} : Set X) := hu ▸ ha
      exact this
    have h2 : b = u := by
      have : b ∈ ({u} : Set X) := hu ▸ hb
      exact this
    exact hab (h1.trans h2.symm)
  · obtain ⟨-, hB, -, -⟩ := h
    have hsolv : Group.IsSolvable (↥(zHull Z F) ⧸ center ↥(zHull Z F)) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (center ↥(zHull Z F)))
    have hsimple := isSimpleGroup_of_isBenderGroup hB
    obtain ⟨x, y, hxy⟩ := exists_not_commute_of_isBenderGroup hB
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) x y)

theorem ZDSetup.benderSub_exists
    (S : ZDSetup X Z M) {F : Subgroup X} (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hns : ¬ Group.IsSolvable ↥(zHull Z F)) :
    ∃ n i e : ℕ, BenderSub Z M (zHull Z F) n i e := by
  obtain ⟨hLM, h | h⟩ := S.corollary713 F hF hFM hne
  · exact absurd h.1 hns
  obtain ⟨hcore, hB, -, -⟩ := h
  obtain ⟨n, i, e, hT⟩ := Bender.isBenderGroup_iff_exists_benderType.mp hB
  obtain ⟨⟨T, hT'⟩, hinv, -⟩ := S.corollary713Extra F hF hFM hne hns
  have hLF : zHull Z F ≤ F := Cor713.zHull_le F
  refine ⟨n, i, e, ?_⟩
  obtain ⟨z, hz, hzFM⟩ := hne
  have hzF : z ∈ F := (Subgroup.mem_inf.mp hzFM).1
  have hzM : z ∈ M := (Subgroup.mem_inf.mp hzFM).2
  exact
    { ne_top := fun h => hF (top_le_iff.mp (h ▸ hLF))
      not_le := hLM
      nonempty := ⟨z, hz, Subgroup.mem_inf.mpr ⟨Cor713.mem_zHull_of_mem hz hzF, hzM⟩⟩
      zhull := zHull_zHull F
      core := hcore
      bender := hT
      borel := ⟨T, by rw [subgroupOf_inf_eq_comap]; exact hT'⟩
      invol := hinv
      strong := S.cor713_isStronglyEmbedded_zHull hF hFM ⟨z, hz, hzFM⟩ }

end CFSG.GH74.Uniqueness
