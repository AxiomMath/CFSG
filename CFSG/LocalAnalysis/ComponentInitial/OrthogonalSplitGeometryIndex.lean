module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitMaximalFamilyOrbits
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryCount

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
open scoped Pointwise

section Proj

variable (r : ℕ) (K : Type*) [Field K]

@[expose] noncomputable def splitScalars : Subgroup (orthElementaryGroup (quadPlus r K)) :=
  (scalars K (Fin r ⊕ Fin r → K)).subgroupOf (orthElementaryGroup (quadPlus r K))

instance splitScalars_normal : (splitScalars r K).Normal :=
  Subgroup.Normal.subgroupOf inferInstance _

abbrev splitProj : Type _ :=
  orthElementaryGroup (quadPlus r K) ⧸ splitScalars r K

variable {r K}

theorem smul_eq_self_of_mem_scalars {V : Type*} [AddCommGroup V] [Module K V]
    {g : V ≃ₗ[K] V} (hg : g ∈ scalars K V) (L : Submodule K V) : g • L = L := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hg
  obtain ⟨d, hd⟩ := mem_scalars.mp (inv_mem hg)
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    change g v ∈ L
    rw [hc]
    exact L.smul_mem c hv
  · refine ⟨g⁻¹ v, ?_, LinearEquiv.apply_inv_apply' g v⟩
    rw [SetLike.mem_coe, hd]
    exact L.smul_mem d hv

variable (r K)

@[expose] noncomputable def splitProjAction :
    splitProj r K →* Equiv.Perm (Submodule K (Fin r ⊕ Fin r → K)) :=
  QuotientGroup.lift (splitScalars r K) (MulAction.toPermHom _ _) fun _ hg =>
    Equiv.ext fun L => smul_eq_self_of_mem_scalars (Subgroup.mem_subgroupOf.mp hg) L

noncomputable instance : MulAction (splitProj r K) (Submodule K (Fin r ⊕ Fin r → K)) :=
  MulAction.compHom _ (splitProjAction r K)

variable {r K}

theorem mk_smul_submodule (g : orthElementaryGroup (quadPlus r K))
    (L : Submodule K (Fin r ⊕ Fin r → K)) : (g : splitProj r K) • L = g • L :=
  rfl

theorem orbit_splitProj (L : Submodule K (Fin r ⊕ Fin r → K)) :
    MulAction.orbit (splitProj r K) L = MulAction.orbit (orthElementaryGroup (quadPlus r K)) L := by
  ext M
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    exact ⟨g, (mk_smul_submodule g L).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, mk_smul_submodule g L⟩

end Proj

theorem orthogonal_geometry_split_geometric_stabilizer_indices {K : Type*} [Field K] [Finite K]
    {r : ℕ} (hr : 3 ≤ r) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) :
    (finrank K W < r → ((MulAction.stabilizer (splitProj r K) W).index : ℚ) =
      splitCount (Nat.card K) r (finrank K W)) ∧
    (finrank K W = r → ((MulAction.stabilizer (splitProj r K) W).index : ℚ) =
      splitMaxIndex (Nat.card K) r) := by
  have hWs : W ∈ singularSubspaces (quadPlus r K) (finrank K W) := ⟨rfl, hW⟩
  have hidx : (MulAction.stabilizer (splitProj r K) W).index =
      Nat.card (MulAction.orbit (orthElementaryGroup (quadPlus r K)) W) := by
    rw [MulAction.index_stabilizer, orbit_splitProj, Nat.card_coe_set_eq]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  ·
    have horb : MulAction.orbit (orthElementaryGroup (quadPlus r K)) W =
        singularSubspaces (quadPlus r K) (finrank K W) := by
      ext L
      constructor
      · intro hL
        obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hL
        exact map_mem_singularSubspaces (orthElementaryGroup_le _ ha) hWs
      · intro hL
        have htrans := orthogonal_geometry_split_partial_flag_transitivity (K := K) (r := r)
          (k := finrank K W) (by omega) (by omega)
        obtain ⟨g, hg, hgW⟩ := htrans.2 W hWs L hL
        exact mem_orbit_elementary.2 ⟨g, hg, hgW⟩
    rw [hidx, horb, card_singularSubspaces hk.le]
    rfl
  ·
    obtain ⟨-, -, -, -, hcover, -, hX, hXs, -⟩ :=
      orthogonal_geometry_split_maximal_family_orbits (K := K) hr
    have hWr : W ∈ singularSubspaces (quadPlus r K) r := ⟨hk, hW⟩
    have hcard : Nat.card (MulAction.orbit (orthElementaryGroup (quadPlus r K)) W) =
        ∏ i ∈ Finset.Icc 1 (r - 1), (Nat.card K ^ i + 1) := by
      rcases hcover W hWr with h | h
      · rw [MulAction.orbit_eq_iff.mpr h, hX]
      · rw [MulAction.orbit_eq_iff.mpr h, hXs]
    rw [hidx, hcard, splitMaxIndex]
    push_cast
    rfl

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
