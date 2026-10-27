module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryMaxBorel

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable (n : ℕ) (K : Type) [Field K]

theorem native_partialBorel_eq_fullBorel [Finite K] (hn : 3 ≤ n) :
    flagStab n K = borel n K := by
  have hle : flagStab n K ≤ posBorel n K :=
    flagStab_le_posBorel (by omega) (fun _ ha => map_flag_top_ne_Xstar hn ha)
  apply le_antisymm
  · intro g hg
    exact mem_borel.mpr ⟨(mem_flagStab.mp hg).1,
      fun i _ _ => (mem_posBorel.mp (hle hg)).2 i⟩
  · intro g hg
    obtain ⟨hgE, hgF⟩ := mem_borel.mp hg
    exact mem_flagStab.mpr ⟨hgE, fun i hi hin => hgF i hi (by omega)⟩

theorem plusDerivedBorel_fixes_top [Finite K] (hn : 3 ≤ n)
    (g : StatedOmega (StatedQuadPlus n K)) (hg : g ∈ plusDerivedBorel n K) :
    (flag n K n).map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin n ⊕ Fin n) K g.val).toLinearMap = flag n K n := by
  have hm : plusDerivedEquiv n K hn g ∈
      (borel n K).subgroupOf (orthElementaryGroup (quadPlus n K)) := by
    rw [← native_partialBorel_eq_fullBorel n K hn, ← plusDerivedBorel_map n K hn]
    exact ⟨g, hg, rfl⟩
  have hf := (mem_borel.mp (Subgroup.mem_subgroupOf.mp hm)).2 n (by omega) le_rfl
  rw [plusDerivedEquiv_val] at hf
  exact hf

theorem plusProjectiveMaximal_comap
    (M : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) (hM : IsCoatom M) :
    IsCoatom (M.comap (QuotientGroup.mk' _)) :=
  Subgroup.isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective _) hM

private theorem ambient_isMax {G : Type*} [Group G] (E : Subgroup G)
    (D : Subgroup E) (hD : IsCoatom D) :
    D.map E.subtype ≠ E ∧
      ∀ M' : Subgroup G, D.map E.subtype ≤ M' → M' ≤ E →
        M' = D.map E.subtype ∨ M' = E := by
  have htop : (⊤ : Subgroup E).map E.subtype = E := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  refine ⟨?_, ?_⟩
  · intro heq
    apply hD.ne_top
    apply Subgroup.map_injective E.subtype_injective
    exact heq.trans htop.symm
  · intro M' hDM hME
    have hsub : D ≤ M'.subgroupOf E := by
      intro x hx
      exact hDM ⟨x, hx, rfl⟩
    rcases hD.le_iff.mp hsub with ht | hd
    · right
      rw [← Subgroup.map_subgroupOf_eq_of_le hME, ht, htop]
    · left
      rw [← Subgroup.map_subgroupOf_eq_of_le hME, hd]

theorem plusProjectiveMaximalBorel_overgroups [Finite K] (hn : 3 ≤ n)
    (M : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (hM : IsCoatom M) (hBM : plusProjectiveBorel n K ≤ M) :
    (∃ i : ℕ, 1 ≤ i ∧ i ≤ n - 2 ∧
      M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K i)) ∨
    M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K (by omega)) ∨
    M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n) := by
  let e := plusDerivedEquiv n K hn
  let E := orthElementaryGroup (quadPlus n K)
  let D : Subgroup (StatedOmega (StatedQuadPlus n K)) := M.comap (QuotientGroup.mk' _)
  let DE : Subgroup E := D.map e.toMonoidHom
  let MA : Subgroup ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) := DE.map E.subtype
  have hD : IsCoatom D := plusProjectiveMaximal_comap n K M hM
  have hDE : IsCoatom DE := (OrderIso.isCoatom_iff e.mapSubgroup D).mpr hD
  have hBD : plusDerivedBorel n K ≤ D := by
    intro x hx
    apply hBM
    rw [← plusDerivedBorel_project n K]
    exact ⟨x, hx, rfl⟩
  have hBDE : (borel n K).subgroupOf E ≤ DE := by
    rw [← native_partialBorel_eq_fullBorel n K hn, ← plusDerivedBorel_map n K hn]
    exact Subgroup.map_mono hBD
  have hBMA : borel n K ≤ MA := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (borel_le (r := n) (K := K))]
    exact Subgroup.map_mono hBDE
  have hMAE : MA ≤ E := Subgroup.map_subtype_le DE
  obtain ⟨hne, hmax⟩ := ambient_isMax E DE hDE
  have hlist := (orthogonal_geometry_split_maximal_Borel_overgroups (K := K) hn).2
    MA hMAE hBMA hne hmax
  have hproj : ∀ W : Submodule K (Fin n ⊕ Fin n → K),
      MA = E ⊓ MulAction.stabilizer
        ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) W →
      M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W := by
    intro W hW
    have hDEW : DE = MulAction.stabilizer E W := by
      apply Subgroup.map_injective E.subtype_injective
      change MA = (MulAction.stabilizer E W).map E.subtype
      have heq : MulAction.stabilizer E W =
          (MulAction.stabilizer ((Fin n ⊕ Fin n → K) ≃ₗ[K]
            (Fin n ⊕ Fin n → K)) W).subgroupOf E := rfl
      rw [heq, Subgroup.subgroupOf_map_subtype, inf_comm]
      exact hW
    have hDW : D = statedDerivedSubspaceStabilizer (StatedQuadPlus n K) W := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      change DE = (statedDerivedSubspaceStabilizer (StatedQuadPlus n K) W).map e.toMonoidHom
      exact hDEW.trans (statedDerivedSubspaceStabilizer_map_elementary (coe_quadPlus n K)
        (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn) W).symm
    have hm : D.map (QuotientGroup.mk' _) = M :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) M
    rw [← hm, hDW, statedDerivedSubspaceStabilizer_map]
  rcases hlist with ⟨i, hi1, hi2, hi⟩ | hs | hx
  · exact Or.inl ⟨i, hi1, hi2, hproj _ hi⟩
  · exact Or.inr (Or.inl (hproj _ hs))
  · exact Or.inr (Or.inr (hproj _ hx))

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
