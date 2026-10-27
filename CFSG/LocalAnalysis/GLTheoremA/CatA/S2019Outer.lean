module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.SignalizerFunctorTheorem.CatalogBridge
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

theorem commutatorElement_mul_mul_of_central {M : Type*} [Group M] {g g' z z' : M}
    (hz : ∀ w, w * z = z * w) (hz' : ∀ w, w * z' = z' * w) : ⁅g * z, g' * z'⁆ = ⁅g, g'⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc g * z * (g' * z') * (g * z)⁻¹ * (g' * z')⁻¹
      = g * (z * g') * z' * z⁻¹ * g⁻¹ * z'⁻¹ * g'⁻¹ := by group
    _ = g * (g' * z) * z' * z⁻¹ * g⁻¹ * z'⁻¹ * g'⁻¹ := by rw [← hz g']
    _ = g * g' * (z * z' * z⁻¹) * g⁻¹ * z'⁻¹ * g'⁻¹ := by group
    _ = g * g' * z' * g⁻¹ * z'⁻¹ * g'⁻¹ := by rw [← hz z', mul_inv_cancel_right]
    _ = g * g' * (z' * g⁻¹) * z'⁻¹ * g'⁻¹ := by group
    _ = g * g' * (g⁻¹ * z') * z'⁻¹ * g'⁻¹ := by rw [← hz' g⁻¹]
    _ = g * g' * g⁻¹ * g'⁻¹ := by group

variable {G : Type} [Group G]

theorem fixSubgroup_conj (α γ : MulAut G) :
    fixSubgroup (γ * α * γ⁻¹) = (fixSubgroup α).map γ.toMonoidHom := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_map_equiv, mem_fixSubgroup]
  change γ (α (γ.symm x)) = x ↔ α (γ.symm x) = γ.symm x
  constructor
  · intro h
    calc α (γ.symm x) = γ.symm (γ (α (γ.symm x))) := (γ.symm_apply_apply _).symm
      _ = γ.symm x := by rw [h]
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

theorem nonLocalized_map_mulAut {J : Subgroup G} (γ : MulAut G) (hJ : NonLocalized J) :
    NonLocalized (J.map γ.toMonoidHom) := by
  intro T hT hs hle
  refine hJ (T.map γ.symm.toMonoidHom) (fun h => hT ?_) ?_ fun j hj => ?_
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ γ.symm.injective] at h
  · haveI := hs
    exact solvable_of_surjective (MonoidHom.subgroupMap_surjective γ.symm.toMonoidHom T)
  · have hγj : γ j ∈ Subgroup.normalizer (T : Set G) := hle ⟨j, hj, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hγj ⊢
    intro t
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm, map_mul, map_mul,
      map_inv]
    exact hγj (γ t)

theorem s2019FixCentralizes_of_nonLocalized [Finite G] (p : ℕ) (α : MulAut G) {J : Subgroup G}
    (hJC : J ≤ fixSubgroup α) (hcomm : ⁅fixSubgroup α, fixSubgroup α⁆ ≤ J)
    (hJs : IsSimpleGroup ↥J) (hJn : NonLocalized J) : S2019FixCentralizes p α := by
  intro L hL T hT2 hLT
  have hperf : ⁅L, L⁆ = L := glaPComponent_perfect hL
  have hLJ : L ≤ J := by
    rw [← hperf]
    exact (Subgroup.commutator_mono hL.1 hL.1).trans hcomm
  have hsn : IsSubnormal L J := by
    have h1 := hL.2.1.inf_of_le hJC
    rwa [inf_eq_left.2 hLJ] at h1
  rcases hsn.eq_bot_or_eq_of_isSimpleGroup hJs with h | h
  · rw [h, Subgroup.commutator_bot_right]
  · subst h
    by_cases hT : T = ⊥
    · rw [hT, Subgroup.commutator_bot_left]
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Group.IsNilpotent ↥T := hT2.isNilpotent
      exact absurd hLT (hJn T hT inferInstance)

theorem s2019FixCentralizes_conj_of_nonLocalized [Finite G] (p : ℕ) (α γ : MulAut G)
    {J : Subgroup G}
    (hJC : J ≤ fixSubgroup α) (hcomm : ⁅fixSubgroup α, fixSubgroup α⁆ ≤ J)
    (hJs : IsSimpleGroup ↥J) (hJn : NonLocalized J) : S2019FixCentralizes p (γ * α * γ⁻¹) := by
  have hfix := fixSubgroup_conj α γ
  haveI := hJs
  refine s2019FixCentralizes_of_nonLocalized p _ (J := J.map γ.toMonoidHom) ?_ ?_
    (J.equivMapOfInjective γ.toMonoidHom γ.injective).symm.isSimpleGroup
    (nonLocalized_map_mulAut γ hJn)
  · rw [hfix]
    exact Subgroup.map_mono hJC
  · rw [hfix, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcomm

end CFSG.LocalAnalysis.GLTheoremA.S2019
