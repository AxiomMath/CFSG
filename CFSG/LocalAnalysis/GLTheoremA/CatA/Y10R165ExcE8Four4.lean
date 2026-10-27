module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four3
public import CFSG.LieType.AlgebraicGroups.KernelRootGroup

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.RouteD.Exotic

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four


theorem canonicalRep_d4d4W_mem_torus_sup_rootSpan {L : Type} [Field L] :
    canonicalRep (coxeterSystem .E8) L d4d4W ∈
      torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char) :=
  CFSG.LieType.AlgebraicGroups.canonicalRep_mem_torus_sup_rootSpan_kernelRoots
    (τ := .E8) (χ := d4d4Char) (L := L) d4d4W_mem_closure

theorem exists_fourLang (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [CharP L ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) :
    ∃ g : ModGL .E8 L,
      g ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char) ∧
        entrywiseFrobGL .E8 L ℓ f g =
          g * canonicalRep (coxeterSystem .E8) L d4d4W := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨z, hz, hz'⟩ := CFSG.LieType.AlgebraicGroups.lang_torus_sup_rootSpan
    (τ := .E8) (L := L) (ℓ := ℓ) (χ := d4d4Char) (e := f) hf
    (canonicalRep (coxeterSystem .E8) L d4d4W) (canonicalRep_d4d4W_mem_torus_sup_rootSpan (L := L))
  refine ⟨z, hz, ?_⟩
  have h : z⁻¹ * entrywiseFrobGL .E8 L ℓ f z =
      canonicalRep (coxeterSystem .E8) L d4d4W := hz'
  calc entrywiseFrobGL .E8 L ℓ f z
      = z * (z⁻¹ * entrywiseFrobGL .E8 L ℓ f z) := by group
    _ = z * canonicalRep (coxeterSystem .E8) L d4d4W := by rw [h]

theorem exists_sq_eq_unit_of_isAlgClosed {L : Type} [Field L] [IsAlgClosed L] (t : Lˣ) :
    ∃ s : Lˣ, s * s = t := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_eq_mul_self (t : L)
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : (t : L) = 0 := by rw [hb]; ring
    exact Units.ne_zero t h0
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply Units.ext
  simpa [Units.val_mk0] using hb.symm

theorem torusGroup_le_d8Chain_of_isAlgClosed (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    torusGroup .E8 L ≤ (⨆ k, e8D8Chain L k).map (adjointGroup .E8 L).subtype := by
  change Subgroup.closure (Set.range fun p : Fin Tag.E8.rank × Lˣ =>
    torusElt .E8 L p.1 p.2) ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  obtain ⟨s, hs⟩ := exists_sq_eq_unit_of_isAlgClosed t
  rw [← hs]
  change torusElt .E8 L i (s * s) ∈ _
  rw [torusElt_eq_prod_rootTorus i s]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact rootTorusSL2_mem_d8Target j _

theorem rootSpan_kernelRoots_d4d4Char_le_d8Chain (K : Type) [Field K] :
    rootSpan .E8 K (kernelRoots d4d4Char) ≤ d8Target K :=
  (rootSpan_mono (kernelRoots_d4d4Char_subset_d8Char)).trans
    (rootSpan_kernelRoots_d8Char_le_d8Chain (K := K))

theorem torus_sup_rootSpan_d4d4Char_le_d8Chain (L : Type) [Field L] [IsAlgClosed L]
    [CharP L 2] :
    torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char) ≤
      (⨆ k, e8D8Chain L k).map (adjointGroup .E8 L).subtype :=
  sup_le (torusGroup_le_d8Chain_of_isAlgClosed L)
    (rootSpan_kernelRoots_d4d4Char_le_d8Chain L)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
