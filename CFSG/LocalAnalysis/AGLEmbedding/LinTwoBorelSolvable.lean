module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

section Borel

variable {F : Type} [Field F]

private theorem borelSL_mul_eq_one (A : borelSL F) :
    ((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 *
      ((A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have h := det_entries (A : SL(2, F))
  rwa [(mem_borelSL_iff _).mp A.2, mul_zero, sub_zero] at h

private def borelSLDiag : borelSL F →* Fˣ where
  toFun A := Units.mkOfMulEqOne _ _ (borelSL_mul_eq_one A)
  map_one' := by
    ext
    simp
  map_mul' A B := by
    ext
    simp [mul_apply_SL, (mem_borelSL_iff _).mp B.2]

private theorem borelSLDiag_ker_comm (A B : (borelSLDiag (F := F)).ker) : A * B = B * A := by
  have hd (C : (borelSLDiag (F := F)).ker) :
      (((C : borelSL F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.mp C.2)
    simpa [borelSLDiag] using h
  have hd' (C : (borelSLDiag (F := F)).ker) :
      (((C : borelSL F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h := borelSL_mul_eq_one (C : borelSL F)
    rwa [hd C, one_mul] at h
  have hl (C : (borelSLDiag (F := F)).ker) :
      (((C : borelSL F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    (mem_borelSL_iff _).mp (C : borelSL F).2
  apply Subtype.ext
  apply Subtype.ext
  apply SL_ext <;>
    simp [mul_apply_SL, hd A, hd B, hd' A, hd' B, hl A, hl B, add_comm]

theorem isSolvable_borelSL : Group.IsSolvable (borelSL F) := by
  have : Group.IsSolvable (borelSLDiag (F := F)).ker :=
    Group.isSolvable_of_comm borelSLDiag_ker_comm
  exact Group.isSolvable_of_ker_le_range (borelSLDiag (F := F)).ker.subtype borelSLDiag
    (by rw [Subgroup.range_subtype])

theorem isSolvable_borel_psl2 : Group.IsSolvable (borel F) := by
  have := isSolvable_borelSL (F := F)
  exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective mk (borelSL F))

end Borel

theorem isSolvable_normalizer_sylow_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (T : Sylow p (PSL2GF p n)) :
    Group.IsSolvable
      (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))) := by
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  obtain ⟨U, hU⟩ := exists_sylow_eq_unipotent_psl2GF hp2 hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (PSL2GF p n) U T
  have hgU : ((g • U : Sylow p (PSL2GF p n)) : Subgroup (PSL2GF p n)) =
      (unipotent (GaloisField p n)).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map, hU]
    rfl
  rw [hgU, normalizer_map_conj, normalizer_unipotent_eq_borel hF]
  have := isSolvable_borel_psl2 (F := GaloisField p n)
  exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)

theorem kFactL2SylowNormalizerSolvable :
    ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ n → ∀ (U : Sylow p (PSL2GF p n))
      (A : Subgroup (MulAut (PSL2GF p n))),
      (∀ α ∈ A, (U : Subgroup (PSL2GF p n)).map (α : PSL2GF p n ≃* PSL2GF p n).toMonoidHom = U) →
      Group.IsSolvable A := by
  intro p n _ hp2 hn U A hA
  set B := A.comap (MulAut.conj : PSL2GF p n →* MulAut (PSL2GF p n))
  have hBN : B ≤ Subgroup.normalizer ((U : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)) := by
    intro x hx
    have hmap := hA _ hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hmap]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hmap] at hh
      obtain ⟨h', hh', he⟩ := hh
      have he' : h' = h := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj,
          mul_right_inj] using he
      rwa [← he']
  have := isSolvable_normalizer_sylow_psl2GF hp2 hn U
  have : Group.IsSolvable B :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBN)
  have : Group.IsSolvable (Outer (PSL2GF p n)) := outer_solvable (GaloisField p n)
  refine Group.isSolvable_of_ker_le_range
    ((MulAut.conj.comp B.subtype).codRestrict A fun x => x.2)
    ((QuotientGroup.mk' (inner (PSL2GF p n))).comp A.subtype) fun a ha => ?_
  obtain ⟨x, hx⟩ : (a : MulAut (PSL2GF p n)) ∈ inner (PSL2GF p n) :=
    (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp ha)
  exact ⟨⟨x, show MulAut.conj x ∈ A from hx ▸ a.2⟩, Subtype.ext hx⟩

end CFSG.AGLEmbedding
