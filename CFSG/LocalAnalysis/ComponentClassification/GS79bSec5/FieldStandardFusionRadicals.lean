module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals

public section

open Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.ABGLocalTools (IsSylowOf)

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_radicals_of_sl_three_cover
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G)
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (V : Subgroup G)
    (hV : CFSG.ABGLocalTools.IsSylowOf 2 V A) :
    ∃ V₁ V₂ : Subgroup G,
      CFSG.LocalAnalysis.EvenBN.LinearThree.Radicals V V₁ V₂ (Nat.card F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hQU : (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) = unipAll F := by
    rw [hQ, unipAll_eq_unitriangular]
  let ψ : unipAll F →* G := A.subtype.comp (φ.comp (unipAll F).subtype)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hAK : φ (x : Matrix.SpecialLinearGroup (Fin 3) F) =
        φ (y : Matrix.SpecialLinearGroup (Fin 3) F) :=
      Subtype.ext (by simpa [ψ] using hxy)
    have hproj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F
        (x : Matrix.SpecialLinearGroup (Fin 3) F) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F
        (y : Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [← DFunLike.congr_fun hφproj (x : Matrix.SpecialLinearGroup (Fin 3) F),
        ← DFunLike.congr_fun hφproj (y : Matrix.SpecialLinearGroup (Fin 3) F)]
      simp only [MonoidHom.comp_apply]
      rw [hAK]
    exact unipEmb_injective (K := F) (by simpa [unipEmb] using hproj)
  let QA : Sylow 2 A := Q.mapSurjective hφsurj
  have hUt : (⊤ : Subgroup (unipAll F)).map (unipAll F).subtype = unipAll F := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hQAmap : ((unipAll F).map φ).map A.subtype =
      (⊤ : Subgroup (unipAll F)).map ψ := by
    conv_lhs => rw [← hUt]
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hQAcoe : (QA : Subgroup A) =
      (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).map φ := by
    show ((Q.mapSurjective hφsurj : Sylow 2 A) : Subgroup A) = _
    exact Sylow.coe_mapSurjective hφsurj Q
  have hQAcoeG : (QA : Subgroup A).map A.subtype =
      ((unipAll F).map φ).map A.subtype := by
    rw [hQAcoe, hQU]
  have hψtop : (⊤ : Subgroup (unipAll F)).map ψ = (QA : Subgroup A).map A.subtype := by
    rw [← hQAmap]
    exact hQAcoeG.symm
  obtain ⟨QV, hQV⟩ := hV
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A QA QV
  have hQAsmul : (QA : Subgroup A).map (MulAut.conj a).toMonoidHom = QV := by
    have h := congrArg (fun P : Sylow 2 A => (P : Subgroup A)) ha
    rw [Sylow.coe_subgroup_smul] at h
    exact h
  have hconjcomp : (MulAut.conj (a : G)).toMonoidHom.comp A.subtype =
      A.subtype.comp (MulAut.conj a).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  have hθtop : (⊤ : Subgroup (unipAll F)).map
      ((MulAut.conj (a : G)).toMonoidHom.comp ψ) = V := by
    rw [← Subgroup.map_map, hψtop, Subgroup.map_map, hconjcomp, ← Subgroup.map_map,
      hQAsmul, hQV]
  have hR := Radicals.map (φ := (MulAut.conj (a : G)).toMonoidHom.comp ψ)
    ((MulAut.conj (a : G)).injective.comp hψinj) (radicals_unipAll (K := F))
  rw [hθtop] at hR
  exact ⟨_, _, hR⟩

end CFSG.ComponentClassification.GS79bSec5
