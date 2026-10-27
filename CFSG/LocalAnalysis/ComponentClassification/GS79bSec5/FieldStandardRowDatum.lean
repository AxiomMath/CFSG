module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardFusion

public section

open Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77 (radOne radTwo unipOne_le_unipAll unipTwo_le_unipAll)

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_datum_with_standard_unipotent_radicals
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F)
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
    ∃ d : CFSG.OddStandard.Seitz77.Datum A,
      d.t = t ∧
      CFSG.OddStandard.sg A d.R = Subgroup.zpowers t ∧
      d.V =
        (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipAll F).map
          (A.subtype.comp φ) ∧
      CFSG.LocalAnalysis.EvenBN.LinearThree.Radicals d.V
        ((CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map
          (A.subtype.comp φ))
        ((CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipTwo F).map
          (A.subtype.comp φ))
        (Nat.card F) := by
  classical
  obtain ⟨htSyl, -⟩ :=
    exists_seitz_fusion_configuration_of_standard hnonab hF A hA hZ e φ hφsurj hφproj hcyc
      t ht htC
  obtain ⟨R, hR⟩ := htSyl
  have hsgR : CFSG.OddStandard.sg A R = Subgroup.zpowers t := hR
  have hsec : CFSG.OddStandard.Sector A R t :=
    ⟨hA, hcyc R, by
      show t ∈ CFSG.OddStandard.sg A R
      rw [hsgR]
      exact Subgroup.mem_zpowers t, ht⟩
  let Vstd : Subgroup G := (unipAll F).map (A.subtype.comp φ)
  let E : Subgroup G := (unipOne F).map (A.subtype.comp φ)
  let E2 : Subgroup G := (unipTwo F).map (A.subtype.comp φ)
  have hVstd : IsSylowOf 2 Vstd A := by
    obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
    have hQU : (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) = unipAll F := by
      rw [hQ, unipAll_eq_unitriangular]
    refine ⟨Q.mapSurjective hφsurj, ?_⟩
    rw [Sylow.coe_mapSurjective hφsurj Q, hQU, Subgroup.map_map]
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
  have hUt : (⊤ : Subgroup (unipAll F)).map (unipAll F).subtype = unipAll F := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htop : (⊤ : Subgroup (unipAll F)).map ψ = Vstd := by
    change (⊤ : Subgroup (unipAll F)).map
      ((A.subtype.comp φ).comp (unipAll F).subtype) = Vstd
    rw [← Subgroup.map_map, hUt]
  have hOne : (radOne F).map ψ = E := by
    change (radOne F).map ((A.subtype.comp φ).comp (unipAll F).subtype) = E
    rw [← Subgroup.map_map, radOne, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 unipOne_le_unipAll]
  have hTwo : (radTwo F).map ψ = E2 := by
    change (radTwo F).map ((A.subtype.comp φ).comp (unipAll F).subtype) = E2
    rw [← Subgroup.map_map, radTwo, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 unipTwo_le_unipAll]
  have hrad0 : CFSG.LocalAnalysis.EvenBN.LinearThree.Radicals
      ((⊤ : Subgroup (unipAll F)).map ψ) ((radOne F).map ψ) ((radTwo F).map ψ)
      (Nat.card F) :=
    Radicals.map (φ := ψ) hψinj (radicals_unipAll (K := F))
  have hrad : CFSG.LocalAnalysis.EvenBN.LinearThree.Radicals Vstd E E2 (Nat.card F) := by
    simpa only [htop, hOne, hTwo] using hrad0
  have hVstdA : Vstd ≤ A := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (φ u).2
  have hVstdN : Vstd ≤ Subgroup.normalizer (A : Set G) :=
    hVstdA.trans (Subgroup.le_normalizer (H := A))
  have hztC : Subgroup.zpowers t ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.zpowers_le.mpr htC
  have hztN : Subgroup.zpowers t ≤ Subgroup.normalizer (A : Set G) :=
    hztC.trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have hzt_normalizer : Subgroup.zpowers t ≤ Subgroup.normalizer Vstd :=
    hztC.trans ((Subgroup.centralizer_le hVstdA).trans
      (Subgroup.centralizer_le_normalizer (Vstd : Set G)))
  have hztP : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  let T : Subgroup G := Vstd ⊔ Subgroup.zpowers t
  have hT : IsPGroup 2 T :=
    IsPGroup.to_sup_of_normal_left' hVstd.isPGroup hztP hzt_normalizer
  have hTN : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (A : Set G))) := hT.comap_subtype
  obtain ⟨Q, hQle⟩ := hTN.exists_le_sylow
  let P : Subgroup G := (Q : Subgroup (Subgroup.normalizer (A : Set G))).map
    (Subgroup.normalizer (A : Set G)).subtype
  have hP : IsSylowOf 2 P (Subgroup.normalizer (A : Set G)) := ⟨Q, rfl⟩
  have hVstdP : Vstd ≤ P := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hVstdN hx⟩,
        hQle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hx)), rfl⟩
  have hRP : CFSG.OddStandard.sg A R ≤ P := by
    rw [hsgR]
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hztN hx⟩,
        hQle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hx)), rfl⟩
  let d : CFSG.OddStandard.Seitz77.Datum A :=
    { R := R, t := t, sector := hsec, P := P, hP := hP, hRP := hRP }
  have hVle : Vstd ≤ d.V := le_inf hVstdP hVstdA
  have hVd : d.V = Vstd :=
    hVstd.eq_of_le hVle (inf_le_right : d.P ⊓ A ≤ A) d.V_isSylow.isPGroup
  refine ⟨d, rfl, hsgR, hVd, ?_⟩
  rw [← hVd] at hrad
  exact hrad

end CFSG.ComponentClassification.GS79bSec5

end
