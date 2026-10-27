module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TransvectionIrreducible
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeSetting
import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV)
open CFSG.QuasithinUnique
open CFSG.Open (pCoreOf)
open CFSG.Quasithin (autOn)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (sup_le_normalizer_blockV le_normalizer_of_isWeakSBlock isQuasisimple_autOn
    quasithinGenFitting_autOn_sup autOnHom autOnHom_surjective autOnHom_eq_one_iff)
open Subgroup
open scoped commutatorElement

namespace TransvIrr

theorem normal_gen {G : Type} [Group G] [Finite G] {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    {T : Subgroup G} {x : G} (hTM : T ≤ L ⊔ S) (hMT : L ⊔ S ≤ normalizer (T : Set G))
    (hCT : (L ⊔ S) ⊓ centralizer (blockV S L : Set G) ≤ T) (hxT : x ∈ T)
    (hxn : x ∉ L ⊔ (L ⊔ S) ⊓ centralizer (blockV S L : Set G)) : L ≤ T := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hMV := sup_le_normalizer_blockV S L
  have hxM : x ∈ L ⊔ S := hTM hxT
  have hq := isQuasisimple_autOn hA hL hSL
  have hFit := quasithinGenFitting_autOn_sup hA hL hSL
  set V := blockV S L with hV
  set M := L ⊔ S with hM
  let ρ := Setup.rho V M hMV
  have hρ1 : ∀ a b : M, ρ a = ρ b → (a : G)⁻¹ * b ∈ M ⊓ centralizer (V : Set G) := by
    intro a b hab
    have : ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact ⟨(a⁻¹ * b).2, (Setup.rho_eq_one_iff hMV _).mp this⟩
  have hcent : autOn M V ⊓ centralizer (autOn L V : Set (MulAut V)) ≤ autOn L V := by
    have := CFSG.Quasithin.centralizer_quasithinGenFitting_le (autOn M V)
    rwa [hFit] at this
  have htN : ρ ⟨x, hxM⟩ ∈ autOn T V :=
    (Setup.mem_autOn_iff_rho hMV hTM).mpr ⟨⟨x, hxM⟩, hxT, rfl⟩
  have htK : ρ ⟨x, hxM⟩ ∉ autOn L V := by
    intro hk
    obtain ⟨p, hpL, hρ⟩ := (Setup.mem_autOn_iff_rho hMV le_sup_left).mp hk
    have h2 := hρ1 p _ hρ
    apply hxn
    have e : x = (p : G) * ((p : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hpL h2
  have hle := le_of_mem_normal (H := autOn M V) (K := autOn L V) (N := autOn T V)
    (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le le_sup_left)
    (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le hTM)
    (CFSG.Quasithin.InternalSec.autOn_normal_of (sup_le Subgroup.le_normalizer hSL))
    (CFSG.Quasithin.InternalSec.autOn_normal_of hMT) hq hcent htN htK
  intro l hl
  have hmem := hle ((Setup.mem_autOn_iff_rho hMV le_sup_left).mpr
    ⟨⟨l, Subgroup.mem_sup_left hl⟩, hl, rfl⟩)
  obtain ⟨p, hpT, hρ⟩ := (Setup.mem_autOn_iff_rho hMV hTM).mp hmem
  have h2 := hρ1 p _ hρ
  have e : l = (p : G) * ((p : G)⁻¹ * l) := by group
  rw [e]
  exact T.mul_mem hpT (hCT h2)

end TransvIrr

theorem shapeOut_of_transvectionData {G : Type} [Group G] [Finite G]
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (ht : TransvectionData S L) :
    ∃ (Y : Type) (_ : Group Y), ShapeOut Y ∧
      Nonempty ((↥(autOn L (blockV S L)) ⧸ Subgroup.center ↥(autOn L (blockV S L))) ≃*
        (Y ⧸ Subgroup.center Y)) := by
  obtain ⟨s, hsS, hgen, hsn, hZ⟩ := ht
  have hset := TransvIrr.setting_of hX hA hL hsS hgen hsn hZ
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hV2 : ∀ v ∈ blockV S L, v * v = 1 := fun v hv => by
    have := (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v hv
    simpa [pow_two] using this
  obtain ⟨W, _, _, _, _, ρ, hirr, htr, hgenρ, hM, hperf, hL1, hs, hC⟩ :=
    TransvIrr.exists_rep_of_setting hset hV2 hsn
      (fun T hTM hMT hCT x hx hxn => TransvIrr.normal_gen hX hA hL hTM hMT hCT hx hxn)
  have hnorm : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hset.le).mpr hset.normL
  have hshape := shapeOut_map_of_transvection_rep ρ (L.subgroupOf (L ⊔ S)) ⟨s, hset.mem⟩ hirr htr
    hgenρ hM hperf hL1 hs
  refine ⟨_, inferInstance, hshape, ?_⟩
  let π := autOnHom S L
  have hπ := autOnHom_surjective S L
  let φ : ↥L →* ↥((L.subgroupOf (L ⊔ S)).map ρ) :=
    (ρ.comp (Subgroup.inclusion hset.le)).codRestrict _ fun l =>
      ⟨⟨l, hset.le l.2⟩, l.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, l', hl', rfl⟩
    exact ⟨⟨(l' : G), hl'⟩, Subtype.ext rfl⟩
  have hφ1 : ∀ l : ↥L, φ l = 1 ↔ ρ ⟨l, hset.le l.2⟩ = 1 := fun l =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hk : π.ker ≤ φ.ker := by
    intro l hl
    have := (autOnHom_eq_one_iff S L l).mp hl
    exact (hφ1 l).mpr (hC _ this)
  have hq := isQuasisimple_autOn hA hL hSL
  have hcomm := hq.1.commutator_eq_top
  have hperfTop : ⁅(⊤ : Subgroup ↥(autOn L (blockV S L))), (⊤ : Subgroup ↥(autOn L (blockV S L)))⁆ =
      (⊤ : Subgroup ↥(autOn L (blockV S L))) := by
    rw [← _root_.commutator_def]; exact hcomm
  have hcen : ∀ a ∈ φ.ker, π a ∈ Subgroup.center ↥(autOn L (blockV S L)) := by
    intro a ha
    have hNn : (φ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top
      hcomm hq.2.1 _ hNn with hc | htop
    · exact hc ⟨a, ha, rfl⟩
    · exfalso
      apply hL1
      intro l' hl'
      let l : ↥L := ⟨l', hl'⟩
      have hl : π l ∈ φ.ker.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨a', ha', hπa⟩ := hl
      have h1 : a'⁻¹ * l ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπa, inv_mul_cancel]
      have h2 : φ l = 1 := by
        have : φ (a' * (a'⁻¹ * l)) = 1 := by
          rw [map_mul, ha', hk h1, one_mul]
        rwa [mul_inv_cancel_left] at this
      exact (hφ1 l).mp h2
  obtain ⟨h, hhs, hhk, -⟩ := CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.exists_central_factor
    π hπ φ hφ hk hcen
  exact CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.nonempty_quotientCenterEquiv_of_central_ker
    h hhs hhk hperfTop

end CFSG.HardMathSupport.Cooperstein.StructureLie
