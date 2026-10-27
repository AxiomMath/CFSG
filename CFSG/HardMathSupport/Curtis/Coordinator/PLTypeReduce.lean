module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeReduceModel
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeReduceKernel
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeOfTransvection
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeSetting

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock NineThreeThree barM blockV blockPL)
open CFSG.Open (pCoreOf)
open CFSG.HardMathSupport.Cooperstein.Coordinator (le_normalizer_of_isWeakSBlock)
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub ker_barMHomSub)
open CFSG.HardMathSupport.Cooperstein.StructureLie
open Subgroup
open scoped commutatorElement

section Restrict

variable {G : Type} [Group G] {S L : Subgroup G}
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def restrictRho (ρ : ↥(L ⊔ S) →* LinearMap.GeneralLinearGroup (ZMod 2) W)
    (N : Subgroup G) (hN : N ≤ L ⊔ S) : ↥N →* ↥((N.subgroupOf (L ⊔ S)).map ρ) :=
  (ρ.comp (Subgroup.inclusion hN)).codRestrict _ fun n => ⟨⟨n, hN n.2⟩, n.2, rfl⟩

theorem restrictRho_surjective (ρ : ↥(L ⊔ S) →* LinearMap.GeneralLinearGroup (ZMod 2) W)
    (N : Subgroup G) (hN : N ≤ L ⊔ S) : Function.Surjective (restrictRho ρ N hN) := by
  rintro ⟨y, n, hn, rfl⟩
  exact ⟨⟨(n : G), hn⟩, Subtype.ext rfl⟩

theorem restrictRho_eq_one_iff (ρ : ↥(L ⊔ S) →* LinearMap.GeneralLinearGroup (ZMod 2) W)
    (N : Subgroup G) (hN : N ≤ L ⊔ S) (n : ↥N) :
    restrictRho ρ N hN n = 1 ↔ ρ ⟨n, hN n.2⟩ = 1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Restrict

section Main

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {s : G}
  {ρ : ↥(L ⊔ S) →* LinearMap.GeneralLinearGroup (ZMod 2) W}

theorem ker_barMHomSub_eq_ker_restrictRho (rep : PLRep M S L s ρ) {N : Subgroup G} (hNL : N ≤ L) :
    (barMHomSub (hNL.trans rep.hL.le)).ker = (restrictRho ρ N (hNL.trans le_sup_left)).ker := by
  ext n
  rw [ker_barMHomSub, mem_subgroupOf, MonoidHom.mem_ker (f := restrictRho ρ N _),
    restrictRho_eq_one_iff]
  exact (rep.rho_eq_one_iff_mem_pCoreOf (hNL n.2)).symm

theorem nonempty_barM_mulEquiv_map (rep : PLRep M S L s ρ) :
    Nonempty (↥(barM M L) ≃* ↥((L.subgroupOf (L ⊔ S)).map ρ)) :=
  nonempty_mulEquiv_of_ker_eq _ _ (CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective _)
    (restrictRho_surjective ρ L le_sup_left)
    (ker_barMHomSub_eq_ker_restrictRho rep le_rfl)

theorem map_normalizer_inf_eq (rep : PLRep M S L s ρ) :
    ((normalizer (S : Set G) ⊓ L).subgroupOf (L ⊔ S)).map ρ =
      (L.subgroupOf (L ⊔ S)).map ρ ⊓
        centralizer {ρ ⟨s, mem_sup_right rep.hsS⟩} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyN : (y : G) ∈ normalizer (S : Set G) ⊓ L := hy
    refine ⟨⟨y, mem_subgroupOf.mpr hyN.2, rfl⟩, ?_⟩
    refine mem_centralizer_iff.mpr fun t ht => ?_
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact (rep.rho_comm_of_mem_normalizer hyN.2 hyN.1).symm
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    have hyL : (y : G) ∈ L := hy
    refine ⟨y, mem_subgroupOf.mpr ⟨?_, hyL⟩, rfl⟩
    exact (rep.rho_comm_iff_mem_normalizer hyL).mp (mem_centralizer_iff.mp hc _ rfl).symm

theorem nonempty_blockPL_mulEquiv_map (rep : PLRep M S L s ρ) :
    Nonempty (↥(blockPL M S L) ≃*
      ↥(((normalizer (S : Set G) ⊓ L).subgroupOf (L ⊔ S)).map ρ)) :=
  nonempty_mulEquiv_of_ker_eq
    (barMHomSub (inf_le_right.trans rep.hL.le : normalizer (S : Set G) ⊓ L ≤ M)) _
    (CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective _)
    (restrictRho_surjective ρ _ ((inf_le_right.trans le_sup_left) :
      normalizer (S : Set G) ⊓ L ≤ L ⊔ S))
    (ker_barMHomSub_eq_ker_restrictRho rep (inf_le_right : normalizer (S : Set G) ⊓ L ≤ L))

end Main

theorem exists_transvectionModel {G : Type} [Group G] [Finite G]
    {M S L : Subgroup G} (hK : CFSG.Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (h3 : NineThreeThree M S L)
    (hZ : Subgroup.center ↥(barM M L) = ⊥) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : FiniteDimensional (ZMod 2) W)
      (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
      (t : LinearMap.GeneralLinearGroup (ZMod 2) W),
      TransvectionModel H t ∧ Nonempty (↥(barM M L) ≃* ↥⁅H, H⁆) ∧
        Nonempty (↥(blockPL M S L) ≃* ↥(⁅H, H⁆ ⊓ Subgroup.centralizer {t})) := by
  obtain ⟨s, hsS, hgen, hsn, hZ2⟩ := h3.2.2.2
  have hset := TransvIrr.setting_of hK hA hL hsS hgen hsn hZ2
  have hSL := le_normalizer_of_isWeakSBlock hK hA hL
  have hV2 : ∀ v ∈ blockV S L, v * v = 1 := fun v hv => by
    have := (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v hv
    simpa [pow_two] using this
  obtain ⟨W, _, _, _, _, ρ, hirr, htr, hgenρ, hM, hperf, hL1, hs, hC⟩ :=
    TransvIrr.exists_rep_of_setting hset hV2 hsn
      (fun T hTM hMT hCT x hx hxn => TransvIrr.normal_gen hK hA hL hTM hMT hCT hx hxn)
  have hnorm : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hset.le).mpr hset.normL
  obtain ⟨hLeq, hmodel⟩ := transvectionModel_of_rep ρ (L.subgroupOf (L ⊔ S)) ⟨s, hset.mem⟩ hirr
    htr hgenρ hM hperf hL1 hs
  have rep : PLRep M S L s ρ := ⟨hA, hL, hSL, hZ, hC, hL1, hsS, hgen, htr⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, ρ.range, ρ ⟨s, hset.mem⟩, hmodel, ?_, ?_⟩
  · obtain ⟨e⟩ := nonempty_barM_mulEquiv_map rep
    exact ⟨e.trans (MulEquiv.subgroupCongr hLeq)⟩
  · obtain ⟨e⟩ := nonempty_blockPL_mulEquiv_map rep
    have hP := map_normalizer_inf_eq rep
    rw [hLeq] at hP
    exact ⟨e.trans (MulEquiv.subgroupCongr hP)⟩

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
