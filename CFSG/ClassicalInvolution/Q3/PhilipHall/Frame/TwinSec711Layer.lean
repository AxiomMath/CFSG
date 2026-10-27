module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEHullKey
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf18OddW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open CFSG.CGT.PushingUpLit.SolKNA.R4.ThmE CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement


section Adapted

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem exists_adapted (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    {W : Subgroup G} (hW2 : IsPGroup 2 ↥W) (hWC : W ≤ Subgroup.centralizer ({u} : Set G)) :
    ∃ (S : Sylow 2 G) (S₁ : Sylow 2 ↥(coreHull Ω u)), W ≤ (S : Subgroup G) ∧
      (S₁ : Subgroup ↥(coreHull Ω u)).map (secEmb Ω u) ≤ (S : Subgroup G) := by
  classical
  set C := Subgroup.centralizer ({u} : Set G) with hC
  set L := coreHull Ω u with hL
  have hWc2 : IsPGroup 2 ↥(W.subgroupOf C) := hW2.comap_of_injective C.subtype C.subtype_injective
  have hWcN : W.subgroupOf C ≤ Subgroup.normalizer (L : Set ↥C) := fun g _ =>
    mem_normalizer_of_conjSub_eq (conjSub_coreHull hΩ hc2 g)
  obtain ⟨P, hP, hPinv⟩ := AscQuot.exists_sylow_normalized' hWc2 hWcN
  set PG : Subgroup G := P.map C.subtype with hPG
  have hPG2 : IsPGroup 2 ↥PG := hP.2.1.map C.subtype
  have hWPn : W ≤ Subgroup.normalizer (PG : Set G) := by
    intro w hw
    refine mem_normalizer_of_conjSub_eq ?_
    have h1 := conjSub_map C.subtype (⟨w, hWC hw⟩ : ↥C) P
    rw [hPinv ⟨w, hWC hw⟩ (Subgroup.mem_subgroupOf.mpr hw)] at h1
    exact h1
  have hsup : IsPGroup 2 ↥(W ⊔ PG) := hW2.to_sup_of_normal_right' hPG2 hWPn
  obtain ⟨S, hS⟩ := hsup.exists_le_sylow
  have hP₁2 : IsPGroup 2 ↥(P.subgroupOf L) :=
    hP.2.1.comap_of_injective L.subtype L.subtype_injective
  let S₁ : Sylow 2 ↥L := ⟨P.subgroupOf L, hP₁2, fun {Q} hQ hle => by
    have hQ' : IsPGroup 2 ↥(Q.map L.subtype) := hQ.map _
    have hPQ : P ≤ Q.map L.subtype := fun x hx =>
      ⟨⟨x, hP.1 hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hQL : Q.map L.subtype ≤ L := by
      rintro _ ⟨q, -, rfl⟩
      exact q.2
    have heq := hP.2.2 _ hQL hQ' hPQ
    refine le_antisymm (fun x hx => ?_) hle
    have hx' : (x : ↥C) ∈ Q.map L.subtype := ⟨x, hx, rfl⟩
    rw [heq] at hx'
    exact Subgroup.mem_subgroupOf.mpr hx'⟩
  refine ⟨S, S₁, le_sup_left.trans hS, ?_⟩
  have hmap : (S₁ : Subgroup ↥L).map (secEmb Ω u) = PG := by
    show (P.subgroupOf L).map (secEmb Ω u) = P.map C.subtype
    unfold secEmb
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hP.1]
  rw [hmap]
  exact le_sup_right.trans hS

end Adapted

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

@[expose] def secD (Ω : Set (Subgroup G)) (W : Subgroup G) (u : G) :
    Set (Subgroup (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u))) :=
  {N | ∃ J ∈ tqMembers3 Ω u, ∃ T ∈ DSet Ω W, IsSylow2In T J ∧
      T ≤ Subgroup.centralizer ({u} : Set G) ∧ N = TwinDisc.secImg Ω u J}

theorem layer (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    {W : Subgroup G} (hW : W ∈ WSet Ω) (huW : u ∈ W) :
    ∃ Pb : Sylow 2 (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)),
      ∀ {Ub : Subgroup (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u))},
        Ub ∈ USet (TwinDisc.secFam Ω u) → Ub ≤ (Pb : Subgroup _) →
        ∀ {N : Subgroup (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u))},
          N ∈ TwinDisc.secFam Ω u → Ub ≤ N → N ∈ secD Ω W u := by
  classical
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hW2 : IsPGroup 2 ↥W := isPGroup_of_mem_WSet hW
  have hWC : W ≤ Subgroup.centralizer ({u} : Set G) := fun w hw => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hWab u huW w hw).symm
  obtain ⟨S, S₁, hWS, hS₁S⟩ := exists_adapted hΩ hc2 hW2 hWC
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω u)) with hπ
  let Pb : Sylow 2 (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) :=
    Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective _) S₁
  have hPb : (Pb : Subgroup (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u))) =
      (S₁ : Subgroup ↥(coreHull Ω u)).map π :=
    Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective _) S₁
  refine ⟨Pb, fun {Ub} hUb hUbP {N} hN hUbN => ?_⟩
  have hΦ : HypOmegaGen (TwinDisc.secFam Ω u) := hypOmegaGen_secFam hΩ hc2
  have hΩL : HypOmegaGen (hullFam Ω u) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) (coreHull Ω u)
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(coreHull Ω u))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω u)
  obtain ⟨hmap, M', hM', hUM', hUU⟩ :=
    TwinThmEW.lift_USet (Ω := hullFam Ω u) hΦ hΩL hodd S₁.isPGroup' hUb (hPb ▸ hUbP)
  have hM'N : M'.map π = N := by
    have h1 : M'.map π ∈ TwinDisc.secFam Ω u := map_mem_quotFamily hM'
    have h2 : Ub ≤ M'.map π := by
      rw [← hmap]
      exact Subgroup.map_mono hUM'
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΦ hUb
    exact Sec6Gen.eq_of_le_of_le hΦ h1 hN (Sec6Gen.isPGroup_of_mem_USet hΦ hUb) h4 h2 hUbN
  obtain ⟨J, hJ, rfl⟩ := exists_of_mem_hullFam hM'
  obtain ⟨hUinf, -, -⟩ :=
    hullpf_key hΩ hc2 hW hWS (hWS huW) hS₁S hJ hUU inf_le_left hUM'
  have hUS : J ⊓ W ≤ (S : Subgroup G) := inf_le_right.trans hWS
  obtain ⟨T, hTD, hTJ⟩ :=
    Q3CL.Thompson.exists_sylow_mem_DSet hΩ hW hWS hJ.1 hUinf inf_le_left hUS
  have hsup : IsPGroup 2 ↥(T ⊔ W) := hTJ.2.1.to_sup_of_normal_right' hW2 hTD.2
  obtain ⟨S', hS'⟩ := hsup.exists_le_sylow
  have hTc : T ≤ Subgroup.centralizer ({u} : Set G) :=
    (le_inf hTJ.1 (le_sup_left.trans hS')).trans
      ((hullpf_inf_le_coreAt hJ.2 (hS' (le_sup_right (a := T) huW))).trans
        (TwinADescent.coreAt_le_centralizer u J))
  exact ⟨J, hJ, T, hTD, hTJ, hTc, hM'N.symm⟩

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711
