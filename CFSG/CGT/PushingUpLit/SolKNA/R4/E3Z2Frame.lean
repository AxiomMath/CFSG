module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3F1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3AM710
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3FrameR.map_mem_secΩ (hF : E3FrameR r n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    {L : Subgroup Y} (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) :
    ((L.subgroupOf (Subgroup.centralizer ({u} : Set Y))).subgroupOf (secH R u)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))) ∈ E3.secΩ R u := by
  obtain ⟨l, hl, rfl⟩ := hO hL
  have hlC : l ∈ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer hl
  have hlH : (⟨l, hlC⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u :=
    hF.nbrGen_le_secH hO (Subgroup.mem_subgroupOf.mpr hl)
  refine ⟨QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨l, hlC⟩, hlH⟩, ?_⟩
  show conjSub _ (tightCore (secR R u)) = _
  rw [hF.tightCore_secR, ← TwistQ.conjSub_map, conjSub_subgroupOf, conjSub_subgroupOf]

theorem E3FrameR.partnerUniq_of_oneOrbit (hF : E3FrameR r n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hthin : ∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    PartnerUniq (CoreAssembly.conjClass (tightCore R)) W := by
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  have hR : TypeRFam r (CoreAssembly.conjClass (tightCore R)) := TightLargeHypR.typeRFam hF.large
  have hRC := hR.restrict C
  obtain ⟨Sq, hdq, -⟩ := hF.exists_secClsR htu ht
  have hPΦ : Q3CL.PartIHypG (E3.secΩ R u) := hdq.partIHypG
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) := hF.maxAdj.1.2.1
  obtain ⟨g₀, hg₀'⟩ := hJΩ
  have hg₀ : conjSub g₀ (tightCore R) = J := hg₀'
  have htrans : ∀ J' ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g J = J' := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g * g₀⁻¹, ?_⟩
    show conjSub (g * g₀⁻¹) J = conjSub g (tightCore R)
    rw [← hg₀, conjSub_mul, conjSub_inv_conjSub]
  refine E3.partnerUniq_of_nbr hR.hyp htrans ?_ hW
  intro W₀ hW₀ L hL L' hL' hU hU'
  have hLC : L ≤ C := hF.nbr_le_centralizer hL
  have hL'C : L' ≤ C := hF.nbr_le_centralizer hL'
  have hLX : L.subgroupOf C ≤ secH R u :=
    (Subgroup.subgroupOf_mono C (le_iSup₂ (f := fun M (_ : M ∈ {M | TC.nbrAdj
      (CoreAssembly.conjClass (tightCore R)) J M}) => M) L ⟨⟨g₀, hg₀⟩, hL⟩)).trans
      (hF.nbrGen_le_secH hO)
  have hL'X : L'.subgroupOf C ≤ secH R u :=
    (Subgroup.subgroupOf_mono C (le_iSup₂ (f := fun M (_ : M ∈ {M | TC.nbrAdj
      (CoreAssembly.conjClass (tightCore R)) J M}) => M) L' ⟨⟨g₀, hg₀⟩, hL'⟩)).trans
      (hF.nbrGen_le_secH hO)
  have hcard : ∀ M : Subgroup Y, M ≤ C →
      Nat.card ↥(M.subgroupOf C ⊓ W₀.subgroupOf C) = Nat.card ↥(M ⊓ W₀) := by
    intro M hMC
    have e : M.subgroupOf C ⊓ W₀.subgroupOf C = (M ⊓ W₀).subgroupOf C := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hMC)).toEquiv
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hR.hyp hU
  obtain ⟨-, -, -, -, -, -, -, -, h4'⟩ := Sec6Gen.exists_data_of_mem_USet hR.hyp hU'
  have key := E3.eq_of_thinSec hRC.hyp hRC.noTwins hPΦ hthin (P := W₀.subgroupOf C)
    ((isPGroup_of_mem_WSet hW₀).comap_subtype) ⟨L, hL.1, hLC, rfl⟩ ⟨L', hL'.1, hL'C, rfl⟩ hLX
    hL'X (hF.map_mem_secΩ hO hL) (hF.map_mem_secΩ hO hL') (by rw [hcard L hLC]; exact h4)
    (by rw [hcard L' hL'C]; exact h4')
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hLC, inf_of_le_left hL'C] at key
  exact key

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
