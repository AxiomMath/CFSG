module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.StronglyEmbedded.TheoremSE.InvolutionCoreTransitivity
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem oddCore_le_of_rank_two_stronglyEmbedded
    (H : Subgroup G) (hH : IsStronglyEmbedded H) (hrank : TwoRankAtLeastTwo G) :
    oddCore G ≤ H := by
  obtain ⟨T, hTH⟩ := hH.containsSylowTwo
  obtain ⟨E, hEcard, hEsq⟩ := twoRankAtLeastTwo_of_contains_sylow T hTH hrank
  let V : Subgroup G := E.map H.subtype
  have hVH : V ≤ H := Subgroup.map_subtype_le E
  have hVcard : Nat.card V = 4 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hEcard
  have hVsq : ∀ v : V, v ^ 2 = 1 := by
    intro v
    obtain ⟨e, he, hev⟩ := Subgroup.mem_map.mp v.property
    apply Subtype.ext
    change (v : G) ^ 2 = 1
    rw [← hev]
    exact congrArg (fun x : E => (x : G)) (hEsq ⟨e, he⟩)
  exact fourGroup_odd_subgroup_le_stronglyEmbedded hH hVH hVcard hVsq
    Subgroup.le_normalizer_of_normal (CFSG.ComponentClassification.OddCore.odd_card G)

theorem exists_normal_regular_twoSubgroup_of_corefree
    (H : Subgroup G) (hH : IsStronglyEmbedded H) (hrank : TwoRankAtLeastTwo G)
    (hcore : oddCore G = ⊥) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ H ∧
      (S.subgroupOf H).Normal ∧
      IsRegularOn S {omega : G ⧸ H | omega ≠ QuotientGroup.mk 1} := by
  let L : Subgroup G := involutionCore G
  let K : Subgroup L := twoPrimeCore L
  let B : Subgroup L := (H ⊓ L).subgroupOf L
  let q : L →* (L ⧸ K) := QuotientGroup.mk' K
  have hLrank : TwoRankAtLeastTwo L := twoRankAtLeastTwo_involutionCore_iff.mpr hrank
  have hBender : TheoremSEBenderConclusion H := by
    rcases theorem_SE H hH with hlow | hmodel
    · exact (hlow hLrank).elim
    · exact hmodel
  have hKbot : K = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective K L.subtype_injective).mp
    have hmap := CFSG.ComponentClassification.OddCore.normal_intersection G L
    change (oddCore L).map L.subtype = L ⊓ oddCore G at hmap
    rw [hcore, inf_bot_eq] at hmap
    simpa only [K, oddCore_eq_twoPrimeCore] using hmap
  have hKB : K ≤ B := by
    intro k hk
    exact hBender.2.1 (Subgroup.mem_map_of_mem L.subtype hk)
  have hKodd : Nat.Coprime 2 (Nat.card K) := by
    simpa [K, twoPrimeCore] using pPrimeCore_coprime_card (p := 2) (G := L)
  have hKcentral : K ≤ Subgroup.center L := by rw [hKbot]; exact bot_le
  have hmodel : IsSimpleBenderGroup (L ⧸ K) := hBender.1
  have hborel : IsBorelSubgroup (B.map q) := hBender.2.2
  obtain ⟨Pbar, hPbarNormal, hPbarRegular⟩ :=
    simpleBender_borel_normalSylow_regular hborel hmodel
  obtain ⟨P, hPNormal, hPmap, hPinj⟩ :=
    sylow_lift_of_central_odd_core K B hKB hKodd hKcentral Pbar hPbarNormal
  let R : Subgroup L := (P : Subgroup B).map B.subtype
  let S : Subgroup G := R.map L.subtype
  have hregCoset : IsRegularOn R {omega : L ⧸ B | omega ≠ QuotientGroup.mk 1} := by
    apply coset_isRegularOn_of_surjective q (QuotientGroup.mk'_surjective K)
      B R ((Pbar : Subgroup (B.map q)).map (B.map q).subtype)
    · simpa only [q, QuotientGroup.ker_mk'] using hKB
    · exact hPmap
    · exact hPinj
    · exact hPbarRegular
  let alpha : G ⧸ H := QuotientGroup.mk 1
  have hpoint : pointStabilizerIn L alpha = B := by
    ext l
    change (l : G) ∈ MulAction.stabilizer G alpha ↔ (l : G) ∈ H ∧ (l : G) ∈ L
    rw [show MulAction.stabilizer G alpha = H by simp [alpha]]
    simp
  have hregOrbit : IsRegularOn S
      {omega : G ⧸ H | InOrbit L alpha omega ∧ omega ≠ alpha} := by
    apply regularOn_orbit_of_coset L alpha R
    rw [hpoint]
    exact hregCoset
  let : MulAction.IsPretransitive L (G ⧸ H) := hH.involutionCore_isPretransitive
  have horbit (omega : G ⧸ H) : InOrbit L alpha omega :=
    MulAction.exists_smul_eq L alpha omega
  have hSle : S ≤ H := by
    intro s hs
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hr
    exact b.property.1
  let H0 : Subgroup G := H ⊓ L
  let e : B ≃* H0 := Subgroup.subgroupOfEquivOfLe inf_le_right
  let P0 : Sylow 2 H0 := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hP0 : (P0 : Subgroup H0) = (P : Subgroup B).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
  have hP0Normal : (P0 : Subgroup H0).Normal := by
    rw [hP0]
    exact hPNormal.map e.toMonoidHom e.surjective
  have hSmap : S = (P0 : Subgroup H0).map H0.subtype := by
    rw [hP0, Subgroup.map_map]
    change ((P : Subgroup B).map B.subtype).map L.subtype = _
    rw [Subgroup.map_map]
    congr 1
  have hH0le : H0 ≤ H := inf_le_left
  have hH0Normal : (H0.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hH0le]
    intro x h hx hh
    exact ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh),
      (inferInstance : L.Normal).conj_mem x hx.2 h⟩
  have hSnormal : (S.subgroupOf H).Normal :=
    normal_subgroupOf_map_of_characteristic_of_normal H0 S H hH0le hH0Normal
      (P0 : Subgroup H0) (Sylow.characteristic_of_normal P0 hP0Normal) hSmap hSle
  refine ⟨S, (P.isPGroup'.map B.subtype).map L.subtype, hSle, hSnormal, ?_⟩
  intro a b ha hb
  exact hregOrbit ⟨horbit a, ha⟩ ⟨horbit b, hb⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
