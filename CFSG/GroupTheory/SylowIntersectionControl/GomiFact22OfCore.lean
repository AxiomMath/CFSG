module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiCenterQuotient
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCoreOfTrichotomy
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicOfBorelTits
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTrichotomyLocal
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTrichotomyOfParabolic
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact22Component
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact22Sylow
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiHyp21Center
import CFSG.GroupTheory.SylowIntersectionControl.GomiParabolicSwapMap
import CFSG.GroupTheory.SylowInfNormal
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCoprimeMap
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

private theorem inf_normalizer_le_centralizer_of_coprime {G : Type} [Group G] [Finite G]
    {Z H : Subgroup G} [Z.Normal] (hZodd : Nat.Coprime (Nat.card Z) 2) (hH : IsPGroup 2 H) :
    Z ⊓ normalizer (H : Set G) ≤ centralizer (H : Set G) := by
  rintro z ⟨hzZ, hzN⟩
  rw [mem_centralizer_iff]
  intro h hh
  have hcZ : z * h * z⁻¹ * h⁻¹ ∈ Z := by
    have hconj : h * z * h⁻¹ ∈ Z := (inferInstance : Z.Normal).conj_mem z hzZ h
    have hmem := Z.mul_mem hzZ (Z.inv_mem hconj)
    convert hmem using 1
    group
  have hcH : z * h * z⁻¹ * h⁻¹ ∈ H :=
    H.mul_mem ((Subgroup.mem_normalizer_iff.mp hzN h).mp hh) (H.inv_mem hh)
  have hbot : Z ⊓ H = ⊥ := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥H)).mp hH
    have hcop : Nat.Coprime (Nat.card Z) (Nat.card H) := by
      rw [hn]
      exact hZodd.pow_right n
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hmem : z * h * z⁻¹ * h⁻¹ ∈ Z ⊓ H := ⟨hcZ, hcH⟩
  rw [hbot, mem_bot] at hmem
  have hcomm : z * h = h * z := by
    calc z * h = z * h * z⁻¹ * h⁻¹ * (h * z) := by group
      _ = 1 * (h * z) := by rw [hmem]
      _ = h * z := one_mul _
  exact hcomm.symm

private theorem dvd_relIndex_inf_normalizer_of_not_isSylowTwoOf {G : Type} [Group G] [Finite G]
    {N H : Subgroup G} [N.Normal] (hH : IsPGroup 2 H)
    (hJ : ¬ IsSylowTwoOf (H ⊓ N) N) :
    2 ∣ H.relIndex (N ⊓ normalizer (H : Set G)) := by
  obtain ⟨T, hHT⟩ := hH.exists_le_sylow
  have hSTop : IsSylowTwoOf (T : Subgroup G) ⊤ :=
    ⟨le_top, T.isPGroup',
      fun h => T.not_dvd_index (Subgroup.relIndex_top_right (T : Subgroup G) ▸ h)⟩
  have hTNsyl : IsSylowTwoOf (N ⊓ T) N :=
    CFSG.isSylowTwoOf_inf_of_normal hSTop le_top (by rw [Subgroup.normalizer_eq_top])
  have hUH : ¬ N ⊓ T ≤ H := by
    intro hle
    have hEq : H ⊓ N = N ⊓ T :=
      le_antisymm (le_inf inf_le_right (inf_le_left.trans hHT)) (le_inf hle inf_le_left)
    exact hJ (hEq.symm ▸ hTNsyl)
  have hHU : H ≤ Subgroup.normalizer ((N ⊓ T : Subgroup G) : Set G) := by
    have h1 : H ≤ Subgroup.normalizer (N : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    exact (le_inf h1 (hHT.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact dvd_relIndex_inf_normalizer hH hTNsyl.2.1 inf_le_left hHU hUH

private theorem exists_K_of_dvd_relIndex {G : Type} [Group G] [Finite G] {N Z H : Subgroup G}
    [N.Normal] [Z.Normal] (hZodd : Nat.Coprime (Nat.card Z) 2)
    (hZc : Z ≤ centralizer (N : Set G)) (hH : IsPGroup 2 H)
    (hdvd : 2 ∣ H.relIndex (N ⊓ normalizer (H : Set G))) :
    ∃ K : Subgroup G, H ≤ K ∧ K ≤ normalizer (H : Set G) ∧
      (K.subgroupOf (normalizer (H : Set G))).IsSubnormal ∧ 2 ∣ H.relIndex K ∧
      normalizer (H : Set G) ⊓ Z ≤ centralizer (K : Set G) := by
  obtain ⟨K, hHK, hKNX, hKsub, hKdvd, hKY⟩ :=
    exists_le_of_inf_normalizer_le (L := N) (X := ⊤) (H := H)
      (Y := N ⊓ normalizer (H : Set G) ⊔ H) inferInstance le_top le_top hdvd
      le_sup_left le_sup_right
  rw [inf_top_eq] at hKNX hKsub
  have hZs : Z ⊓ normalizer (H : Set G) ≤
      centralizer (((N ⊓ normalizer (H : Set G)) ⊔ H : Subgroup G)) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact (inf_le_left : Z ⊓ normalizer (H : Set G) ≤ Z).trans
        (hZc.trans (Subgroup.centralizer_le (inf_le_left : N ⊓ normalizer (H : Set G) ≤ N)))
    · rw [Subgroup.le_centralizer_iff]
      exact inf_normalizer_le_centralizer_of_coprime hZodd hH
  refine ⟨K, hHK, hKNX, hKsub, hKdvd, ?_⟩
  rw [inf_comm]
  exact hZs.trans (Subgroup.centralizer_le hKY)

private theorem isPIsolatedOver_normalizer_map_of_not_isSylowTwoOf {G : Type} [Group G] [Finite G]
    {N Z H : Subgroup G} [N.Normal] [Z.Normal] (hZodd : Nat.Coprime (Nat.card Z) 2)
    (hZc : Z ≤ centralizer (N : Set G)) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H)
    (hJ : ¬ IsSylowTwoOf (H ⊓ N) N) :
    IsPIsolatedOver 2
      (normalizer ((H.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)))
      (H.map (QuotientGroup.mk' Z)) := by
  obtain ⟨K, hHK, hKNX, hKsub, hKdvd, hcent⟩ :=
    exists_K_of_dvd_relIndex hZodd hZc hH
      (dvd_relIndex_inf_normalizer_of_not_isSylowTwoOf hH hJ)
  exact IsPIsolatedOver.normalizer_map_mk' Z hZodd hiso hH hHK hKNX hKsub hKdvd hcent

private theorem exists_sylow_not_isGomiParabolicSwap_map_mk' {G : Type} [Group G] [Finite G]
    {L Z : Subgroup G} [Z.Normal] (hZodd : Nat.Coprime (Nat.card Z) 2)
    (hZZ : Z ≤ centralizer (Z : Set G)) (hZL : Z ≤ centralizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hquasi : CFSG.IsQuasisimple ↥L) (hLZ : Z.subgroupOf L = center ↥L)
    (hswap : (IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)) →
      ∃ S : Sylow 2 G, ¬ IsGomiParabolicSwap (S : Subgroup G) L) :
    (IsGomiL3 (↥(L.map (QuotientGroup.mk' Z)) ⧸ center ↥(L.map (QuotientGroup.mk' Z))) ∨
      IsGomiSp4 (↥(L.map (QuotientGroup.mk' Z)) ⧸ center ↥(L.map (QuotientGroup.mk' Z)))) →
      ∃ S : Sylow 2 (G ⧸ Z),
        ¬ IsGomiParabolicSwap (S : Subgroup (G ⧸ Z)) (L.map (QuotientGroup.mk' Z)) := by
  intro htypes
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_center_map_mk' hquasi hLZ
  obtain ⟨S, hS⟩ := hswap (htypes.imp (fun h => h.of_mulEquiv e) (fun h => h.of_mulEquiv e))
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective Z), fun hh => hS ?_⟩
  rw [Sylow.coe_mapSurjective] at hh
  exact IsGomiParabolicSwap.of_map_mk' hZodd hZZ hZL hperf S.isPGroup' hh

private theorem not_exception_map_mk' {G : Type} [Group G] [Finite G] {L Z : Subgroup G} [Z.Normal]
    (hquasi : CFSG.IsQuasisimple ↥L) (hLZ : Z.subgroupOf L = center ↥L)
    (hexc : ¬ (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨
      IsGomiSz (↥L ⧸ center ↥L))) :
    ¬ (IsGomiL2 (↥(L.map (QuotientGroup.mk' Z)) ⧸ center ↥(L.map (QuotientGroup.mk' Z))) ∨
      IsGomiU3 (↥(L.map (QuotientGroup.mk' Z)) ⧸ center ↥(L.map (QuotientGroup.mk' Z))) ∨
      IsGomiSz (↥(L.map (QuotientGroup.mk' Z)) ⧸ center ↥(L.map (QuotientGroup.mk' Z)))) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_center_map_mk' hquasi hLZ
  rintro (h | h | h)
  · exact hexc (Or.inl (h.of_mulEquiv e))
  · exact hexc (Or.inr (Or.inl (h.of_mulEquiv e)))
  · exact hexc (Or.inr (Or.inr (h.of_mulEquiv e)))

private theorem exists_quotient_of_gomiChevCore (hIso : GomiChevIsolated) (hCore : GomiChevCore)
    (hRad : GomiChevRadical) {G : Type} [Group G] [Finite G] {L N Z H : Subgroup G}
    [N.Normal] [Z.Normal] (hNL : N = normalClosure (L : Set G)) (hZN : Z ≤ N)
    (hZc : Z ≤ centralizer (N : Set G)) (hZL : Z ≤ centralizer (L : Set G))
    (hZZ : Z ≤ centralizer (Z : Set G)) (hperf : ⁅L, L⁆ = L) (hL : GomiHyp21 L)
    (hLc : IsGomiChevTwo ↥L) (hLZ : Z.subgroupOf L = center ↥L)
    (hZodd : Nat.Coprime (Nat.card Z) 2)
    (hexc : ¬ (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨
      IsGomiSz (↥L ⧸ center ↥L)))
    (hswap : (IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)) →
      ∃ S : Sylow 2 G, ¬ IsGomiParabolicSwap (S : Subgroup G) L)
    (hH : IsPGroup 2 H) (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) :
    ∃ M : Subgroup (G ⧸ Z), M ≠ ⊤ ∧ Odd M.index ∧
      (∀ a ∈ normalizer ((H.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)),
        a ^ 2 ∈ H.map (QuotientGroup.mk' Z) → a ∈ M) ∧
      twoResidual (M ⊓ N.map (QuotientGroup.mk' Z) ⊓
        centralizer (pCoreOf 2 (M ⊓ N.map (QuotientGroup.mk' Z)) : Set (G ⧸ Z))) = ⊥ := by
  let π := QuotientGroup.mk' Z
  have hNmap : N.map π = normalClosure (L.map π : Set (G ⧸ Z)) := by
    rw [hNL, Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective Z), Subgroup.coe_map]
  have hLq_comm : GomiConjugatesCommute (L.map π) :=
    hL.toGomiConjugatesCommute.map (QuotientGroup.mk'_surjective Z)
  have hLq_inf : L.map π ⊓ centralizer (L.map π : Set (G ⧸ Z)) = ⊥ :=
    inf_centralizer_map_mk'_eq_bot hL.quasisimple hLZ
  have hLq_chev : IsGomiChevTwo ↥(L.map π) := hLc.map_mk' hLZ
  have hHq : IsPGroup 2 (H.map π) := hH.map π
  have hexcq := not_exception_map_mk' hL.quasisimple hLZ hexc
  have hswapq := exists_sylow_not_isGomiParabolicSwap_map_mk' hZodd hZZ hZL hperf
    hL.quasisimple hLZ hswap
  by_cases hJs : IsSylowTwoOf (H ⊓ N) N
  · have hJq : IsSylowTwoOf (H.map π ⊓ normalClosure (L.map π : Set (G ⧸ Z)))
        (normalClosure (L.map π : Set (G ⧸ Z))) := by
      rw [← hNmap]
      exact (isSylowTwoOf_inf_map_mk'_iff hZodd hZN hH).mpr hJs
    obtain ⟨M, hM1, hM2, hM3, hM4⟩ :=
      exists_of_isSylowTwoOf_inf_normalClosure hRad hLq_comm hLq_inf hLq_chev hJq
    exact ⟨M, hM1, hM2, fun a ha _ => hM3 ha, by rw [hNmap]; exact hM4⟩
  · have hisoq : IsPIsolatedOver 2 (normalizer (H.map π : Set (G ⧸ Z))) (H.map π) :=
      isPIsolatedOver_normalizer_map_of_not_isSylowTwoOf hZodd hZc hH hiso hJs
    have hJq : ¬ IsSylowTwoOf (H.map π ⊓ normalClosure (L.map π : Set (G ⧸ Z)))
        (normalClosure (L.map π : Set (G ⧸ Z))) := by
      rw [← hNmap]
      exact fun h => hJs ((isSylowTwoOf_inf_map_mk'_iff hZodd hZN hH).mp h)
    obtain ⟨M, hM1, hM2, hM3, hM4⟩ :=
      exists_of_not_isSylowTwoOf_inf_normalClosure hIso hCore hLq_comm hLq_inf hLq_chev
        hexcq hswapq hHq hisoq hJq
    exact ⟨M, hM1, hM2, hM3, by rw [hNmap]; exact hM4⟩

theorem gomiFact22_of_gomiChevCore (hIso : GomiChevIsolated) (hCore : GomiChevCore)
    (hRad : GomiChevRadical) : GomiFact22 := by
  intro G _ _ L hL hLc hexc hswap H _ hHp hiso
  let N : Subgroup G := normalClosure (L : Set G)
  have hN : N.Normal := Subgroup.normalClosure_normal
  let Z : Subgroup G := N ⊓ centralizer (N : Set G)
  have hZ : Z.Normal := inferInstance
  have hZN : Z ≤ N := inf_le_left
  have hZc : Z ≤ centralizer (N : Set G) := inf_le_right
  have hZL : Z ≤ centralizer (L : Set G) :=
    hZc.trans (Subgroup.centralizer_le fun x hx => Subgroup.le_normalClosure hx)
  have hZZ : Z ≤ centralizer (Z : Set G) :=
    hZc.trans (Subgroup.centralizer_le fun x hx => hZN hx)
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hL.quasisimple.1
  have hLZ : Z.subgroupOf L = center ↥L := hL.toGomiConjugatesCommute.subgroupOf_center_eq
  have hZodd : Nat.Coprime (Nat.card Z) 2 :=
    hL.toGomiConjugatesCommute.coprime_card_center_normalClosure hLc.2.1
  obtain ⟨Mbar, hMbarNe, hMbarOdd, hNclause, hO2⟩ :=
    exists_quotient_of_gomiChevCore hIso hCore hRad (hNL := rfl) hZN hZc hZL hZZ hperf
      hL hLc hLZ hZodd hexc hswap hHp hiso
  let M : Subgroup G := Mbar.comap (QuotientGroup.mk' Z)
  have hMmap : M.map (QuotientGroup.mk' Z) = Mbar :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) Mbar
  have hMneq : M ≠ ⊤ := by
    intro htop
    exact hMbarNe (by rw [← hMmap, htop,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)])
  have hModd : Odd M.index := by
    change Odd (Mbar.comap (QuotientGroup.mk' Z)).index
    rw [Subgroup.index_comap_of_surjective Mbar (QuotientGroup.mk'_surjective Z)]
    exact hMbarOdd
  refine ⟨M, hMneq, hModd, ?_, ?_⟩
  · have hMsq : ∀ a ∈ normalizer (H : Set G), a ^ 2 ∈ H → a ∈ M := by
      intro a ha ha2
      have h1 : (QuotientGroup.mk' Z) a ∈ normalizer
          ((H.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) :=
        Subgroup.le_normalizer_map _ (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
      have h2 : (QuotientGroup.mk' Z) a ^ 2 ∈ H.map (QuotientGroup.mk' Z) :=
        Subgroup.mem_map.mpr ⟨a ^ 2, ha2, by simp⟩
      exact Subgroup.mem_comap.mpr (hNclause _ h1 h2)
    exact hiso.exists_le_of_sq_mem hHp hMsq
  · have hMW : twoResidual (Mbar ⊓ N.map (QuotientGroup.mk' Z) ⊓
        centralizer (pCoreOf 2 (Mbar ⊓ N.map (QuotientGroup.mk' Z)) : Set (G ⧸ Z))) ≤ ⊥ :=
      hO2.le
    have hmain := twoResidual_inf_centralizer_le_comap (N := N) (Z := Z)
      hL.isPGroup_quotient hZc hZodd (M := Mbar) (W := ⊥) hMW
    have hbot : (⊥ : Subgroup (G ⧸ Z)).comap (QuotientGroup.mk' Z) = Z := by
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rw [hbot] at hmain
    exact hmain

theorem gomiFact22_of_parabolic (hIso : GomiChevIsolated) (hBT : GomiChevBorelTits)
    (hGen : GomiChevAtomGeneration) (hOrb : GomiChevAtomOrbit) (hRad : GomiChevRadical)
    (hSwap : GomiChevSwap) (hLevi : GomiChevLevi) : GomiFact22 :=
  gomiFact22_of_gomiChevCore hIso
    (gomiChevCore_of_trichotomy hIso
      (gomiChevTrichotomy_of_parabolic hBT hGen hOrb hRad hSwap hLevi)
      (gomiChevParabolic_of_borelTits hBT) hRad) hRad

end CFSG.GroupTheory

end
