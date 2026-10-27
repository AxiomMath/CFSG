module

public import CFSG.CGT.PushingUpLit.LIT.A4.SECBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingDefs

public section

namespace CFSG.CGT.PushingUpLit.SEC

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.CGT.PushingUpLit.A4
open CFSG.ComponentClassification.AschbacherStrongEmbedding
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem fusionStronglyEmbedded_of_subgroupOf_top' {X : Type*} [Group X] [Finite X]
    {H : Subgroup X} (h : fusionStronglyEmbedded (H.subgroupOf (⊤ : Subgroup X))) :
    fusionStronglyEmbedded H := by
  have hmap := h.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
  have himage : (H.subgroupOf (⊤ : Subgroup X)).map
      (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom = H := by
    change (H.subgroupOf (⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype = H
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
  rwa [himage] at hmap

theorem eq_one_of_noTwoQuotient_of_split {L : Type*} [Group L] [Finite L]
    (hL : NoTwoQuotient L) {u : L} (hu : u ^ 2 = 1)
    (hint : Subgroup.zpowers (QuotientGroup.mk' (CFSG.oddCore L) u) ⊓
      commutator (L ⧸ CFSG.oddCore L) = ⊥)
    (hsup : Subgroup.zpowers (QuotientGroup.mk' (CFSG.oddCore L) u) ⊔
      commutator (L ⧸ CFSG.oddCore L) = ⊤) : u = 1 := by
  set q := QuotientGroup.mk' (CFSG.oddCore L) with hq
  set C := commutator (L ⧸ CFSG.oddCore L) with hC
  let N : Subgroup L := C.comap q
  have hNn : N.Normal := Subgroup.normal_comap q
  have hqu : (q u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  have hsq : ∀ a : L, a ^ 2 ∈ N := by
    intro a
    have ha : q a ∈ Subgroup.zpowers (q u) ⊔ C := by rw [hsup]; exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at ha
    obtain ⟨y, hy, c, hc, hyc⟩ := ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hy2 : ((q u) ^ k) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hqu, one_zpow]
    show q (a ^ 2) ∈ C
    rw [map_pow, ← hyc]
    have h1 : (q u ^ k * c) ^ 2 = ((q u ^ k)⁻¹ * c * (q u ^ k)) * c := by
      calc (q u ^ k * c) ^ 2 = (q u ^ k * c) * (q u ^ k * c) := sq _
        _ = ((q u ^ k) ^ 2) * (((q u ^ k)⁻¹ * c * (q u ^ k)) * c) := by group
        _ = ((q u ^ k)⁻¹ * c * (q u ^ k)) * c := by rw [hy2, one_mul]
    rw [h1]
    refine C.mul_mem ?_ hc
    have := (inferInstance : C.Normal).conj_mem c hc (q u ^ k)⁻¹
    simpa using this
  have hP : IsPGroup 2 (L ⧸ N) := isPGroup_quotient_of_sq_mem N hsq
  have hNtop : N = ⊤ := hL N hP
  have huN : u ∈ N := hNtop ▸ Subgroup.mem_top u
  have hq1 : q u = 1 := by
    have h2 : q u ∈ Subgroup.zpowers (q u) ⊓ C := ⟨Subgroup.mem_zpowers _, huN⟩
    rw [hint] at h2
    exact Subgroup.mem_bot.mp h2
  have huO : u ∈ CFSG.oddCore L := (QuotientGroup.eq_one_iff u).mp hq1
  have hodd : Odd (Nat.card (CFSG.oddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have hdvd : orderOf u ∣ Nat.card (CFSG.oddCore L) := by
    have := orderOf_dvd_natCard (⟨u, huO⟩ : CFSG.oddCore L)
    rwa [Subgroup.orderOf_mk] at this
  have hdvd2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h1 ▸ hdvd) hodd.not_two_dvd_nat

theorem fusionStronglyEmbedded_of_pointHullStrongSplit {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} {z : G} (hz : orderOf z = 2) (hM : M ≠ ⊤)
    (huniq : ∀ g : G, z ∈ rightConjugate M g ↔ g ∈ M)
    (hO : NoTwoQuotient ↥(involutionPointHull z)) (h3 : PointHullStrongSplit M z) :
    fusionStronglyEmbedded (M.subgroupOf (involutionPointHull z)) := by
  have hLn : (involutionPointHull z).Normal := minimalLocalFailure_hull_normal z
  have hzL : z ∈ involutionPointHull z := Subgroup.subset_closure (distinguished_mem_pointClass z)
  rcases h3 with hrank | ⟨u, hu2, -, hint, hsup, hse, hclass⟩
  ·
    have hzo : orderOf (⟨z, hzL⟩ : involutionPointHull z) = 2 :=
      (Subgroup.orderOf_mk z hzL).trans hz
    have hzK : (⟨z, hzL⟩ : involutionPointHull z) ∈ M.subgroupOf (involutionPointHull z) :=
      Subgroup.mem_subgroupOf.mpr (mem_of_unique huniq)
    refine ⟨?_, ?_, ?_⟩
    · intro htop
      apply hM
      refine eq_top_iff.mpr fun g _ => (conj_mem_iff huniq g).mp ?_
      have hgL : g⁻¹ * z * g ∈ involutionPointHull z :=
        Subgroup.subset_closure (class_conj_mem (distinguished_mem_pointClass z) g)
      have hmem : (⟨g⁻¹ * z * g, hgL⟩ : involutionPointHull z) ∈
          M.subgroupOf (involutionPointHull z) := htop ▸ Subgroup.mem_top _
      exact hmem
    · have hord : orderOf (⟨⟨z, hzL⟩, hzK⟩ : ↥(M.subgroupOf (involutionPointHull z))) = 2 :=
        (Subgroup.orderOf_mk _ hzK).trans hzo
      exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)
    · intro g hg
      by_contra hnodd
      have hev := Nat.not_odd_iff_even.mp hnodd
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥((M.subgroupOf (involutionPointHull z)) ⊓
          (M.subgroupOf (involutionPointHull z)).map (MulAut.conj g⁻¹).toMonoidHom)) 2
        (even_iff_two_dvd.mp hev)
      have hso : orderOf ((s : involutionPointHull z)) = 2 := (Subgroup.orderOf_coe s).trans hs
      obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_twoRank_le_one hrank hzo hso)
      obtain ⟨k, hk, hks⟩ := s.2.2
      have hsM : ((s : involutionPointHull z) : G) ∈ M := s.2.1
      have hkM : ((k : involutionPointHull z) : G) ∈ M := hk
      have hks' : (g : G)⁻¹ * (k : G) * (g : G) = ((s : involutionPointHull z) : G) := by
        have := congrArg (fun x : involutionPointHull z => (x : G)) hks
        simpa [MulAut.conj_apply] using this
      have hcs : (c : G) * z * (c : G)⁻¹ = ((s : involutionPointHull z) : G) := by
        have := congrArg (fun x : involutionPointHull z => (x : G)) hc
        simpa using this
      have hc1 : (c : G)⁻¹ ∈ M := by
        refine (conj_mem_iff huniq (c : G)⁻¹).mp ?_
        simpa [hcs] using hsM
      have hgc : ((c : G)⁻¹ * (g : G)⁻¹) ∈ M := by
        refine (conj_mem_iff huniq ((c : G)⁻¹ * (g : G)⁻¹)).mp ?_
        have hk' : (k : G) = (g : G) * ((s : involutionPointHull z) : G) * (g : G)⁻¹ := by
          rw [← hks']; group
        have : (g : G) * ((c : G) * z * (c : G)⁻¹) * (g : G)⁻¹ ∈ M := by
          rw [hcs, ← hk']; exact hkM
        simpa [mul_assoc] using this
      have hgM : (g : G) ∈ M := by
        have h1 : (g : G)⁻¹ ∈ M := by
          have := M.mul_mem (M.inv_mem hc1) hgc
          simpa using this
        simpa using M.inv_mem h1
      exact hg (Subgroup.mem_subgroupOf.mpr hgM)
  ·
    have hu1 : u = 1 := eq_one_of_noTwoQuotient_of_split hO hu2 hint hsup
    have hmem : ∀ t ∈ involutionPointClass z,
        t ∈ ⁅involutionPointHull z, involutionPointHull z⁆ := by
      intro t ht
      simpa [hu1] using hclass t ht
    have hle : involutionPointHull z ≤ ⁅involutionPointHull z, involutionPointHull z⁆ :=
      (Subgroup.closure_le _).mpr hmem
    have hle' : ⁅involutionPointHull z, involutionPointHull z⁆ ≤ involutionPointHull z :=
      Subgroup.commutator_le_right _ _
    have heq : ⁅involutionPointHull z, involutionPointHull z⁆ = involutionPointHull z :=
      le_antisymm hle' hle
    rw [heq] at hse
    exact hse

end CFSG.CGT.PushingUpLit.SEC
