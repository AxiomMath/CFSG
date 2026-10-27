module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Frattini
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Conj
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Swap

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem StarLift.starLift_of_mem_right
    (hu : StarLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J)) (T : Sylow 2 (quasiNormalizer u))
    (hTB : (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u))
    (hzT : z ∈ partCSylow T) {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L)
    (hc : PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (partCSylow T))
    (hT : partCSylow T ≤ partCLeft T L ⊔ partCRight T L)
    (φ : partCRight T L ≃* QuaternionGroup 2) {w : J} (hwP : w ∈ partCRight T L)
    (hww : w * w = centralElt J) : partCSylow T ≤ quasiNormalizer w ∧ StarLift B z w := by
  have hZ : ∀ x, x ∈ Subgroup.center J ↔ x = 1 ∨ x = centralElt J := fun _ => h.mem_center_iff
  have hTB' : partCSylow T ≤ B := by
    rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hTB ht)
  have hwT : w ∈ partCSylow T := hc.right_le hwP
  have hTw : partCSylow T ≤ quasiNormalizer w := fun t ht => by
    refine (h.mem_normalizer_zpowers_iff hww).mpr ?_
    rcases hc.conj_eq_or_of_caseB2 _ hT φ hZ ht hwT with h1 | h1 <;> rw [h1]
    · rw [mul_inv_cancel]
      exact (Subgroup.center J).one_mem
    · rw [mul_assoc, (h.commute_centralElt w⁻¹).eq.symm, ← mul_assoc, mul_inv_cancel, one_mul]
      exact h.centralElt_mem_center
  obtain ⟨g, hg, hgB⟩ := hu.exists_mem_quasiNormalizer_not_mem h hz T hL hwP (hTB' hwT) hww
  have hesc : EscapingLift B z w :=
    { mem := hTB' hwT
      sq := hww
      commute := hc.comm_map_of_caseB2 _ hT φ hZ ⟨w, hwT, rfl⟩ ⟨z, hzT, rfl⟩
      escape := h.not_centralizer_le_of_mem_normalizer hww hg hgB }
  have hrankw : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer w) :=
    hrank.trans (CFSG.SectionRank.pRank_mono (by decide) hTw)
  obtain ⟨q₁, hq₁, q₂, hq₂, h11, h22, h21, h21e⟩ :=
    quaternion_exists_pair hc.quaternion.some hc.mem_left hc.order
  have hne1 : ∀ {q : J}, q ∈ partCLeft T L → q * q = centralElt J → q * w ≠ 1 := by
    intro q hq hqq hqw
    have hqP : q ∈ partCRight T L := by
      rw [eq_inv_of_mul_eq_one_left hqw]
      exact (partCRight T L).inv_mem hwP
    have h1 := hc.mul_self_eq_one_of_mem_left_right hq hqP
    rw [hqq] at h1
    exact hc.centralElt_ne_one h1
  have h12 : q₁ * q₂ * (q₁ * q₂) = centralElt J := by
    refine hc.mul_self_of_ne ((partCLeft T L).mul_mem hq₁ hq₂) (fun h1 => h21e ?_)
      (fun he => h21 ?_)
    · rw [← hc.inv_eq_mul_centralElt h11]
      exact eq_inv_of_mul_eq_one_right h1
    · calc q₂ = q₁⁻¹ * (q₁ * q₂) := by group
        _ = q₁ := by rw [he, hc.inv_eq_mul_centralElt h11, hc.mul_centralElt_mul_centralElt]
  exact ⟨hTw, hesc.starLift_of_pair h hz IH hrankw (hc.commute q₁ hq₁ w hwP)
    (hc.commute q₂ hq₂ w hwP) h11 h22 (hne1 hq₁ h11) (hne1 hq₂ h22) h12⟩

theorem MaximalStarLift.caseB2Normalized
    (hu : MaximalStarLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J)) (T : Sylow 2 (quasiNormalizer u))
    (hTB : (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u))
    (hzT : z ∈ partCSylow T) {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L)
    (hc : PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (partCSylow T))
    (hT : partCSylow T ≤ partCLeft T L ⊔ partCRight T L)
    (hφ : Nonempty (partCRight T L ≃* QuaternionGroup 2)) :
    PartC.CaseB2Normalized (partCSylow T) (partCRight T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hφ
  have hZ : ∀ x, x ∈ Subgroup.center J ↔ x = 1 ∨ x = centralElt J := fun _ => h.mem_center_iff
  intro R hR hTR _ hRP
  by_contra hRT
  obtain ⟨r, hrR, hrT⟩ := IsConcreteLE.not_le_iff_exists.mp hRT
  obtain ⟨n, hnR, hnT, hnn⟩ := exists_pow_not_mem_mul_self_mem hR hrR hrT
  obtain ⟨w, hwP, hww, hnw⟩ := hc.exists_conj_eq_of_caseB2 _ hT φ hZ
    (fun p hp => (Subgroup.mem_normalizer_iff.mp (hRP hnR) p).mp hp) hnn
  obtain ⟨hTw, hw⟩ :=
    hu.toStarLift.starLift_of_mem_right h hz IH T hTB hzT hL hc hrank hT φ hwP hww
  have hnw' : n ∈ quasiNormalizer w := by
    refine (h.mem_normalizer_zpowers_iff hww).mpr ?_
    rcases hnw with h1 | h1 <;> rw [h1]
    · rw [mul_inv_cancel]
      exact (Subgroup.center J).one_mem
    · rw [mul_assoc, (h.commute_centralElt w⁻¹).eq.symm, ← mul_assoc, mul_inv_cancel, one_mul]
      exact h.centralElt_mem_center
  set R'' := partCSylow T ⊔ Subgroup.zpowers n with hR''
  have hR''2 : IsPGroup 2 R'' := hR.to_le (_root_.sup_le hTR (Subgroup.zpowers_le.mpr hnR))
  have hR''w : R'' ≤ quasiNormalizer w := _root_.sup_le hTw (Subgroup.zpowers_le.mpr hnw')
  have hlt : partCSylow T < R'' := lt_of_le_of_ne le_sup_left fun h' =>
    hnT (h' ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  have hcardT : Nat.card (partCSylow T) =
      2 ^ (Nat.card (quasiNormalizer u)).factorization 2 := by
    rw [Subgroup.card_map_of_injective (quasiNormalizer u).subtype_injective,
      T.card_eq_multiplicity]
  have hcardR : Nat.card R'' ≤ 2 ^ (Nat.card (quasiNormalizer w)).factorization 2 := by
    obtain ⟨S, hS⟩ := (hR''2.comap_subtype (K := quasiNormalizer w)).exists_le_sylow
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR''w).toEquiv, ← S.card_eq_multiplicity]
    exact Subgroup.card_le_of_le hS
  have hpow := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (hu.maximal w hw)
  have hlt' := Subgroup.card_lt_of_lt hlt
  omega

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
