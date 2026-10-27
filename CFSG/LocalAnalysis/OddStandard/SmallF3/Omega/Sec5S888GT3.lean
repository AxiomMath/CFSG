module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements3
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private theorem s888GT3_odd_card_oddCoreIn [Finite G] (H : Subgroup G) :
    Odd (Nat.card (oddCoreIn H)) := by
  unfold oddCoreIn CFSG.inSubgroup
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.ABGLocalTools.odd_card_oddCore

private theorem s888GT3_pow_mul {Q : Subgroup G} {o : G}
    (ho : o ∈ normalizer (Q : Set G)) {q : G} (hq : q ∈ Q) (m : ℕ) :
    ∃ q' ∈ Q, (q * o) ^ m = q' * o ^ m := by
  induction m with
  | zero => exact ⟨1, Q.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨q', hq', h⟩ := ih
    have hom : o ^ m ∈ normalizer (Q : Set G) := (normalizer (Q : Set G)).pow_mem ho m
    have hc : o ^ m * q * (o ^ m)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hom q).mp hq
    refine ⟨q' * (o ^ m * q * (o ^ m)⁻¹), Q.mul_mem hq' hc, ?_⟩
    rw [pow_succ, h]
    group

theorem centS_of_516a (h516a : Asc82Lemma516a) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {T : Subgroup G}
    (hTN : IsSylow2Of T (normalizer (Qsub K₁ K₂ h : Set G)))
    (hNz : normalizer (Qsub K₁ K₂ h : Set G) ≤ centralizer ({z} : Set G)) :
    ∀ s ∈ T, (∀ q ∈ Qsub K₁ K₂ h, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Qsub K₁ K₂ h := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hsT hscomm
  have hQO : Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)) =
      centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) :=
    h516a G t L S z r B A K₁ K₂ h c
  have hsmod : s ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G))
      (Qsub K₁ K₂ h) :=
    ⟨hTN.1 hsT, hNz (hTN.1 hsT), hTN.1 hsT, hscomm⟩
  have hssup : s ∈ Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)) := by
    rw [hQO]
    exact hsmod
  have hO_le : oddCoreIn (centralizer ({t} : Set G)) ≤
      normalizer (Qsub K₁ K₂ h : Set G) := by
    intro o ho
    have hmem : o ∈ Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)) :=
      Subgroup.mem_sup_right ho
    rw [hQO] at hmem
    exact hmem.2.2.1
  have hnorm : ((Qsub K₁ K₂ h).subgroupOf
      (Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)))).Normal := by
    have h1 := Subgroup.normal_subgroupOf_sup_of_le_normalizer
      (H := oddCoreIn (centralizer ({t} : Set G))) (N := Qsub K₁ K₂ h) hO_le
    rw [sup_comm] at h1
    exact h1
  haveI : ((Qsub K₁ K₂ h).subgroupOf
      (Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)))).Normal := hnorm
  have hsL : (⟨s, hssup⟩ :
      ↥(Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)))) ∈
      (Qsub K₁ K₂ h).subgroupOf
          (Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G))) ⊔
        (oddCoreIn (centralizer ({t} : Set G))).subgroupOf
          (Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G))) := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left) (le_sup_right), Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨q, hq, o, ho, hqo⟩ := Subgroup.mem_sup_of_normal_left.mp hsL
  have hqG : (q : G) ∈ Qsub K₁ K₂ h := Subgroup.mem_subgroupOf.mp hq
  have hoG : (o : G) ∈ oddCoreIn (centralizer ({t} : Set G)) :=
    Subgroup.mem_subgroupOf.mp ho
  have hqoG : (q : G) * (o : G) = s := congrArg Subtype.val hqo
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf).mp
    (hTN.2.1.to_le (Subgroup.zpowers_le.mpr hsT))
      ⟨s, Subgroup.mem_zpowers s⟩
  have hs2 : orderOf s = 2 ^ n := by
    rw [← hn]
    exact (Subgroup.orderOf_mk s (Subgroup.mem_zpowers s)).symm
  have hko : Odd (orderOf (o : G)) := by
    have h2 : Odd (Nat.card ↥(oddCoreIn (centralizer ({t} : Set G)))) :=
      s888GT3_odd_card_oddCoreIn _
    have h1 : orderOf (⟨(o : G), hoG⟩ :
        ↥(oddCoreIn (centralizer ({t} : Set G)))) ∣
        Nat.card ↥(oddCoreIn (centralizer ({t} : Set G))) :=
      orderOf_dvd_natCard _
    simpa using h2.of_dvd_nat h1
  have hsk : s ^ orderOf (o : G) ∈ Qsub K₁ K₂ h := by
    obtain ⟨q', hq', hpow⟩ :=
      s888GT3_pow_mul (hO_le hoG) hqG (orderOf (o : G))
    rw [← hqoG, hpow, pow_orderOf_eq_one, mul_one]
    exact hq'
  have hcop : Nat.Coprime (orderOf (o : G)) (orderOf s) := by
    rw [hs2]
    exact (Nat.coprime_two_right.mpr hko).pow_right n
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := s) hcop
  rw [← hm]
  exact (Qsub K₁ K₂ h).pow_mem hsk m

end CFSG.OddStandard.SmallF3.Omega
