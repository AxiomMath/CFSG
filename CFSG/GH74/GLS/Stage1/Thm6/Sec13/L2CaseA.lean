module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2U

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem card_H [Finite G] : Nat.card H = 32 := by
  rw [c.c2.c3.card_H, c.c2.P_card]

theorem card_Hs_cases [Finite G] :
    (Nat.card T = 8 ∧ H ⊔ T = H) ∨ (Nat.card T = 16 ∧ Nat.card ↥(H ⊔ T) = 64) := by
  have hle := c.card_Hs_le
  rcases c.T_card_cases with h8 | h16
  · left
    refine ⟨h8, ?_⟩
    have := Subgroup.eq_of_le_of_card_ge (le_sup_left : H ≤ H ⊔ T) (by have := c.card_H; omega)
    exact this.symm
  · right
    refine ⟨h16, ?_⟩
    have hTH : ¬ T ≤ H := by
      intro h
      have : T ≤ EV x V := by
        rw [← c.c2.c3.hp.T_inter]
        exact le_inf le_rfl h
      have := Subgroup.card_le_of_le this
      rw [c.c2.c3.out.card_EV] at this
      omega
    obtain ⟨t, htT, htH⟩ := IsConcreteLE.not_le_iff_exists.1 hTH
    have hne : H.relIndex (H ⊔ T) ≠ 1 := by
      intro h1
      rw [relIndex_eq_one] at h1
      exact htH (h1 (Subgroup.mem_sup_right htT))
    have hrel := c.c2.c3.relIndex_le_two
    have h2 : H.relIndex (H ⊔ T) = 2 := by
      have : 0 < H.relIndex (H ⊔ T) := Nat.pos_of_ne_zero (by
        intro h0
        have := relIndex_mul_card H (H ⊔ T)
        rw [h0] at this
        have : 0 < Nat.card ↥(H ⊔ T) := Nat.card_pos
        omega)
      omega
    have := relIndex_mul_card H (H ⊔ T)
    rw [inf_of_le_left le_sup_left, h2, c.card_H] at this
    omega

end Ctx2S

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem false_of_cyclic [Finite G] (h15 : IG_15_15) (hSeq : S = H ⊔ T) {g : G} (hg : g ∈ H ⊔ T)
    (hcyc : ∀ s ∈ H ⊔ T, ∃ k : ℤ, (g ^ k)⁻¹ * s ∈ Hzero H f) : False := by
  have hP := c.c2.c3
  have hn := c.normIn_Hs
  have := hn.normal
  have hS : Sylow2In (H ⊔ T) ⊤ := hSeq ▸ c.syl
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left hP.x_mem_H
  let gb : ↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T) := qm (H ⊔ T) (Hzero H f) ⟨g, hg⟩
  have hcycR : IsCyclic (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨gb, ?_⟩
    rw [eq_top_iff]
    intro r _
    obtain ⟨⟨s, hs⟩, rfl⟩ := (QuotientGroup.mk'_surjective _) r
    obtain ⟨k, hk⟩ := hcyc s hs
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : qm (H ⊔ T) (Hzero H f) ⟨g ^ k, zpow_mem hg k⟩ = qm (H ⊔ T) (Hzero H f) ⟨s, hs⟩ :=
      qm_eq_iff.2 hk
    rw [← h1]
    show gb ^ k = _
    rw [← map_zpow]
    rfl
  have hsplit : H ⊔ T = Hzero H f ⊔ zpowers g := by
    apply le_antisymm
    · intro s hs
      obtain ⟨k, hk⟩ := hcyc s hs
      have : s = g ^ k * ((g ^ k)⁻¹ * s) := by group
      rw [this]
      exact (Hzero H f ⊔ zpowers g).mul_mem (Subgroup.mem_sup_right (zpow_mem_zpowers g k))
        (Subgroup.mem_sup_left hk)
    · exact sup_le hn.le ((zpowers_le).2 hg)
  have hxb2 : qm (H ⊔ T) (Hzero H f) ⟨x, hxS⟩ * qm (H ⊔ T) (Hzero H f) ⟨x, hxS⟩ = 1 := by
    rw [← map_mul]
    apply qm_eq_one.2
    show x * x ∈ Hzero H f
    rw [hP.x_sq]; exact one_mem _
  have hxb1 : qm (H ⊔ T) (Hzero H f) ⟨x, hxS⟩ ≠ 1 := fun h => hP.x_notin_H0 (qm_eq_one.1 h)
  have hc : ∀ p ∈ H ⊔ T, p * p = 1 → p ∈ Hzero H f ∨ ∃ q ∈ Hzero H f, p = q * x := by
    intro p hp hpp
    have hpb2 : qm (H ⊔ T) (Hzero H f) ⟨p, hp⟩ * qm (H ⊔ T) (Hzero H f) ⟨p, hp⟩ = 1 := by
      rw [← map_mul]
      apply qm_eq_one.2
      show p * p ∈ Hzero H f
      rw [hpp]; exact one_mem _
    by_cases hpb : qm (H ⊔ T) (Hzero H f) ⟨p, hp⟩ = 1
    · left; exact qm_eq_one.1 hpb
    · right
      have heq := cyclic_unique_invol hpb2 hxb2 hpb hxb1
      have hu : p⁻¹ * x ∈ Hzero H f := qm_eq_iff.1 heq
      refine ⟨x * (p⁻¹ * x)⁻¹ * x⁻¹, ?_, by group⟩
      exact hP.H0_norm_H x hP.x_mem_H _ ((Hzero H f).inv_mem hu)
  obtain ⟨w, hw1, -⟩ := transfer_cyclic h15 hP.out.simple hP.out.nonabelian hS hn.le c.hPT hxS
    hP.x_notin_H0 hP.x_sq hg hsplit hc
  exact c.c2.not_fused w hw1

end Ctx2S

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem caseA_struct [Finite G] (h15 : IG_15_15) (hSeq : S = H ⊔ T) :
    Nat.card T = 16 ∧ Nat.card ↥(H ⊔ T) = 64 ∧ ∀ s ∈ H ⊔ T, s * s ∈ Hzero H f := by
  have hP := c.c2.c3
  have hn := c.normIn_Hs
  have := hn.normal
  rcases c.card_Hs_cases with ⟨h8, hHs⟩ | ⟨h16, h64⟩
  · exfalso
    refine c.false_of_cyclic h15 hSeq (g := x) (Subgroup.mem_sup_left hP.x_mem_H) ?_
    intro s hs
    rw [hHs] at hs
    obtain ⟨q, hq, h | h⟩ := hP.mem_H_iff.1 hs
    · refine ⟨0, ?_⟩
      rw [zpow_zero, inv_one, one_mul, h]
      exact hq
    · refine ⟨1, ?_⟩
      rw [zpow_one, h]
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hP.x_sq
      have e : x⁻¹ * (q * x) = x * q * x⁻¹ := by rw [hxi]; group
      rw [e]
      exact hP.H0_norm_H x hP.x_mem_H q hq
  · refine ⟨h16, h64, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg, hgg⟩ := hcon
    apply c.false_of_cyclic h15 hSeq hg
    have hRcard : Nat.card (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) = 4 := by
      have := card_QR (M := H ⊔ T) (N := Hzero H f) hn.le
      rw [c.c2.P_card, h64] at this
      omega
    let gb : ↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T) := qm (H ⊔ T) (Hzero H f) ⟨g, hg⟩
    have hgb2 : gb * gb ≠ 1 := by
      intro h
      apply hgg
      rw [← map_mul] at h
      exact qm_eq_one.1 h
    have hord : orderOf gb = 4 := by
      have hd : orderOf gb ∣ 4 := by
        have := orderOf_dvd_natCard gb
        rwa [hRcard] at this
      have h1 : orderOf gb ≠ 1 := by
        intro h
        apply hgb2
        rw [orderOf_eq_one_iff.1 h]; simp
      have h2 : orderOf gb ≠ 2 := by
        intro h
        apply hgb2
        have : gb ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one gb
        rwa [pow_two] at this
      have : orderOf gb ∣ 2 ^ 2 := by simpa using hd
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 this with ⟨i, hi, hi'⟩
      interval_cases i
      · rw [pow_zero] at hi'; exact absurd hi' h1
      · rw [pow_one] at hi'; exact absurd hi' h2
      · simpa using hi'
    have htop : zpowers gb = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord, hRcard]
    intro s hs
    have hr : qm (H ⊔ T) (Hzero H f) ⟨s, hs⟩ ∈ zpowers gb := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hr
    have h1 : qm (H ⊔ T) (Hzero H f) ⟨g ^ k, zpow_mem hg k⟩ = qm (H ⊔ T) (Hzero H f) ⟨s, hs⟩ := by
      rw [← hk]
      show _ = gb ^ k
      rw [← map_zpow]
      rfl
    exact ⟨k, qm_eq_iff.1 h1⟩

end Ctx2S

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
