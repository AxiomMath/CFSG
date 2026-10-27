module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup
open scoped commutatorElement

theorem commutator_eq_bot_of_normal_pPrime_of_quasisimple {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (Q : Subgroup G) [Q.Normal] (hQ : CFSG.IsQuasisimple ↥Q)
    (hpQ : p ∣ Nat.card Q) (K : Subgroup G) [K.Normal] (hK : Nat.Coprime p (Nat.card K)) :
    ⁅K, Q⁆ = ⊥ := by
  obtain ⟨hperf, hsimp, -⟩ := hQ
  haveI := hsimp
  set N : Subgroup ↥Q := (K ⊓ Q).subgroupOf Q with hN
  haveI hNn : N.Normal := Subgroup.Normal.subgroupOf inferInstance Q
  have hNZ : N ≤ Subgroup.center ↥Q := by
    haveI hbar : (N.map (QuotientGroup.mk' (Subgroup.center ↥Q))).Normal :=
      Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (Subgroup.center ↥Q))) with h0 | htop
    · intro n hn
      have : QuotientGroup.mk' (Subgroup.center ↥Q) n ∈
          N.map (QuotientGroup.mk' (Subgroup.center ↥Q)) := ⟨n, hn, rfl⟩
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exfalso
      have hcomm : ∀ x y : ↥Q, ⁅x, y⁆ ∈ N := by
        intro x y
        have hx : QuotientGroup.mk' (Subgroup.center ↥Q) x ∈
            N.map (QuotientGroup.mk' (Subgroup.center ↥Q)) := by rw [htop]; trivial
        obtain ⟨n, hn, hnx⟩ := hx
        have hz : n⁻¹ * x ∈ Subgroup.center ↥Q := by
          have := QuotientGroup.eq.1 hnx
          simpa using this
        have hxn : x = n * (n⁻¹ * x) := by group
        set z := n⁻¹ * x with hzdef
        have hzy : z * y * z⁻¹ = y := by
          have := Subgroup.mem_center_iff.1 hz y
          rw [← this]
          group
        have h1 : ⁅x, y⁆ = ⁅n, y⁆ := by
          rw [hxn, commutatorElement_def, commutatorElement_def]
          calc n * z * y * (n * z)⁻¹ * y⁻¹ = n * (z * y * z⁻¹) * n⁻¹ * y⁻¹ := by group
            _ = n * y * n⁻¹ * y⁻¹ := by rw [hzy]
        rw [h1, commutatorElement_def]
        have : n * (y * n⁻¹ * y⁻¹) = n * y * n⁻¹ * y⁻¹ := by group
        rw [← this]
        exact N.mul_mem hn (hNn.conj_mem _ (N.inv_mem hn) y)
      have hNtop : N = ⊤ := by
        rw [eq_top_iff]
        have h1 : (⊤ : Subgroup ↥Q) = ⁅(⊤ : Subgroup ↥Q), ⊤⁆ := by
          rw [← _root_.commutator_def]
          exact (Group.isPerfect_def.1 hperf).symm
        rw [h1, Subgroup.commutator_le]
        intro x _ y _
        exact hcomm x y
      have hQK : Q ≤ K := by
        intro q hq
        have : (⟨q, hq⟩ : ↥Q) ∈ N := by rw [hNtop]; trivial
        exact (Subgroup.mem_subgroupOf.1 this).1
      have hdvd : p ∣ Nat.card K := hpQ.trans (Subgroup.card_dvd_of_le hQK)
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hK hdvd)
  have hKQ : ⁅K, Q⁆ ≤ (Subgroup.center ↥Q).map Q.subtype := by
    rw [Subgroup.commutator_le]
    intro k hk q hq
    have h1 : ⁅k, q⁆ ∈ K := by
      have : ⁅k, q⁆ = k * (q * k⁻¹ * q⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact K.mul_mem hk ((‹K.Normal›).conj_mem _ (K.inv_mem hk) q)
    have h2 : ⁅k, q⁆ ∈ Q := by
      have : ⁅k, q⁆ = (k * q * k⁻¹) * q⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Q.mul_mem ((‹Q.Normal›).conj_mem _ hq k) (Q.inv_mem hq)
    have h3 : (⟨⁅k, q⁆, h2⟩ : ↥Q) ∈ N := Subgroup.mem_subgroupOf.2 ⟨h1, h2⟩
    exact ⟨_, hNZ h3, rfl⟩
  have hcent1 : ⁅⁅K, Q⁆, Q⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx q hq
    obtain ⟨z, hz, rfl⟩ := hKQ hx
    have hc : (⟨q, hq⟩ : ↥Q) * z = z * ⟨q, hq⟩ := Subgroup.mem_center_iff.1 hz ⟨q, hq⟩
    have hc' : q * (z : G) = (z : G) * q := congrArg Subtype.val hc
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc (z : G) * q * (z : G)⁻¹ * q⁻¹ = (q * (z : G)) * (z : G)⁻¹ * q⁻¹ := by rw [← hc']
      _ = 1 := by group
  have hcent2 : ⁅⁅Q, K⁆, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Q K]
    exact hcent1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Q) (H₂ := Q) (H₃ := K)
    hcent2 hcent1
  rw [Subgroup.isPerfect_iff.1 hperf] at h3
  rw [Subgroup.commutator_comm]
  exact h3

theorem oddPCoreInClosure_of_quasisimple_normal {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (Q : Subgroup G) [Q.Normal] (hQ : CFSG.IsQuasisimple ↥Q)
    (hcent : Odd (Nat.card ↥(Subgroup.centralizer (Q : Set G))))
    (hdvd : p ∣ Nat.card G → p ∣ Nat.card Q) : OddPCoreInClosure p G := by
  by_cases hG : p ∣ Nat.card G
  · intro K hK _ hKcop
    have hcomm : ⁅K, Q⁆ = ⊥ :=
      commutator_eq_bot_of_normal_pPrime_of_quasisimple hp Q hQ (hdvd hG) K hKcop
    have hle : K ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact hcent.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  · exact OddPCoreInClosure.of_not_dvd hp hG

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
