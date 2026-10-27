module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem mem_V_of_comm_T (ha : Ctx4P t L S x₁ x₂ lam rho tau) {b : G}
    (hbQ : b ∈ ctxQ t tau x₁ x₂ rho) (ht : b * t = t * b) (htau : b * tau = tau * b) :
    b ∈ fourGrp x₁ x₂ := by
  have hc := ha.toCtx4L.toCtx4Q
  have hcent : ∀ e ∈ closure ({t, tau} : Set G), e * b = b * e := by
    intro e he
    rcases (mem_T_iff hc).mp he with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact ht.symm
    · exact htau.symm
    · calc (t * tau) * b = t * (tau * b) := mul_assoc t tau b
        _ = t * (b * tau) := by rw [← htau]
        _ = (t * b) * tau := (mul_assoc t b tau).symm
        _ = (b * t) * tau := by rw [← ht]
        _ = b * (t * tau) := mul_assoc b t tau
  have hmem : b ∈ ctxQ t tau x₁ x₂ rho ⊓
      centralizer ((closure {t, tau} : Subgroup G) : Set G) :=
    ⟨hbQ, Subgroup.mem_centralizer_iff.mpr hcent⟩
  rw [ha.CQ_t_tau] at hmem
  exact hmem

theorem B_eq_CQ (ha : Ctx4P t L S x₁ x₂ lam rho tau) {B : Subgroup G} {ω : G}
    (hB : BData t x₁ x₂ lam rho tau B ω) :
    B = ctxQ t tau x₁ x₂ rho ⊓ centralizer ({ω} : Set G) := by
  have hc := ha.toCtx4L.toCtx4Q
  have hle : B ≤ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({ω} : Set G) := fun b hb =>
    ⟨hB.le_Q hb, Subgroup.mem_centralizer_singleton_iff.mpr (hB.ω_comm b hb).symm⟩
  rcases (mem_T_iff hc).mp hB.ω_mem with hω1 | hωt | hωtau | hωtt
  · exact absurd hω1 hB.ω_ne
  · rw [hωt] at hle ⊢
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_CQ_t hc, hB.card]
    norm_num
  · rw [hωtau] at hle ⊢
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_CQ_tau hc, hB.card]
    norm_num
  · rw [hωtt] at hle ⊢
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_CQ_ttau hc, hB.card]
    norm_num

theorem T_cent_cases (ha : Ctx4P t L S x₁ x₂ lam rho tau) {B : Subgroup G} {ω : G}
    (hB : BData t x₁ x₂ lam rho tau B ω) {d : G} (hd : d ∈ closure ({t, tau} : Set G))
    (hdc : ∀ b ∈ B, d * b = b * d) : d = 1 ∨ d = ω := by
  have hc := ha.toCtx4L.toCtx4Q
  have hcardV : Nat.card (fourGrp x₁ x₂) = 4 := card_fourGrp hc
  have key : (∀ b ∈ B, t * b = b * t) → (∀ b ∈ B, tau * b = b * tau) → False := by
    intro ht htau
    have hBleV : B ≤ fourGrp x₁ x₂ := fun b hb =>
      mem_V_of_comm_T ha (hB.le_Q hb) (ht b hb).symm (htau b hb).symm
    have hcard := Subgroup.card_le_of_le hBleV
    rw [hB.card, hcardV] at hcard
    omega
  have hmul : ∀ b ∈ B, (d * ω) * b = b * (d * ω) := fun b hb =>
    Commute.mul_left (hdc b hb) (hB.ω_comm b hb)
  rcases (mem_T_iff hc).mp hd with hd1 | hdt | hdtau | hdtt
  · exact Or.inl hd1
  · rcases (mem_T_iff hc).mp hB.ω_mem with hω1 | hωt | hωtau | hωtt
    · exact absurd hω1 hB.ω_ne
    · exact Or.inr (hdt.trans hωt.symm)
    · exact False.elim (key (fun b hb => by rw [← hdt]; exact hdc b hb)
        (fun b hb => by rw [← hωtau]; exact hB.ω_comm b hb))
    · have htau : ∀ b ∈ B, tau * b = b * tau := by
        intro b hb
        have h := hmul b hb
        rw [hdt, hωtt] at h
        rw [show t * (t * tau) = tau by rw [← mul_assoc, hc.t_mul_self, one_mul]] at h
        exact h
      exact False.elim (key (fun b hb => by rw [← hdt]; exact hdc b hb) htau)
  · rcases (mem_T_iff hc).mp hB.ω_mem with hω1 | hωt | hωtau | hωtt
    · exact absurd hω1 hB.ω_ne
    · exact False.elim (key (fun b hb => by rw [← hωt]; exact hB.ω_comm b hb)
        (fun b hb => by rw [← hdtau]; exact hdc b hb))
    · exact Or.inr (hdtau.trans hωtau.symm)
    · have ht : ∀ b ∈ B, t * b = b * t := by
        intro b hb
        have h := hmul b hb
        rw [hdtau, hωtt] at h
        rw [show tau * (t * tau) = t by
          rw [← mul_assoc, ← hc.t_comm_tau, mul_assoc, hc.tau_mul_self, mul_one]] at h
        exact h
      exact False.elim (key ht (fun b hb => by rw [← hdtau]; exact hdc b hb))
  · rcases (mem_T_iff hc).mp hB.ω_mem with hω1 | hωt | hωtau | hωtt
    · exact absurd hω1 hB.ω_ne
    · have htau : ∀ b ∈ B, tau * b = b * tau := by
        intro b hb
        have h := hmul b hb
        rw [hdtt, hωt] at h
        rw [show (t * tau) * t = tau by
          rw [mul_assoc, ← hc.t_comm_tau, ← mul_assoc, hc.t_mul_self, one_mul]] at h
        exact h
      exact False.elim (key (fun b hb => by rw [← hωt]; exact hB.ω_comm b hb) htau)
    · have ht : ∀ b ∈ B, t * b = b * t := by
        intro b hb
        have h := hmul b hb
        rw [hdtt, hωtau] at h
        rw [show (t * tau) * tau = t by rw [mul_assoc, hc.tau_mul_self, mul_one]] at h
        exact h
      exact False.elim (key ht (fun b hb => by rw [← hωtau]; exact hB.ω_comm b hb))
    · exact Or.inr (hdtt.trans hωtt.symm)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
