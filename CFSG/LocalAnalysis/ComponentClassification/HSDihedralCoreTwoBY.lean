module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBBig
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreFix

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A}

structure TwoBY (φ : Δ.Fusion) where
  Y : Subgroup X
  le_T : Y ≤ φ.T
  normal : ∀ g ∈ (φ.T : Subgroup X), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y
  elem : ElemAbelianTwo Y
  card : Nat.card Y = 8
  t_mem : Δ.t ∈ Y
  dz_mem : Δ.dz ∈ Y
  le_S : Y ≤ Δ.S

variable {k : A} (h2 : Δ.CaseTwo k) (φ : Δ.Fusion)

include h2 in
theorem TwoB_t_mem_Y (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) {Y : Subgroup X}
    (hYT : Y ≤ φ.T) (hYn : ∀ g ∈ (φ.T : Subgroup X), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hYel : ElemAbelianTwo Y) (hY8 : Nat.card Y = 8) (htzY : Δ.t * Δ.dz ∈ Y) : Δ.t ∈ Y := by
  classical
  have h8 := h2.2.2.2.2.1
  have hYS_n : ∀ s ∈ Δ.S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := fun s hs y hy => hYn s (φ.le hs) y hy
  by_contra htY
  have hC := four_le_card_fix hYel hY8 (fun y hy => hYn _ (φ.le Δ.t_mem) y hy) Δ.t_sq
  by_cases hYD : ∃ u ∈ Y, u ∈ Δ.D ∧ u ≠ 1
  · obtain ⟨u, huY, huD, hu1⟩ := hYD
    have hz : Δ.dz ∈ Y ⊓ Δ.D := by
      refine Δ.dz_mem_of_normal h8 inf_le_right (fun h => hu1 ?_) fun d hd n hn => ?_
      · have : u ∈ Y ⊓ Δ.D := mem_inf.mpr ⟨huY, huD⟩
        rw [h] at this
        exact mem_bot.mp this
      · exact mem_inf.mpr ⟨hYS_n d (Δ.D_le hd) n (mem_inf.mp hn).1,
          Δ.conj_mem_D d (Δ.D_le hd) n (mem_inf.mp hn).2⟩
    apply htY
    have := mul_mem htzY (mem_inf.mp hz).1
    rwa [mul_assoc, ← pow_two, Δ.dz_sq, mul_one] at this
  · push Not at hYD
    obtain ⟨y, hyC, hy1, hytz⟩ : ∃ y ∈ Y ⊓ centralizer ({Δ.t} : Set X), y ≠ 1 ∧
        y ≠ Δ.t * Δ.dz := by
      by_contra hno
      push Not at hno
      have := card_le_of_forall_mem_finset (Y ⊓ centralizer ({Δ.t} : Set X))
        {1, Δ.t * Δ.dz} fun y hy => by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases h1 : y = 1
          · exact Or.inl h1
          · exact Or.inr (hno y hy h1)
      have := this.trans Finset.card_le_two
      omega
    obtain ⟨hyY, hyCt⟩ := mem_inf.mp hyC
    have hyS : y ∈ Δ.S := Δ.mem_S_of_commute_t φ.isPGroup φ.le (hYT hyY)
      (mem_centralizer_singleton_iff.mp hyCt)
    have hy2 := hYel.sq_eq_one y hyY
    have hyD : ∀ d ∈ Δ.D, y * d = d * y := by
      intro d hd
      have hcY : y * d * y⁻¹ * d⁻¹ ∈ Y := by
        have := mul_mem hyY (hYS_n d (Δ.D_le hd) _ (inv_mem hyY))
        simpa [mul_assoc] using this
      have hcD : y * d * y⁻¹ * d⁻¹ ∈ Δ.D := mul_mem (Δ.conj_mem_D y hyS d hd) (inv_mem hd)
      have h1 := hYD _ hcY hcD
      calc y * d = (y * d * y⁻¹ * d⁻¹) * (d * y) := by group
        _ = d * y := by rw [h1, one_mul]
    rcases h2.2.2.2.2.2 _ (Δ.ψe_mem_R hyS) (Δ.commute_Dbar hyS hyD) with h | h
    · obtain ⟨q, hq, hyq | hyq⟩ := Δ.mem_Qz_of_centralizes h8 hyS hyD h
      · apply htY
        have := Δ.eq_t_of_mem_Q hq (hyq ▸ hy2) (hyq ▸ hy1)
        rw [← this, ← hyq]
        exact hyY
      · have hq2 : q ^ 2 = 1 := by
          rw [hyq, (show Commute q Δ.dz from Δ.commute_of_mem_Q_D hq Δ.dz_mem).mul_pow,
            Δ.dz_sq, mul_one] at hy2
          exact hy2
        by_cases hq1 : q = 1
        · apply hy1
          exact hYD y hyY (by rw [hyq, hq1, one_mul]; exact Δ.dz_mem)
        · exact hytz (by rw [hyq, Δ.eq_t_of_mem_Q hq hq2 hq1])
    · refine TwoB_false_of_comm_field h2 φ hD1 hyS hyD (fun q hq => ?_) h
      have hcY : y * q * y⁻¹ * q⁻¹ ∈ Y := by
        have := mul_mem hyY (hYS_n q (Δ.Q_le hq) _ (inv_mem hyY))
        simpa [mul_assoc] using this
      have hcQ : y * q * y⁻¹ * q⁻¹ ∈ Δ.Q := mul_mem (Δ.conj_mem_Q hyS hq) (inv_mem hq)
      by_cases hc1 : y * q * y⁻¹ * q⁻¹ = 1
      · calc y * q = (y * q * y⁻¹ * q⁻¹) * (q * y) := by group
          _ = q * y := by rw [hc1, one_mul]
      · exact absurd (Δ.eq_t_of_mem_Q hcQ (hYel.sq_eq_one _ hcY) hc1 ▸ hcY) htY

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
