module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L58A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56H

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem inf_conjugate_Q_eq_bot_of_ne {g : G} (hgT : g ∈ T) (hne : conjugate Q g ≠ Q) :
    Q ⊓ conjugate Q g = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hQ₀
  have hQgT : conjugate Q g ≤ T := fun x hx => by
    have h1 := h.ST (h.QS (mem_conjugate_iff.mp hx))
    rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group]
    exact mul_mem (mul_mem (inv_mem hgT) h1) hgT
  have hQgp : IsPGroup 2 (conjugate Q g) := h.sylT.isPGroup.to_le hQgT
  have hQ₀N : conjugate Q g ⊓ S ≤ normalizer ((Q ⊓ conjugate Q g : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun s hs w hw => mem_inf.mpr
      ⟨h.conj_mem_Q (mem_inf.mp hs).2 (mem_inf.mp hw).1, mul_mem (mul_mem (mem_inf.mp hs).1
        (mem_inf.mp hw).2) (inv_mem (mem_inf.mp hs).1)⟩
  obtain ⟨x₀, hx₀, hx₀2, hx₀Z⟩ := exists_involution_center (hQgp.to_le inf_le_left)
    (le_inf inf_le_right (inf_le_left.trans h.QS)) hQ₀N hQ₀
  have hQup : ∀ y ∈ conjugate Q g ⊓ S, y ∈ Q := by
    intro y hy
    have h1 := h.conj_mem_Q_of_conj_mem_Q (a := g) (v := g * x₀ * g⁻¹) (v' := g * y * g⁻¹)
      (mem_conjugate_iff.mp (mem_inf.mp hx₀).2) (mem_conjugate_iff.mp (mem_inf.mp hy).1)
      (by rw [orderOf_conj', hx₀2])
      (by
        have h2 := hx₀Z y hy
        calc g * x₀ * g⁻¹ * (g * y * g⁻¹) = g * (x₀ * y) * g⁻¹ := by group
          _ = g * (y * x₀) * g⁻¹ := by rw [h2]
          _ = g * y * g⁻¹ * (g * x₀ * g⁻¹) := by group)
      (by rw [show g⁻¹ * (g * x₀ * g⁻¹) * g = x₀ by group]; exact (mem_inf.mp hx₀).1)
      (by rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]; exact (mem_inf.mp hy).2)
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
  have hlt : Q ⊓ conjugate Q g < conjugate Q g := by
    refine lt_of_le_of_ne inf_le_right fun h1 => hne ?_
    refine (eq_of_le_of_card_ge (h1 ▸ inf_le_left : conjugate Q g ≤ Q) ?_)
    rw [card_conjugate_eq_card]
  obtain ⟨y, hyQg, hyQ₀, hyN⟩ := exists_mem_normalizer_not_mem_of_lt hQgp hlt
  have hyS : y ∉ S := fun h1 => hyQ₀ (mem_inf.mpr ⟨hQup y (mem_inf.mpr ⟨hyQg, h1⟩), hyQg⟩)
  have hyT := hQgT hyQg
  have hP : IsPGroup 2 ↥((Q ⊓ conjugate Q g) ⊔ zpowers y) :=
    hQgp.to_le (sup_le inf_le_right (zpowers_le.mpr hyQg))
  have hPN : (Q ⊓ conjugate Q g) ⊔ zpowers y ≤
      normalizer ((Q ⊓ conjugate Q g : Subgroup G) : Set G) :=
    sup_le le_normalizer (zpowers_le.mpr hyN)
  obtain ⟨x, hx, hx2, hxy⟩ := exists_involution_center hP le_sup_left hPN hQ₀
  have hyx : y * x = x * y := hxy y (mem_sup_right (mem_zpowers y))
  have hxQ := (mem_inf.mp hx).1
  have hxQg := (mem_inf.mp hx).2
  have hx22 : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx2; omega
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by have h2 := h.z2; rw [h1, orderOf_one] at h2; omega
  have hxZ : ∃ s ∈ S, s * x ≠ x * s := by
    by_contra hall
    push Not at hall
    exact hyS ((h.repoint hxQ hx2 hall).mem_S_of_commute hyT hyx)
  have hxz : x ≠ z := fun h1 => by
    obtain ⟨s, hs, hsx⟩ := hxZ
    exact hsx (h1 ▸ h.zS s hs)
  have hW : ∀ u ∈ Q, u * u = 1 → u * x = x * u → u = 1 ∨ u = x ∨ u = z ∨ u = x * z :=
    fun u hu hu2 hux => h.mem_W hxQ hx22 hx1 hxz hu hu2 hux
  have hCx : S ⊓ centralizer ({x} : Set G) < S := by
    refine lt_of_le_of_ne inf_le_left fun h1 => ?_
    obtain ⟨s, hs, hsx⟩ := hxZ
    have h2 : s ∈ S ⊓ centralizer ({x} : Set G) := by rw [h1]; exact hs
    exact hsx (mem_centralizer_singleton_iff.mp (mem_inf.mp h2).2)
  obtain ⟨s₀, hs₀S, hs₀C, hs₀N⟩ := exists_mem_normalizer_not_mem_of_lt h.isPGroup_S hCx
  have hs₀z : s₀ * z * s₀⁻¹ = z := by rw [h.zS s₀ hs₀S, mul_inv_cancel_right]
  have hs₀x : s₀ * x * s₀⁻¹ = x * z := by
    have hxmem : x ∈ S ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨h.QS hxQ, mem_centralizer_singleton_iff.mpr rfl⟩
    have h1 := (mem_normalizer_iff.mp hs₀N x).mp hxmem
    have hcx := mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2
    have hsq : s₀ * x * s₀⁻¹ * (s₀ * x * s₀⁻¹) = 1 := by
      rw [show s₀ * x * s₀⁻¹ * (s₀ * x * s₀⁻¹) = s₀ * (x * x) * s₀⁻¹ by group, hx22]
      group
    rcases hW _ (h.conj_mem_Q hs₀S hxQ) hsq hcx with h2 | h2 | h2 | h2
    · exact absurd (by
        calc x = s₀⁻¹ * (s₀ * x * s₀⁻¹) * s₀ := by group
          _ = 1 := by rw [h2]; group) hx1
    · exact absurd (mem_inf.mpr ⟨hs₀S, mem_centralizer_singleton_iff.mpr (by
        calc s₀ * x = s₀ * x * s₀⁻¹ * s₀ := by group
          _ = x * s₀ := by rw [h2])⟩) hs₀C
    · exact absurd (by
        calc x = s₀⁻¹ * (s₀ * x * s₀⁻¹) * s₀ := by group
          _ = s₀⁻¹ * z * s₀ := by rw [h2]
          _ = z := by rw [mul_assoc, ← h.zS s₀ hs₀S, ← mul_assoc, inv_mul_cancel, one_mul]) hxz
    · exact h2
  have hfix := (h.footeF_data hxQ hx2).1
  have hQsQ₁ : Q ⊓ centralizer ({x} : Set G) ≤
      T ⊓ centralizer ({x} : Set G) ⊓ coreActionKernel (footeF L₀ x) := fun e he =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨h.ST (h.QS (mem_inf.mp he).1), (mem_inf.mp he).2⟩,
      h.mem_coreActionKernel_footeF_of_commute hxQ hx2 (mem_inf.mp he).1
        (mem_centralizer_singleton_iff.mp (mem_inf.mp he).2).symm⟩
  have hQ₁S : ∀ e ∈ T ⊓ centralizer ({x} : Set G) ⊓ coreActionKernel (footeF L₀ x), e ∈ S →
      e ∈ Q ⊓ centralizer ({x} : Set G) := fun e he heS =>
    mem_inf.mpr ⟨h.mem_Q_of_mem_coreActionKernel_footeFixed hxQ hx2 heS
      (mem_inf.mp (mem_inf.mp he).1).2 (hfix ▸ (mem_inf.mp he).2),
      (mem_inf.mp (mem_inf.mp he).1).2⟩
  have hyQ₁ : y ∈ T ⊓ centralizer ({x} : Set G) ⊓ coreActionKernel (footeF L₀ x) :=
    mem_inf.mpr ⟨mem_inf.mpr ⟨hyT, mem_centralizer_singleton_iff.mpr hyx⟩,
      h.mem_coreActionKernel_footeF_conjugate hxQg hyQg hx2 hyx.symm⟩
  have hlt' : Q ⊓ centralizer ({x} : Set G) <
      T ⊓ centralizer ({x} : Set G) ⊓ coreActionKernel (footeF L₀ x) := by
    refine lt_of_le_of_ne hQsQ₁ fun h1 => hyS ?_
    have h2 : y ∈ Q ⊓ centralizer ({x} : Set G) := by rw [h1]; exact hyQ₁
    exact h.QS (mem_inf.mp h2).1
  obtain ⟨b, hbQ₁, hbQs, hbN⟩ := exists_mem_normalizer_not_mem_of_lt
    (h.sylT.isPGroup.to_le (inf_le_left.trans inf_le_left)) hlt'
  have hbS : b ∉ S := fun h1 => hbQs (hQ₁S b hbQ₁ h1)
  have hbT := (mem_inf.mp (mem_inf.mp hbQ₁).1).1
  have hbx : b * x = x * b := mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hbQ₁).1).2
  have hbz : b * z * b⁻¹ = x * z := by
    have hzQs : z ∈ Q ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨h.zQ, mem_centralizer_singleton_iff.mpr (h.zS x (h.QS hxQ)).symm⟩
    have h1 := (mem_normalizer_iff.mp hbN z).mp hzQs
    have hsq : b * z * b⁻¹ * (b * z * b⁻¹) = 1 := by
      rw [show b * z * b⁻¹ * (b * z * b⁻¹) = b * (z * z) * b⁻¹ by group, hz22]
      group
    rcases hW _ (mem_inf.mp h1).1 hsq (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2)
      with h2 | h2 | h2 | h2
    · exact absurd (by
        calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
          _ = 1 := by rw [h2]; group) hz1
    · exact absurd (by
        calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
          _ = b⁻¹ * x * b := by rw [h2]
          _ = x := by rw [mul_assoc, ← hbx, ← mul_assoc, inv_mul_cancel, one_mul]) hxz.symm
    · exact absurd (h.mem_S_of_commute hbT (by
        calc b * z = b * z * b⁻¹ * b := by group
          _ = z * b := by rw [h2])) hbS
    · exact h2
  have hxzc : x * z = z * x := h.zS x (h.QS hxQ)
  refine false_of_three_cycle h.sylT.isPGroup (mul_mem (h.ST hs₀S) hbT) ?_ ?_ ?_ hxz hx1
  · rw [show s₀ * b * z * (s₀ * b)⁻¹ = s₀ * (b * z * b⁻¹) * s₀⁻¹ by group, hbz,
      show s₀ * (x * z) * s₀⁻¹ = s₀ * x * s₀⁻¹ * (s₀ * z * s₀⁻¹) by group, hs₀x, hs₀z,
      mul_assoc, hz22, mul_one]
  · rw [show s₀ * b * x * (s₀ * b)⁻¹ = s₀ * (b * x * b⁻¹) * s₀⁻¹ by group,
      show b * x * b⁻¹ = x by rw [hbx, mul_inv_cancel_right], hs₀x]
  · rw [show s₀ * b * (x * z) * (s₀ * b)⁻¹ = s₀ * (b * x * b⁻¹) * s₀⁻¹ *
        (s₀ * (b * z * b⁻¹) * s₀⁻¹) by group,
      show b * x * b⁻¹ = x by rw [hbx, mul_inv_cancel_right], hbz, hs₀x,
      show s₀ * (x * z) * s₀⁻¹ = s₀ * x * s₀⁻¹ * (s₀ * z * s₀⁻¹) by group, hs₀x, hs₀z]
    calc x * z * (x * z * z) = x * (z * x) * (z * z) := by group
      _ = x * (x * z) * 1 := by rw [← hxzc, hz22]
      _ = z := by rw [mul_one, ← mul_assoc, hx22, one_mul]

end Sec5

end CFSG.ComponentClassification.Foote5
