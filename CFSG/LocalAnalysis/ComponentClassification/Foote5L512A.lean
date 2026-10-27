module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511S
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem exists_conj_mul_of_mem_Q {x : G} (hx : x ∈ S ⊓ L) (hx2 : orderOf x = 2) {c : G}
    (hcQ : c ∈ Q) (hc2 : c * c = 1) (hcx : c * x = x * c) :
    ∃ g : G, g * c = c * g ∧ g⁻¹ * x * g = t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε⟩ := h.quotient_simple.2
  obtain ⟨k, hkL, hk⟩ := h.exists_conj_t hx hx2
  have hcS := h.QS hcQ
  have hcN := h.S_le hcS
  have hP : IsPGroup 2 (zpowers c) := isPGroup_zpowers_of_pow_two (k := 1)
    (by rw [pow_one, sq]; exact hc2)
  have hPN : zpowers c ≤ normalizer (L : Set G) := zpowers_le.mpr hcN
  have hc1 : actG L ε c = 1 := (h.actG_eq_one_iff_mem_Q ε hcS).mpr hcQ
  obtain ⟨k₁, hk₁L, hk₁C, hψ⟩ := exists_lift_of_fixed_pgroup ε hP hPN (x := psi L ε ⟨k, hkL⟩)
    fun p hp => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
      rw [actG_zpow ε hcN, hc1, one_zpow, MulAut.one_apply]
  set o := k₁⁻¹ * k with ho
  have hoO : o ∈ oddCoreIn L := by
    have h1 := (psi_eq_iff ε ⟨k₁, hk₁L⟩ ⟨k, hkL⟩).mp hψ
    exact h1
  have hk₁c : k₁ * c = c * k₁ := (mem_centralizer_iff.mp hk₁C c (mem_zpowers c)).symm
  set x' := k₁⁻¹ * x * k₁ with hx'
  have hx'o : x' = o * t * o⁻¹ := by
    rw [hx', ho, ← hk]
    group
  have hx'c : x' * c = c * x' := by
    calc x' * c = k₁⁻¹ * x * (k₁ * c) := by rw [hx']; group
      _ = k₁⁻¹ * x * (c * k₁) := by rw [hk₁c]
      _ = k₁⁻¹ * (x * c) * k₁ := by group
      _ = k₁⁻¹ * (c * x) * k₁ := by rw [hcx]
      _ = (k₁⁻¹ * c) * x * k₁ := by group
      _ = (c * k₁⁻¹) * x * k₁ := by
          rw [show k₁⁻¹ * c = c * k₁⁻¹ by
            calc k₁⁻¹ * c = k₁⁻¹ * (c * k₁) * k₁⁻¹ := by group
              _ = k₁⁻¹ * (k₁ * c) * k₁⁻¹ := by rw [hk₁c]
              _ = c * k₁⁻¹ := by group]
      _ = c * x' := by rw [hx']; group
  have htc : t * c = c * t := (h.commute_Q_R hcQ h.tR).symm
  set N := oddCoreIn L ⊓ centralizer ({t} : Set G) with hN
  have hNodd : ¬ 2 ∣ Nat.card N := fun h2 => by
    have h3 := Subgroup.card_dvd_of_le (inf_le_left : N ≤ oddCoreIn L)
    have h4 := Nat.odd_iff.mp (odd_card_oddCoreIn L)
    have h5 := dvd_trans h2 h3
    omega
  have hcpow : ∀ p ∈ zpowers c, p * c = c * p := fun p hp => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
    exact (Commute.zpow_left (Commute.refl c) i).eq
  have hpt : ∀ p ∈ zpowers c, p * t * p⁻¹ = t := fun p hp => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
    rw [(Commute.zpow_left (show Commute c t from htc.symm) i).eq, mul_inv_cancel_right]
  have hpx' : ∀ p ∈ zpowers c, p * x' * p⁻¹ = x' := fun p hp => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
    rw [(Commute.zpow_left (show Commute c x' from hx'c.symm) i).eq, mul_inv_cancel_right]
  have hNn : ∀ p ∈ zpowers c, ∀ n ∈ N, p * n * p⁻¹ ∈ N := fun p hp n hn =>
    mem_inf.mpr ⟨conj_mem_oddCoreIn ε (hPN hp) (mem_inf.mp hn).1,
      mem_centralizer_singleton_iff.mpr (by
        have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hn).2
        calc p * n * p⁻¹ * t = p * n * (p⁻¹ * t * p) * p⁻¹ := by group
          _ = p * n * t * p⁻¹ := by
              rw [show p⁻¹ * t * p = t by
                have h2 := hpt p⁻¹ (inv_mem hp)
                rwa [inv_inv] at h2]
          _ = p * (t * n) * p⁻¹ := by rw [mul_assoc p, h1]
          _ = t * (p * n * p⁻¹) := by
              rw [show p * (t * n) * p⁻¹ = (p * t * p⁻¹) * (p * n * p⁻¹) by group, hpt p hp])⟩
  have hy : ∀ p ∈ zpowers c, o⁻¹ * (p * o * p⁻¹) ∈ N := by
    intro p hp
    refine mem_inf.mpr ⟨mul_mem (inv_mem hoO) (conj_mem_oddCoreIn ε (hPN hp) hoO),
      mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : (p * o * p⁻¹) * t * (p * o * p⁻¹)⁻¹ = x' := by
      calc (p * o * p⁻¹) * t * (p * o * p⁻¹)⁻¹ = p * (o * (p⁻¹ * t * p) * o⁻¹) * p⁻¹ := by
            group
        _ = p * (o * t * o⁻¹) * p⁻¹ := by
            rw [show p⁻¹ * t * p = t by
              have h2 := hpt p⁻¹ (inv_mem hp)
              rwa [inv_inv] at h2]
        _ = x' := by rw [← hx'o, hpx' p hp]
    calc o⁻¹ * (p * o * p⁻¹) * t = o⁻¹ * ((p * o * p⁻¹) * t * (p * o * p⁻¹)⁻¹) *
          (p * o * p⁻¹) := by group
      _ = o⁻¹ * (o * t * o⁻¹) * (p * o * p⁻¹) := by rw [h1, hx'o]
      _ = t * (o⁻¹ * (p * o * p⁻¹)) := by group
  obtain ⟨o₁, ho₁N, ho₁c⟩ := exists_commute_of_coprime hP hNodd hNn hy
  have ho₁t : o₁ * t * o₁⁻¹ = x' := by
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp ho₁N).2
    calc o₁ * t * o₁⁻¹ = o * ((o⁻¹ * o₁) * t) * (o⁻¹ * o₁)⁻¹ * o⁻¹ := by group
      _ = o * (t * (o⁻¹ * o₁)) * (o⁻¹ * o₁)⁻¹ * o⁻¹ := by rw [h1]
      _ = o * t * o⁻¹ := by group
      _ = x' := hx'o.symm
  refine ⟨k₁ * o₁, ?_, ?_⟩
  · rw [mul_assoc, (ho₁c c (mem_zpowers c)).symm, ← mul_assoc, hk₁c, mul_assoc]
  · calc (k₁ * o₁)⁻¹ * x * (k₁ * o₁) = o₁⁻¹ * x' * o₁ := by rw [hx']; group
      _ = o₁⁻¹ * (o₁ * t * o₁⁻¹) * o₁ := by rw [ho₁t]
      _ = t := by group

theorem zt_commute_T (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) (hsS : s ∉ S)
    (hz : z = s⁻¹ * t * s) {y : G} (hy : y ∈ T) : y * (z * t) = (z * t) * y := by
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have htz : t * z = z * t := h.zS t h.tS
  by_cases hyS : y ∈ S
  · rw [← mul_assoc, h.zS y hyS, mul_assoc, h.tZ y hyS, ← mul_assoc]
  · have hσ : s⁻¹ * y ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 (inv_mem hsT) hy
      (fun h1 => hsS (by simpa using inv_mem h1)) hyS
    have hyz : y * z * y⁻¹ = t := by
      calc y * z * y⁻¹ = s * ((s⁻¹ * y) * z * (s⁻¹ * y)⁻¹) * s⁻¹ := by group
        _ = s * z * s⁻¹ := by rw [h.zS _ hσ, mul_inv_cancel_right]
        _ = t := by rw [hz]; group
    have hyt : y * t * y⁻¹ = z := by
      calc y * t * y⁻¹ = s * ((s⁻¹ * y) * t * (s⁻¹ * y)⁻¹) * s⁻¹ := by group
        _ = s * t * s⁻¹ := by rw [h.tZ _ hσ, mul_inv_cancel_right]
        _ = z := h.conj_t_eq_z hss hz
    calc y * (z * t) = (y * z * y⁻¹) * (y * t * y⁻¹) * y := by group
      _ = (z * t) * y := by rw [hyz, hyt, htz]

theorem conj_z_ne_zt (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) (hsS : s ∉ S)
    (hz : z = s⁻¹ * t * s) (g : G) : g⁻¹ * z * g ≠ z * t := by
  intro hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := conjugate T g⁻¹ with hP
  have hPC : P ≤ centralizer ({z} : Set G) := by
    intro x hx
    rw [hP, mem_conjugate_iff, inv_inv] at hx
    have h1 := h.zt_commute_T hT2 hsT hsS hz hx
    rw [← hg] at h1
    refine mem_centralizer_singleton_iff.mpr ?_
    calc x * z = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = z * x := by group
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.sylT.isPGroup
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := k) (by
    rw [hP, card_conjugate_eq_card, hk])
  have h1 := card_le_twoPart hP2 (hPC.trans h.centralizer_le_normalizer)
  rw [twoPart, ← h.sylS.card_eq, hP, card_conjugate_eq_card, hT2] at h1
  have h2 : 0 < Nat.card S := Nat.card_pos
  omega

theorem mem_R_or_mem_Rs_of_conj (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) (hsS : s ∉ S)
    (hz : z = s⁻¹ * t * s) (hRsQ : conjugate (S ⊓ L) s ≤ Q) {g : G}
    (hg : g⁻¹ * z * g ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s) :
    g⁻¹ * z * g ∈ S ⊓ L ∨ g⁻¹ * z * g ∈ conjugate (S ⊓ L) s := by
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have hzt := h.conj_t_eq_z hss hz
  have hst : s * t * s⁻¹ ≠ t := by rw [hzt]; exact h.z_ne_t
  have hRs := h.inf_conjugate_R_eq_bot hna hsN hst
  have hcomm : ∀ a ∈ S ⊓ L, ∀ b ∈ conjugate (S ⊓ L) s, a * b = b * a := fun a ha b hb =>
    (h.commute_of_inf_conjugate_eq_bot hsN hRs ha hb).symm
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_commute hcomm hg
  have hz2 := h.z_mul_self
  have hx2 : (a * b) * (a * b) = 1 := by
    rw [← hab, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hz2]
    group
  have hab' := hcomm a ha b hb
  have haa : a * a = 1 := by
    have h1 : (a * a) * (b * b) = 1 := by
      rw [← hx2, show a * b * (a * b) = a * (b * a) * b by group, ← hab']
      group
    have h2 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a * a ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s :=
      mem_inf.mpr ⟨mul_mem ha ha, h2 ▸ inv_mem (mul_mem hb hb)⟩
    rwa [hRs, mem_bot] at h3
  have hbb : b * b = 1 := by
    have h1 : (a * a) * (b * b) = 1 := by
      rw [← hx2, show a * b * (a * b) = a * (b * a) * b by group, ← hab']
      group
    rwa [haa, one_mul] at h1
  by_cases ha1 : a = 1
  · right
    rw [hab, ha1, one_mul]
    exact hb
  by_cases hb1 : b = 1
  · left
    rw [hab, hb1, mul_one]
    exact ha
  exfalso
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact haa) ha1
  have hbQ := hRsQ hb
  obtain ⟨g₁, hg₁b, hg₁a⟩ := h.exists_conj_mul_of_mem_Q ha hao hbQ hbb hab'.symm
  set b' := s * b * s⁻¹ with hb'
  have hb'R : b' ∈ S ⊓ L := mem_conjugate_iff.mp hb
  have hb'2 : b' * b' = 1 := by
    rw [hb', show s * b * s⁻¹ * (s * b * s⁻¹) = s * (b * b) * s⁻¹ by group, hbb]
    group
  have hb'1 : b' ≠ 1 := fun h1 => hb1 (by
    calc b = s⁻¹ * b' * s := by rw [hb']; group
      _ = 1 := by rw [h1]; group)
  have hb'o : orderOf b' = 2 := orderOf_eq_prime (by rw [sq]; exact hb'2) hb'1
  obtain ⟨g₂, hg₂z, hg₂b⟩ := h.exists_conj_mul_of_mem_Q hb'R hb'o h.zQ hz2
    (h.zS b' (mem_inf.mp hb'R).1).symm
  have hstt : s⁻¹ * z * s = t := by
    rw [hz]
    have h1 := h.tZ _ hss
    calc s⁻¹ * (s⁻¹ * t * s) * s = (s * s)⁻¹ * (t * (s * s)) := by group
      _ = (s * s)⁻¹ * ((s * s) * t) := by rw [← h1]
      _ = t := by group
  have htb : t * b = b * t := hcomm t h.tR b hb
  set g₃ := s⁻¹ * g₂ * s with hg₃
  have hg₃bt : g₃⁻¹ * (b * t) * g₃ = z * t := by
    have h1 : g₂⁻¹ * (b' * z) * g₂ = t * z := by
      calc g₂⁻¹ * (b' * z) * g₂ = (g₂⁻¹ * b' * g₂) * (g₂⁻¹ * z * g₂) := by group
        _ = t * z := by
            rw [hg₂b, show g₂⁻¹ * z * g₂ = z by
              calc g₂⁻¹ * z * g₂ = g₂⁻¹ * (z * g₂) := by group
                _ = g₂⁻¹ * (g₂ * z) := by rw [hg₂z]
                _ = z := by group]
    calc g₃⁻¹ * (b * t) * g₃ = s⁻¹ * (g₂⁻¹ * (b' * (s * t * s⁻¹)) * g₂) * s := by
          rw [hg₃, hb']; group
      _ = s⁻¹ * (g₂⁻¹ * (b' * z) * g₂) * s := by rw [hzt]
      _ = s⁻¹ * (t * z) * s := by rw [h1]
      _ = (s⁻¹ * t * s) * (s⁻¹ * z * s) := by group
      _ = z * t := by rw [← hz, hstt]
  apply h.conj_z_ne_zt hT2 hsT hsS hz (g * (g₁ * g₃))
  calc (g * (g₁ * g₃))⁻¹ * z * (g * (g₁ * g₃)) = g₃⁻¹ * (g₁⁻¹ * (g⁻¹ * z * g) * g₁) * g₃ := by
        group
    _ = g₃⁻¹ * (g₁⁻¹ * (a * b) * g₁) * g₃ := by rw [hab]
    _ = g₃⁻¹ * ((g₁⁻¹ * a * g₁) * (g₁⁻¹ * b * g₁)) * g₃ := by group
    _ = g₃⁻¹ * (t * b) * g₃ := by
        rw [hg₁a, show g₁⁻¹ * b * g₁ = b by
          calc g₁⁻¹ * b * g₁ = g₁⁻¹ * (b * g₁) := by group
            _ = g₁⁻¹ * (g₁ * b) := by rw [hg₁b]
            _ = b := by group]
    _ = z * t := by rw [htb, hg₃bt]

end Sec5

end CFSG.ComponentClassification.Foote5
