module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainConfig

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Stage1

variable {G : Type*} [Group G]

namespace Config

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  {k : ℕ} {A : Subgroup G} (hS : Setup ε t L U Q P a ψ p) (hC : Config t Q P k A)
include hS hC

theorem mem_At [Finite G] {x : G} (hx : x ∈ A ⊔ zpowers t) : ∃ b ∈ A, x = b ∨ x = b * t := by
  obtain ⟨b, hb, z, hz, rfl⟩ :=
    exists_mul_of_mem_sup_normalizer (zpowers_le.2 hC.t_mem_normalizer) hx
  rcases hS.shape.mem_zpowers_iff.1 hz with rfl | rfl
  · exact ⟨b, hb, Or.inl (mul_one b)⟩
  · exact ⟨b, hb, Or.inr rfl⟩

theorem conj_t_eq [Finite G] {y : G}
    (hy : y ∈ normalizer ((A ⊔ (U ⊔ zpowers t) : Subgroup G) : Set G)) :
    ∃ b ∈ A, y⁻¹ * t * y = b * t := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  set T : Subgroup G := A ⊔ (U ⊔ zpowers t)
  have htT : t ∈ T := mem_sup_right (mem_sup_right (mem_zpowers t))
  have hAT : A ≤ T := le_sup_left
  have hyi : y⁻¹ ∈ normalizer (T : Set G) := inv_mem hy
  have ht'T : y⁻¹ * t * y ∈ T := by
    have := (mem_normalizer_iff.1 hyi t).1 htT
    rwa [inv_inv] at this
  have htriv : ∀ x ∈ A, (y⁻¹ * t * y) * x * (y⁻¹ * t * y)⁻¹ * x⁻¹ ∈ pw A 2 := by
    intro x hx
    have hyx : y * x * y⁻¹ ∈ T := (mem_normalizer_iff.1 hy x).1 (hAT hx)
    have hz := hC.cm_mem_pw_T hS hyx
    have hzA : y⁻¹ * cm t (y * x * y⁻¹) * y ∈ A := by
      have h1 : y⁻¹ * t * y * x⁻¹ * (y⁻¹ * t * y)⁻¹ ∈ A := by
        have := (mem_normalizer_iff.1 ((hC.T_le_normalizer hS) ht'T) x⁻¹).1 (inv_mem hx)
        simpa [mul_assoc] using this
      have e : y⁻¹ * cm t (y * x * y⁻¹) * y = x * (y⁻¹ * t * y * x⁻¹ * (y⁻¹ * t * y)⁻¹) := by
        simp only [cm]; group
      rw [e]
      exact mul_mem hx h1
    have hpow : (y⁻¹ * cm t (y * x * y⁻¹) * y) ^ 2 ^ (k - 1) = 1 := by
      have e := conj_pow (a := y⁻¹) (b := cm t (y * x * y⁻¹)) (i := 2 ^ (k - 1))
      rw [inv_inv] at e
      rw [e, (hC.level.pow_eq_one_iff hQ hQ2 hC.k_pos (pw_le A 2 hz)).2 hz]
      group
    have hmem := (hC.level.pow_eq_one_iff hQ hQ2 hC.k_pos hzA).1 hpow
    have e : (y⁻¹ * t * y) * x * (y⁻¹ * t * y)⁻¹ * x⁻¹ =
        (y⁻¹ * cm t (y * x * y⁻¹) * y)⁻¹ := by
      simp only [cm]; group
    rw [e]
    exact inv_mem hmem
  obtain ⟨b, hb, hb' | hb'⟩ := hC.mem_At hS (hC.mem_At_of_trivial hS ht'T htriv)
  · exfalso
    have h2 : (y⁻¹ * t * y) * (y⁻¹ * t * y) = 1 := by
      rw [show (y⁻¹ * t * y) * (y⁻¹ * t * y) = y⁻¹ * (t * t) * y by group, hS.shape.mul_self]
      group
    have hq : y⁻¹ * t * y ∈ Q := hC.level.mem_Q _ (hb' ▸ hb) h2
    have := hS.shape.conj_not_mem hS.rad.odd y⁻¹
    rw [inv_inv] at this
    exact this (hS.rad.Q_le_L hq)
  · exact ⟨b, hb, hb'⟩

theorem normalizes_pw [Finite G] {x : G}
    (hx : x ∈ normalizer ((A ⊔ (U ⊔ zpowers t) : Subgroup G) : Set G)) :
    ∀ c ∈ pw A 2, x * c * x⁻¹ ∈ pw A 2 := by
  intro c hc
  obtain ⟨b, hb, hbt⟩ := hC.conj_t_eq hS hx
  obtain ⟨y, hy, rfl⟩ := hC.exists_cm_eq hS hc
  have h1 : cm t y = cm (x⁻¹ * t * x) y := by
    rw [hbt, cm_mul_t hC.level.comm (fun _ h => hC.t_conj_mem h) hy hb]
  rw [h1]
  have h2 := cm_conj_conj x (x⁻¹ * t * x) y
  rw [show x * (x⁻¹ * t * x) * x⁻¹ = t by group] at h2
  rw [← h2]
  exact hC.cm_mem_pw_T hS ((mem_normalizer_iff.1 hx y).1 (mem_sup_left hy))

theorem normalizes_A [Finite G] (hk : 3 ≤ k) {x : G}
    (hx : x ∈ normalizer ((A ⊔ (U ⊔ zpowers t) : Subgroup G) : Set G)) :
    ∀ b ∈ A, x * b * x⁻¹ ∈ A := by
  intro b hb
  refine hC.mem_A_of_centralizer_pw hS hk ((mem_normalizer_iff.1 hx b).1 (mem_sup_left hb))
    fun c hc => ?_
  have hc' : x⁻¹ * c * x ∈ pw A 2 := by
    have := hC.normalizes_pw hS (inv_mem hx) c hc
    rwa [inv_inv] at this
  have hcomm := hC.level.comm b hb _ (pw_le A 2 hc')
  calc x * b * x⁻¹ * c = x * (b * (x⁻¹ * c * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * c * x) * b) * x⁻¹ := by rw [hcomm]
    _ = c * (x * b * x⁻¹) := by group

theorem mem_T_of_normalizer [Finite G] (hT : Terminal t P k A)
    {x : G} (hx : x ∈ normalizer ((A ⊔ (U ⊔ zpowers t) : Subgroup G) : Set G))
    (hx2 : IsPGroup 2 (zpowers x)) : x ∈ A ⊔ (U ⊔ zpowers t) := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  have hxN : x ∈ A ⊔ (P ⊔ zpowers t) := by
    rcases hT with ⟨hinv, hN⟩ | ⟨hk, hτ⟩
    · apply hN
      by_cases hk : k = 2
      · have hpwQ : pw A 2 = Q := by
          have := hC.level.pw_top hQ hQ2 hC.k_pos
          rwa [hk] at this
        refine mem_normalizer_of_conj_mem fun z hz => ?_
        have hzT : z ∈ A ⊔ (U ⊔ zpowers t) := (sup_le_sup_left le_sup_right A) hz
        refine hC.mem_At_of_centralizer_Q hS ((mem_normalizer_iff.1 hx z).1 hzT) fun q hq => ?_
        have hq' : x⁻¹ * q * x ∈ Q := by
          have := hC.normalizes_pw hS (inv_mem hx) q (hpwQ ▸ hq)
          rwa [inv_inv, hpwQ] at this
        have hzc : z * (x⁻¹ * q * x) = (x⁻¹ * q * x) * z := by
          obtain ⟨b, hb, hzb | hzb⟩ := hC.mem_At hS hz
          · rw [hzb]
            exact hC.level.comm b hb _ (hC.level.Q_le hq')
          · rw [hzb]
            have h1 := hC.level.comm b hb _ (hC.level.Q_le hq')
            have h2 := hS.shape.commute_of_mem (hS.rad.Q_le_L hq')
            rw [mul_assoc, ← h2, ← mul_assoc, h1, mul_assoc]
        calc x * z * x⁻¹ * q = x * (z * (x⁻¹ * q * x)) * x⁻¹ := by group
          _ = x * ((x⁻¹ * q * x) * z) * x⁻¹ := by rw [hzc]
          _ = q * (x * z * x⁻¹) := by group
      · have hk3 : 3 ≤ k := by have := hC.two_le; omega
        refine mem_normalizer_of_conj_mem fun z hz => ?_
        obtain ⟨b, hb, hzb | hzb⟩ := hC.mem_At hS hz
        · rw [hzb]
          exact mem_sup_left (hC.normalizes_A hS hk3 hx b hb)
        · rw [hzb]
          obtain ⟨c, hc, hct⟩ := hC.conj_t_eq hS (inv_mem hx)
          rw [inv_inv] at hct
          rw [show x * (b * t) * x⁻¹ = (x * b * x⁻¹) * (x * t * x⁻¹) by group, hct, ← mul_assoc]
          exact mul_mem (mem_sup_left (mul_mem (hC.normalizes_A hS hk3 hx b hb) hc))
            (mem_sup_right (mem_zpowers t))
    · apply hC.normalizer_le
      have htpw : zpowers t ≤ normalizer ((pw A 2 : Subgroup G) : Set G) :=
        zpowers_le.2 (mem_normalizer_of_conj_mem fun c hc => by
          rw [hC.t_inv_pw hc]; exact inv_mem hc)
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      obtain ⟨c, hc, w, hw, rfl⟩ := exists_mul_of_mem_sup_normalizer htpw hz
      have hxc := hC.normalizes_pw hS hx c hc
      rcases hS.shape.mem_zpowers_iff.1 hw with hw1 | hw1
      · rw [hw1, mul_one]
        exact mem_sup_left hxc
      · rw [hw1]
        obtain ⟨d, hd, hdt⟩ := hC.conj_t_eq hS (inv_mem hx)
        rw [inv_inv] at hdt
        have hd2 : d ^ 2 ^ (k - 1) = 1 := by
          have h1 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
            rw [show (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group,
              hS.shape.mul_self]
            group
          rw [hdt] at h1
          have h2 : d * t * (d * t) = d * (t * d * t⁻¹) * (t * t) := by group
          rw [h2, hτ d hd, hS.shape.mul_self, mul_one, ← mul_assoc, mul_inv_cancel,
            one_mul] at h1
          exact h1
        have hdpw := (hC.level.pow_eq_one_iff hQ hQ2 hC.k_pos hd).1 hd2
        rw [show x * (c * t) * x⁻¹ = (x * c * x⁻¹) * (x * t * x⁻¹) by group, hdt, ← mul_assoc]
        exact mul_mem (mem_sup_left (mul_mem hxc hdpw)) (mem_sup_right (mem_zpowers t))
  have hTN : A ⊔ (U ⊔ zpowers t) ≤ A ⊔ (P ⊔ zpowers t) :=
    sup_le_sup_left (sup_le_sup_right hS.rad.U_le_P _) A
  have hV : IsPGroup 2 (A ⊔ (U ⊔ zpowers t) ⊔ zpowers x : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (hC.isPGroup_T hS) hx2 (zpowers_le.2 hx)
  have heq := hC.eq_T_of_le_NA hS hV le_sup_left (sup_le hTN (zpowers_le.2 hxN))
  rw [← heq]
  exact mem_sup_right (mem_zpowers x)

theorem seitz_sylow [Finite G] (hT : Terminal t P k A)
    {V : Subgroup G} (hV : IsPGroup 2 V) (hTV : A ⊔ (U ⊔ zpowers t) ≤ V) :
    V = A ⊔ (U ⊔ zpowers t) := by
  by_contra hne
  have hlt : A ⊔ (U ⊔ zpowers t) < V := lt_of_le_of_ne hTV (Ne.symm hne)
  obtain ⟨n, hnV, hnN, hnT⟩ := exists_mem_normalizer_not_mem hV hlt
  exact hnT (hC.mem_T_of_normalizer hS hT hnN (hV.to_le (zpowers_le.2 hnV)))

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
