module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYDCent
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup Equiv

section Fusion

variable {D : Type} [Group D] [Finite D] (c : DConfig D)

omit [Finite D] in
theorem DConfig.exists_conj_tb_vb : ∃ g : DBar D, g * c.tb * g⁻¹ = c.vb := by
  obtain ⟨g, hg⟩ := c.fus_v
  refine ⟨QuotientGroup.mk g, ?_⟩
  have := congrArg (QuotientGroup.mk : D → DBar D) hg
  simpa [DConfig.tb, DConfig.vb] using this

omit [Finite D] in
theorem DConfig.exists_conj_tb_tvb : ∃ g : DBar D, g * c.tb * g⁻¹ = c.tb * c.vb := by
  obtain ⟨g, hg⟩ := c.fus_tv
  refine ⟨QuotientGroup.mk g, ?_⟩
  have := congrArg (QuotientGroup.mk : D → DBar D) hg
  simpa [DConfig.tb, DConfig.vb] using this

theorem DConfig.cent_of_conj {a : DBar D} (ha : a ∈ zpowers c.tb ⊔ zpowers c.vb) {g : DBar D}
    (hg : g * c.tb * g⁻¹ = a) :
    centralizer ({a} : Set (DBar D)) = centralizer ({c.tb} : Set (DBar D)) := by
  have hcard : Nat.card ↥(centralizer ({a} : Set (DBar D))) = 480 := by
    rw [← hg, card_centralizer_conj, c.card_cent_tb]
  have hle := c.VJ_le_cent ha
  have : centralizer ({a} : Set (DBar D)) = (zpowers c.tb ⊔ zpowers c.vb) ⊔ c.fhom.range :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, c.card_VJ])).symm
  rw [this, c.cent_tb]

theorem DConfig.cent_vb :
    centralizer ({c.vb} : Set (DBar D)) = centralizer ({c.tb} : Set (DBar D)) := by
  obtain ⟨g, hg⟩ := c.exists_conj_tb_vb
  exact c.cent_of_conj (mem_sup_right (mem_zpowers _)) hg

theorem DConfig.cent_tvb :
    centralizer ({c.tb * c.vb} : Set (DBar D)) = centralizer ({c.tb} : Set (DBar D)) := by
  obtain ⟨g, hg⟩ := c.exists_conj_tb_tvb
  exact c.cent_of_conj (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)))
    hg

end Fusion

section Center

variable {D : Type} [Group D] [Finite D] (c : DConfig D)

theorem conj_eq_of_mem_center {X : Type*} [Group X] {w : X} (hw : w ∈ center X) (g : X) :
    g * w * g⁻¹ = w := by
  rw [mem_center_iff.1 hw g]
  group

include c in
theorem DConfig.center_bar : center (DBar D) = ⊥ := by
  classical
  by_contra hne
  have hZ1 : Nat.card (center (DBar D)) ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hZ1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center (DBar D))) p hpd
  have hzc : (z : DBar D) ∈ center (DBar D) := z.2
  have hz1 : (z : DBar D) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  by_cases hp2 : p = 2
  · subst hp2
    have hzC : (z : DBar D) ∈ centralizer ({c.tb} : Set (DBar D)) :=
      mem_centralizer_singleton_iff.2 (mem_center_iff.1 hzc c.tb).symm
    rw [c.cent_tb] at hzC
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute c.V_comm_J hzC
    obtain ⟨σ, rfl⟩ := hb
    have hσ : σ = 1 := by
      refine CFSG.perm_eq_one_of_forall_commute (by simp) fun τ => (c.fhom_injective ?_).symm
      have h1 := mem_center_iff.1 hzc (c.fhom τ)
      have h2 := c.V_comm_J a ha (c.fhom τ) ⟨τ, rfl⟩
      rw [hab, ← mul_assoc, ← h2, mul_assoc, mul_assoc] at h1
      rw [map_mul, map_mul]
      exact mul_left_cancel h1
    subst hσ
    rw [map_one, mul_one] at hab
    have hcc : ∀ g : DBar D, g * (z : DBar D) * g⁻¹ = z := fun g => conj_eq_of_mem_center hzc g
    rcases c.mem_V ha with h | h | h | h
    · rw [h] at hab
      exact hz1 hab
    · rw [h] at hab
      obtain ⟨g, hg⟩ := c.exists_conj_tb_vb
      apply c.tb_ne_vb
      have := hcc g
      rw [hab, hg] at this
      exact this.symm
    · rw [h] at hab
      obtain ⟨g, hg⟩ := c.exists_conj_tb_vb
      apply c.tb_ne_vb
      calc c.tb = g⁻¹ * (g * c.tb * g⁻¹) * g := by group
        _ = g⁻¹ * c.vb * g := by rw [hg]
        _ = c.vb := by
          have := hcc g⁻¹
          rw [hab, inv_inv] at this
          exact this
    · rw [h] at hab
      obtain ⟨g, hg⟩ := c.exists_conj_tb_tvb
      apply c.vb_ne_one
      have h3 : c.tb = c.tb * c.vb := by
        calc c.tb = g⁻¹ * (g * c.tb * g⁻¹) * g := by group
          _ = g⁻¹ * (c.tb * c.vb) * g := by rw [hg]
          _ = c.tb * c.vb := by
            have := hcc g⁻¹
            rw [hab, inv_inv] at this
            exact this
      exact left_eq_mul.1 h3
  · have hnorm : (zpowers (z : DBar D)).Normal := normal_zpowers_of_mem_center hzc
    have hodd : Odd (Nat.card (zpowers (z : DBar D))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
      exact hp.odd_of_ne_two hp2
    have hle := le_oddCore_of_normal' hodd
    rw [oddCore_quot_eq_bot] at hle
    exact hz1 (mem_bot.1 (hle (mem_zpowers _)))

include c in
theorem DConfig.zstar_bar : Open.fusionZStar (DBar D) = ⊥ := by
  have hO : Open.fusionOddCore (DBar D) = ⊥ := oddCore_quot_eq_bot
  have h1 := fusionZStar_le_center hO
  rw [c.center_bar] at h1
  exact le_bot_iff.1 h1

end Center

end CFSG.EvenSporadicStandard.HSStd.FiveY
