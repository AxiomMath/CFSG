module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iCoreA
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iCoreB
public import CFSG.GH74.GLS.IVK.Proofs2.SylowCommute

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2.Lemma31iRels

namespace Lemma31iCoreC

variable {G : Type} [Group G] {n : ℕ} {z t d j d' j' : G}

theorem conj_rot₁' (h : Rels n z t d j d' j') (k : ℤ) :
    (d * d') ^ k * d' * ((d * d') ^ k)⁻¹ = d' := by
  rw [((Lemma31iCoreA.commute_a_d' h).zpow_left k).eq, mul_inv_cancel_right]

theorem v_conj_b (h : Rels n z t d j d' j') :
    (j * j') * (d * d'⁻¹) * (j * j')⁻¹ = (d * d'⁻¹)⁻¹ := by
  calc (j * j') * (d * d'⁻¹) * (j * j')⁻¹
      = ((j * j') * d * (j * j')⁻¹) * ((j * j') * d' * (j * j')⁻¹)⁻¹ := by group
    _ = d⁻¹ * d'⁻¹⁻¹ := by rw [Lemma31iCoreB.v_inv_d h, Lemma31iCoreB.v_inv_d' h]
    _ = (d * d'⁻¹)⁻¹ := by
      rw [inv_inv, mul_inv_rev, inv_inv]
      exact ((Lemma31iCoreA.commute_dd' h).inv_left).eq

theorem y_not_mem (h : Rels n z t d j d' j') :
    j * d' * j' ∉ B₁ d d' j j' t ⊔ B₂ d d' t := by
  intro hy
  have hn := h.three_le
  obtain ⟨w₁, hw₁, w₂, hw₂, hyw⟩ :=
    ((SylowCommute.card_sup_mul_card_inf _ _ (Lemma31iCoreA.B_comm h)).2 _).1 hy
  obtain ⟨k, hk⟩ := (Lemma31iCoreA.mem_B₁_iff h w₁).1 hw₁
  obtain ⟨l, hl⟩ := (Lemma31iCoreA.mem_B₂_iff h w₂).1 hw₂
  have hconj : d⁻¹ = w₁ * (w₂ * d * w₂⁻¹) * w₁⁻¹ := by
    rw [← Lemma31iCoreB.y_conj_d h, hyw]
    group
  rcases hk with hk | hk <;> rcases hl with hl | hl
  · rw [hl, Lemma31iCoreA.conj_rot₂ h l, hk, Lemma31iCoreA.conj_rot₁ h k] at hconj
    exact Lemma31iCoreB.d_sq_ne_one h (mul_eq_one_iff_eq_inv.mpr hconj.symm)
  · rw [hl, Lemma31iCoreA.conj_refl₂ h l, hk, conj_rot₁' h k] at hconj
    exact Lemma31iCoreA.d'_inv_ne_d h (by rw [← hconj, inv_inv])
  · rw [hl, Lemma31iCoreA.conj_rot₂ h l, hk, Lemma31iCoreA.conj_refl₁ h k] at hconj
    exact h.d_ne_d' (inv_inj.mp hconj).symm
  · have hy' : j * d' * j' = d' * (j * j') := by
      calc j * d' * j' = (j * d') * j' := rfl
        _ = (d' * j) * j' := by rw [h.jd']
        _ = d' * (j * j') := by group
    have ht2 : t * (d * d'⁻¹) ^ l * t = ((d * d'⁻¹)⁻¹) ^ l := by
      have e := (conj_zpow (a := t) (b := d * d'⁻¹) (i := l)).symm
      rw [Lemma31iCoreA.t_conj_b h, Lemma31iCoreB.tinv h] at e
      exact e
    have hprod : j * d' * j' = (d * d') ^ k * (j * j') * ((d * d'⁻¹)⁻¹) ^ l := by
      rw [hyw, hk, hl, ← ht2]
      group
    have e4 : (j * j') * (d * d'⁻¹)⁻¹ * (j * j')⁻¹ = d * d'⁻¹ := by
      calc (j * j') * (d * d'⁻¹)⁻¹ * (j * j')⁻¹ = ((j * j') * (d * d'⁻¹) * (j * j')⁻¹)⁻¹ := by group
        _ = ((d * d'⁻¹)⁻¹)⁻¹ := by rw [v_conj_b h]
        _ = d * d'⁻¹ := inv_inv _
    have e3 : (j * j') * ((d * d'⁻¹)⁻¹) ^ l * (j * j')⁻¹ = (d * d'⁻¹) ^ l := by
      have := conj_zpow (a := j * j') (b := (d * d'⁻¹)⁻¹) (i := l)
      rw [e4] at this
      exact this.symm
    have hd' : d' = (d * d') ^ k * (d * d'⁻¹) ^ l := by
      have e1 : d' * (j * j') = (d * d') ^ k * (j * j') * ((d * d'⁻¹)⁻¹) ^ l := by
        rw [← hy', hprod]
      have e2 : d' = (d * d') ^ k * ((j * j') * ((d * d'⁻¹)⁻¹) ^ l * (j * j')⁻¹) := by
        calc d' = d' * (j * j') * (j * j')⁻¹ := by group
          _ = (d * d') ^ k * (j * j') * ((d * d'⁻¹)⁻¹) ^ l * (j * j')⁻¹ := by rw [e1]
          _ = (d * d') ^ k * ((j * j') * ((d * d'⁻¹)⁻¹) ^ l * (j * j')⁻¹) := by group
      exact e2.trans (by rw [e3])
    have hX : d ^ (k + l) = d' ^ (1 - (k - l)) := by
      have e : d' = d ^ (k + l) * d' ^ (k - l) :=
        hd'.trans (Lemma31iCoreA.a_zpow_mul_b_zpow h k l)
      calc d ^ (k + l) = d' * (d' ^ (k - l))⁻¹ := eq_mul_inv_of_mul_eq e.symm
        _ = d' ^ (1 - (k - l)) := by rw [zpow_sub d' (1 : ℤ) (k - l), zpow_one]
    have hdiv1 := Lemma31iCoreA.dvd_of_zpow_eq h _ _ hX
    have hX' : d ^ (1 - (k - l)) = d' ^ (k + l) := by
      have e : t * d ^ (k + l) * t⁻¹ = t * d' ^ (1 - (k - l)) * t⁻¹ := by rw [hX]
      rw [Lemma31iCoreA.t_zpow_d h, Lemma31iCoreA.t_zpow_d' h] at e
      exact e.symm
    have hdiv2 := Lemma31iCoreA.dvd_of_zpow_eq h _ _ hX'
    have h2 : (2 : ℤ) ∣ ((2 ^ (n - 2) : ℕ) : ℤ) := by
      refine ⟨((2 ^ (n - 3) : ℕ) : ℤ), ?_⟩
      rw [Lemma31iCoreA.pow_n2 hn]
      push_cast
      ring
    have e1 := h2.trans hdiv1
    have e2 := h2.trans hdiv2
    omega

theorem card_big [Finite G] (h : Rels n z t d j d' j') :
    2 ^ (2 * n - 1) ≤ Nat.card ↥(B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j')) := by
  have hn := h.three_le
  have hcardM : Nat.card ↥(B₁ d d' j j' t ⊔ B₂ d d' t) = 2 ^ (2 * n - 2) := by
    obtain ⟨hc, -⟩ := SylowCommute.card_sup_mul_card_inf (B₁ d d' j j' t) (B₂ d d' t)
      (Lemma31iCoreA.B_comm h)
    rw [Lemma31iCoreA.B_inf h, Subgroup.card_bot, mul_one, Lemma31iCoreA.card_B₁ h,
      Lemma31iCoreA.card_B₂ h, ← pow_add] at hc
    rw [hc]
    congr 1
    omega
  have hne : Nat.card ↥(B₁ d d' j j' t ⊔ B₂ d d' t) ≠
      Nat.card ↥(B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j')) := by
    intro hc
    have heq := Subgroup.eq_of_le_of_card_ge
      (le_sup_left : B₁ d d' j j' t ⊔ B₂ d d' t ≤
        B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j')) (le_of_eq hc.symm)
    apply y_not_mem h
    rw [heq]
    exact mem_sup_right (mem_zpowers _)
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le
    (le_sup_left : B₁ d d' j j' t ⊔ B₂ d d' t ≤
      B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j'))
  have hc2 : 2 ≤ c := by
    by_contra hcon
    push Not at hcon
    interval_cases c
    · rw [mul_zero] at hc
      have := Nat.card_pos (α := ↥(B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j')))
      omega
    · rw [mul_one] at hc
      exact hne hc.symm
  calc 2 ^ (2 * n - 1) = 2 ^ (2 * n - 2) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
    _ = Nat.card ↥(B₁ d d' j j' t ⊔ B₂ d d' t) * 2 := by rw [hcardM]
    _ ≤ Nat.card ↥(B₁ d d' j j' t ⊔ B₂ d d' t) * c := Nat.mul_le_mul_left _ hc2
    _ = _ := hc.symm

theorem B_le_of_mem {M : Subgroup G} (hd : d ∈ M) (hd' : d' ∈ M)
    (hj : j ∈ M) (hj' : j' ∈ M) (ht : t ∈ M) :
    B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j') ≤ M := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact sup_le (zpowers_le.mpr (mul_mem hd hd'))
      (zpowers_le.mpr (mul_mem (mul_mem hj hj') ht))
  · exact sup_le (zpowers_le.mpr (mul_mem hd (inv_mem hd'))) (zpowers_le.mpr ht)
  · exact zpowers_le.mpr (mul_mem (mul_mem hj hd') hj')

theorem B_comm_z (h : Rels n z t d j d' j') :
    ∀ g ∈ B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j'), g * z = z * g := by
  intro g hg
  have hle := B_le_of_mem (M := centralizer ({z} : Set G))
    (mem_centralizer_singleton_iff.mpr h.z_comm_d.symm)
    (mem_centralizer_singleton_iff.mpr h.z_comm_d'.symm)
    (mem_centralizer_singleton_iff.mpr h.z_comm_j.symm)
    (mem_centralizer_singleton_iff.mpr h.z_comm_j'.symm)
    (mem_centralizer_singleton_iff.mpr h.z_comm_t.symm)
  exact mem_centralizer_singleton_iff.mp (hle hg)

end Lemma31iCoreC

end CFSG.GH74.GLS.IVK.Proofs2
