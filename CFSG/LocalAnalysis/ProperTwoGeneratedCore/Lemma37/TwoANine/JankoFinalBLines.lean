module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalBCenter

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalB

open Subgroup JankoTwelve JankoFinal

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z} {m s : G}
  {W : Subgroup G}

theorem conj_mem_center {g x : G} (hg : g ∈ normalizer (W : Set G))
    (hx : x ∈ W ⊓ centralizer (W : Set G)) : g * x * g⁻¹ ∈ W ⊓ centralizer (W : Set G) :=
  (mem_normalizer_iff.mp (mem_normalizer_inf_centralizer hg) x).mp hx

omit [Finite G] in
theorem p_mem_S {p : G} (hp : fr.P3bar = zpowers p) : p ∈ fr.S :=
  (le_sup_left : fr.P3bar ≤ fr.P3bar ⊔ fr.P3bbar) (hp ▸ mem_zpowers p)

omit [Finite G] in
theorem mem_centralizer_P3bar {p g : G} (hp : fr.P3bar = zpowers p) (hg : g * p = p * g) :
    g ∈ centralizer (fr.P3bar : Set G) := by
  rw [hp, centralizer_zpowers]
  exact mem_centralizer_singleton_iff.mpr hg

theorem exists_mem_normalizer_W_ne (h : Hyp fr) (hW : JankoFinalW fr m W s) {p : G}
    (hp : fr.P3bar = zpowers p) (hp3 : orderOf p = 3) :
    ∃ g ∈ normalizer (W : Set G), g * s = s * g ∧ g * p * g⁻¹ ≠ p ∧ Odd (orderOf g) := by
  have hm := hW.choiceM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : p ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hp3; exact absurd hp3 (by norm_num)
  have hps : IsConj s p := hW.isConj_s.trans (h.isConj_s₃_of_mem_S (p_mem_S hp) hp1).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hps
  have hcard : Nat.card (centralizer ({p} : Set G)) = Nat.card (centralizer ({s} : Set G)) := by
    have := card_inf_centralizer_conj (U := ⊤) (g := c)
      (mem_normalizer_iff.mpr fun x => by simp) s
    rwa [hc, top_inf_eq, top_inf_eq] at this
  have hRp : fr.R m ≤ centralizer ({p} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp
      (h.R_le_centralizer_P3bar hm.mem_centralizer hr) p (hp ▸ mem_zpowers p)).symm
  have h10 : 3 ^ 10 ∣ Nat.card (centralizer ({s} : Set G)) := by
    rw [← hcard, ← h.card_R hm.mem_K hm.orderOf_m]
    exact card_dvd_of_le hRp
  obtain ⟨K, hK, hWK, hKs⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (n := 9) (by rw [hW.card_W]; exact pow_dvd_pow 3 (by norm_num))
    ((pow_dvd_pow 3 (by norm_num)).trans h10) (W_le_centralizer_s hW)
  have hlt : W < K := lt_of_le_of_ne hWK fun heq => by
    have := hW.card_W
    rw [heq, hK] at this
    exact absurd this (by norm_num)
  obtain ⟨g, hgK, hgW, hgN⟩ := exists_mem_normalizer_not_mem (IsPGroup.of_card hK) hlt
  have hgs : g * s = s * g := mem_centralizer_singleton_iff.mp (hKs hgK)
  refine ⟨g, hgN, hgs, fun hgp => hgW ?_, odd_orderOf_of_mem hK hgK⟩
  exact mem_W_of_comm h hW hgs (mem_centralizer_P3bar hp (mul_inv_eq_iff_eq_mul.mp hgp))

theorem exists_mem_normalizer_W_comm_p (h : Hyp fr) (hW : JankoFinalW fr m W s) {p : G}
    (hp : fr.P3bar = zpowers p) :
    ∃ r ∈ normalizer (W : Set G), r * p = p * r ∧ r * s * r⁻¹ ≠ s ∧ Odd (orderOf r) := by
  have hm := hW.choiceM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR := h.card_R hm.mem_K hm.orderOf_m
  have hlt : W < fr.R m := lt_of_le_of_ne (W_le_R hW) fun heq => by
    have := hW.card_W
    rw [heq, hR] at this
    exact absurd this (by norm_num)
  obtain ⟨r, hrR, hrW, hrN⟩ := exists_mem_normalizer_not_mem (IsPGroup.of_card hR) hlt
  refine ⟨r, hrN, (mem_centralizer_iff.mp (h.R_le_centralizer_P3bar hm.mem_centralizer hrR) p
    (hp ▸ mem_zpowers p)).symm, fun hrs => hrW ?_, odd_orderOf_of_mem hR hrR⟩
  rw [← hW.R_inf_centralizer]
  exact mem_inf.mpr ⟨hrR, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hrs)⟩

theorem false_of_swap (h : Hyp fr) (hW : JankoFinalW fr m W s) {p σ g : G}
    (hp : fr.P3bar = zpowers p) (hσ : zpowers σ = zpowers s) (hσE : σ ∈ fr.E)
    (htσ : fr.t * σ * fr.t⁻¹ = σ⁻¹) (hgN : g ∈ normalizer (W : Set G))
    (hgp : g * p * g⁻¹ = σ) (hgσ : g * σ * g⁻¹ = p⁻¹) : False := by
  have htt : fr.t * fr.t = 1 := by rw [← sq, ← fr.orderOf_t, pow_orderOf_eq_one]
  have hzz : z * z = 1 := by rw [← sq, ← h.set.orderOf_z, pow_orderOf_eq_one]
  have hpP : p ∈ fr.P3bar := hp ▸ mem_zpowers p
  have c1 : MulAut.conj g⁻¹ σ = p := by rw [MulAut.conj_apply, inv_inv, ← hgp]; group
  have c2 : MulAut.conj g⁻¹ p = σ⁻¹ := by
    have hp' : p = (g * σ * g⁻¹)⁻¹ := by rw [hgσ, inv_inv]
    rw [MulAut.conj_apply, inv_inv, hp']
    group
  have c3 : MulAut.conj z p = p⁻¹ := by
    rw [MulAut.conj_apply]
    exact h.z_inv_of_mem_S (p_mem_S hp)
  have c4 : MulAut.conj z σ = σ := by
    rw [MulAut.conj_apply, ← mem_centralizer_singleton_iff.mp (fr.E_le hσE),
      mul_inv_cancel_right]
  have c5 : MulAut.conj g p = σ := by rw [MulAut.conj_apply, hgp]
  have c6 : MulAut.conj g σ = p⁻¹ := by rw [MulAut.conj_apply, hgσ]
  have c7 : MulAut.conj fr.t σ = σ⁻¹ := by rw [MulAut.conj_apply, htσ]
  have c8 : MulAut.conj fr.t p = p := by
    rw [MulAut.conj_apply, ← mem_centralizer_iff.mp h.t_mem_centralizer_P3bar p hpP,
      mul_inv_cancel_right]
  obtain ⟨y, hy⟩ : ∃ y, y = fr.t * (g * z * g⁻¹) := ⟨_, rfl⟩
  have hyc : ∀ a, y * a * y⁻¹ =
      MulAut.conj fr.t (MulAut.conj g (MulAut.conj z (MulAut.conj g⁻¹ a))) := by
    intro a
    simp only [MulAut.conj_apply]
    rw [hy]
    group
  have hyσ : y * σ * y⁻¹ = σ := by rw [hyc, c1, c3, map_inv, c5, map_inv, c7, inv_inv]
  have hyp : y * p * y⁻¹ = p := by rw [hyc, c2, map_inv, c4, map_inv, c6, inv_inv, c8]
  have hys : y * s = s * y := by
    have hyC : y ∈ centralizer (zpowers σ : Set G) := by
      rw [centralizer_zpowers]
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hyσ)
    rw [hσ, centralizer_zpowers] at hyC
    exact mem_centralizer_singleton_iff.mp hyC
  have hyW : y ∈ W :=
    mem_W_of_comm h hW hys (mem_centralizer_P3bar hp (mul_inv_eq_iff_eq_mul.mp hyp))
  have hx : fr.t * y = g * z * g⁻¹ := by rw [hy, ← mul_assoc, htt, one_mul]
  have hty : fr.t * y * (fr.t * y) = 1 := by
    rw [hx]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  obtain ⟨w, hw, hwt⟩ := exists_conj_eq_mul htt hty (odd_orderOf_of_mem hW.card_W hyW)
  have hwW : w ∈ W := zpowers_le.mpr hyW hw
  have hkN : w⁻¹ * g ∈ normalizer (W : Set G) := mul_mem (inv_mem (le_normalizer hwW)) hgN
  have hk : w⁻¹ * g * z * (w⁻¹ * g)⁻¹ = fr.t := by
    calc w⁻¹ * g * z * (w⁻¹ * g)⁻¹ = w⁻¹ * (g * z * g⁻¹) * w := by group
      _ = w⁻¹ * (w * fr.t * w⁻¹) * w := by rw [← hx, hwt]
      _ = fr.t := by group
  have hcard := card_inf_centralizer_conj hkN z
  rw [hk, hW.card_W_inf_t, hW.card_W_inf_z] at hcard
  norm_num at hcard

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalB
