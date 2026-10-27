module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalAW

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal

open Subgroup JankoTwelve

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z} {m s : G} (h : Hyp fr)
  (p12 : JankoProp12 fr) (hm : JankoChoiceM fr m)
  (hs : fr.E ⊓ centralizer ({m} : Set G) = zpowers s) (hs3 : orderOf s = 3)

include h hm hs hs3 in
theorem card_K_inf_le : Nat.card (fr.K ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ 6 := by
  have h48 := card_dvd_of_le (inf_le_left : fr.K ⊓ centralizer ({s} : Set G) ≤ fr.K)
  have h162 := card_dvd_of_le (le_inf inf_le_right (inf_le_left.trans fr.K_le) :
    fr.K ⊓ centralizer ({s} : Set G) ≤ centralizer ({s} : Set G) ⊓ centralizer ({z} : Set G))
  rw [fr.card_K] at h48
  rw [card_centralizer_s h hm hs hs3] at h162
  exact Nat.le_of_dvd (by norm_num) (by simpa using Nat.dvd_gcd h48 h162)

include h p12 in
theorem UK_inf_le_of_mem {e : G} (he : e ∈ fr.E) : (fr.U ⊔ fr.K) ⊓ centralizer ({e} : Set G) ≤
    fr.K ⊓ centralizer ({e} : Set G) ⊔ fr.U ⊓ centralizer ({e} : Set G) := by
  rintro g ⟨hg, hge⟩
  rw [sup_comm] at hg
  obtain ⟨k, hk, u, hu, rfl⟩ := exists_mul_of_mem_sup p12.K_le_normalizer_U hg
  have hge' : k * u * e * (k * u)⁻¹ = e := by
    rw [mem_centralizer_singleton_iff.mp hge, mul_inv_cancel_right]
  have huS := comm_mem_S h p12 (E_le_I he) hu
  have hkE : k⁻¹ * e * k ∈ fr.E := by
    have := (mem_normalizer_iff.mp (fr.K_le_normalizer (inv_mem hk)) e).mp he
    rwa [inv_inv] at this
  have heq : k⁻¹ * e * k * e⁻¹ = u * e * u⁻¹ * e⁻¹ := by
    calc k⁻¹ * e * k * e⁻¹ = k⁻¹ * (k * u * e * (k * u)⁻¹) * k * e⁻¹ := by rw [hge']
      _ = u * e * u⁻¹ * e⁻¹ := by group
  have hmem : k⁻¹ * e * k * e⁻¹ ∈ fr.E ⊓ fr.S :=
    mem_inf.mpr ⟨fr.E.mul_mem hkE (fr.E.inv_mem he), heq ▸ huS⟩
  rw [E_inf_S h, mem_bot, mul_inv_eq_one] at hmem
  have hkC : k ∈ centralizer ({e} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc k * e = k * (k⁻¹ * e * k) := by rw [hmem]
      _ = e * k := by group
  have huC : u ∈ centralizer ({e} : Set G) := by
    have := mul_mem (inv_mem hkC) hge
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (mem_sup_left ⟨hk, hkC⟩) (mem_sup_right ⟨hu, huC⟩)

include h p12 hs in
theorem UK_inf_le : (fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G) ≤
    fr.K ⊓ centralizer ({s} : Set G) ⊔ fr.U ⊓ centralizer ({s} : Set G) :=
  UK_inf_le_of_mem h p12 (s_mem_E hs)

include h p12 hm hs hs3 in
theorem card_UK_inf_le :
    Nat.card ((fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ 2 * 3 ^ 8 := by
  have hle : fr.K ⊓ centralizer ({s} : Set G) ≤
      normalizer ((fr.U ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G) := fun k hk =>
    inf_mem_normalizer (p12.K_le_normalizer_U hk.1)
      (mem_normalizer_centralizer_singleton (mem_centralizer_singleton_iff.mp hk.2))
  have h1 := card_sup_mul_card_inf hle
  have hpos : 0 < Nat.card (fr.K ⊓ centralizer ({s} : Set G) ⊓
    (fr.U ⊓ centralizer ({s} : Set G)) : Subgroup G) := Nat.card_pos
  have h2 := card_K_inf_le h hm hs hs3
  rw [card_U_inf_s h p12 hs hs3] at h1
  calc Nat.card ((fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G) : Subgroup G)
      ≤ Nat.card (fr.K ⊓ centralizer ({s} : Set G) ⊔ fr.U ⊓ centralizer ({s} : Set G) :
        Subgroup G) := card_le_of_le (UK_inf_le h p12 hs)
    _ ≤ 2 * 3 ^ 8 := by nlinarith

include h hm hs in
theorem W_sup_z_le : Wof fr m s ⊔ zpowers z ≤ (fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G) := by
  have hR : fr.R m ≤ fr.U ⊔ fr.K := sup_le le_sup_left (zpowers_le.mpr (mem_sup_right hm.mem_K))
  have hzs : z ∈ centralizer ({s} : Set G) := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (fr.E_le (s_mem_E hs))).symm
  exact sup_le (le_inf (W_le_R.trans hR) (W_le_centralizer hs))
    (zpowers_le.mpr ⟨mem_sup_right h.z_mem_K, hzs⟩)

include h p12 hm hs hs3 in
theorem card_W_sup_z : Nat.card (Wof fr m s ⊔ zpowers z : Subgroup G) = 2 * 3 ^ 8 := by
  have hcop : Nat.Coprime (Nat.card (zpowers z)) (Nat.card (Wof fr m s)) := by
    rw [Nat.card_zpowers, h.set.orderOf_z, card_W h p12 hm hs hs3]
    norm_num
  rw [sup_comm, card_sup_of_inf_eq_bot (zpowers_le.mpr (z_mem_normalizer_W h hm hs))
    (disjoint_of_coprime_natCard hcop).eq_bot, Nat.card_zpowers, h.set.orderOf_z,
    card_W h p12 hm hs hs3]

include h p12 hm hs hs3 in
theorem UK_inf_centralizer_eq :
    (fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G) = Wof fr m s ⊔ zpowers z :=
  (eq_of_le_of_card_ge (W_sup_z_le h hm hs)
    (by rw [card_W_sup_z h p12 hm hs hs3]; exact card_UK_inf_le h p12 hm hs hs3)).symm

include h p12 hm hs hs3 in
theorem le_W_of_odd {B : Subgroup G} (hB : Odd (Nat.card B))
    (hBle : B ≤ (fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G)) : B ≤ Wof fr m s := by
  rw [UK_inf_centralizer_eq h p12 hm hs hs3] at hBle
  have hN : B ≤ normalizer (Wof fr m s : Set G) :=
    hBle.trans (sup_le le_normalizer (zpowers_le.mpr (z_mem_normalizer_W h hm hs)))
  have h1 := card_sup_mul_card_inf hN
  obtain ⟨q, hq⟩ := card_dvd_of_le (le_sup_right : Wof fr m s ≤ B ⊔ Wof fr m s)
  have hdvd := card_dvd_of_le (sup_le hBle le_sup_left)
  rw [card_W_sup_z h p12 hm hs hs3, hq, card_W h p12 hm hs hs3, mul_comm 2] at hdvd
  have hq2 : q ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  rw [card_W h p12 hm hs hs3] at hq h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with rfl | rfl
  · have hEq : Wof fr m s = B ⊔ Wof fr m s :=
      eq_of_le_of_card_ge le_sup_right (by rw [hq, card_W h p12 hm hs hs3, mul_one])
    exact hEq ▸ le_sup_left
  · rw [hq] at h1
    obtain ⟨r, hr⟩ := hB
    omega

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal
