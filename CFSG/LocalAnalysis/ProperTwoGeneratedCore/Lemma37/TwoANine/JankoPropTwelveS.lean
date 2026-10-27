module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveK

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Hyp

variable {fr : JankoFrame G z}

theorem U_le_centralizer_S (h : Hyp fr) : fr.U ≤ centralizer (fr.S : Set G) := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  rw [← h.center_U] at hs
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hs).2 u hu).symm

theorem K_le_normalizer_centralizer_S (h : Hyp fr) :
    fr.K ≤ normalizer (centralizer (fr.S : Set G) : Set G) := fun _ hk =>
  mem_normalizer_centralizer (h.K_le_normalizer_S hk)

theorem centralizer_S_le_centralizer {y : G} (_h : Hyp fr) (hyS : y ∈ fr.S) :
    centralizer (fr.S : Set G) ≤ centralizer ({y} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyS)

theorem odd_card_centralizer_S (h : Hyp fr) : Odd (Nat.card (centralizer (fr.S : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₁ := centralizer (fr.S : Set G)
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨y, hy, hy1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bar (by norm_num)
  have hyS : y ∈ fr.S := (le_sup_left : fr.P3bar ≤ fr.S) hy
  have hys : IsConj y fr.s₃ := h.isConj_s₃_of_mem_S hyS hy1
  have htU : zpowers fr.t ≤ normalizer (U₁ : Set G) :=
    Subgroup.zpowers_le.mpr (h.K_le_normalizer_centralizer_S h.t_mem_K)
  have hb : zpowers fr.t ⊓ U₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rcases (CFSG.Walter.J1.mem_zpowers_of_orderOf_eq_two fr.orderOf_t).mp hx1 with h1 | h1
    · exact h1 ▸ Subgroup.one_mem _
    · exact absurd (h1 ▸ hx2) h.t_not_mem_centralizer_S
  have hcard := card_sup_of_inf_eq_bot htU hb
  have h4 : 2 ^ 2 ∣ Nat.card (zpowers fr.t ⊔ U₁ : Subgroup G) := by
    rw [hcard, Nat.card_zpowers, fr.orderOf_t]
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    exact ⟨k, by ring⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := (zpowers fr.t ⊔ U₁ : Subgroup G)) 2 h4
  have hP'c : Nat.card (P.map (zpowers fr.t ⊔ U₁).subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP]
    norm_num
  have hP'y : P.map (zpowers fr.t ⊔ U₁).subtype ≤ centralizer ({y} : Set G) :=
    (Subgroup.map_subtype_le _).trans (sup_le
      (Subgroup.zpowers_le.mpr (h.t_mem_centralizer_of_mem_P3bar hy))
      (h.centralizer_S_le_centralizer hyS))
  have := h.p7.card_le_two y hys _ hP'y (IsPGroup.of_card (n := 2) (by rw [hP'c]; norm_num))
  omega

theorem centralizer_S_inf_z (h : Hyp fr) :
    centralizer (fr.S : Set G) ⊓ centralizer ({z} : Set G) = fr.E := by
  set X₁ := centralizer (fr.S : Set G) ⊓ centralizer ({z} : Set G)
  have hEX : fr.E ≤ X₁ :=
    le_inf ((h.E_le_N.trans h.N_le_U).trans h.U_le_centralizer_S) fr.E_le
  have hKX : fr.K ≤ normalizer (X₁ : Set G) := fun k hk =>
    inf_mem_normalizer (h.K_le_normalizer_centralizer_S hk)
      (mem_normalizer_centralizer_singleton (Subgroup.mem_centralizer_singleton_iff.mp
        (fr.K_le hk)))
  have hXodd : Odd (Nat.card X₁) :=
    Odd.of_dvd_nat h.odd_card_centralizer_S (Subgroup.card_dvd_of_le inf_le_left)
  have hXN := fr.le_normalizer_E X₁ inf_le_right hXodd hEX hKX
  have hXEK : X₁ ≤ fr.E ⊔ fr.K := by
    rw [← fr.normalizer_E]
    exact le_inf hXN inf_le_right
  have hKX₁ : fr.K ⊓ X₁ = ⊥ :=
    le_bot_iff.mp (h.K_inf_centralizer_S ▸ inf_le_inf_left _ inf_le_left)
  have hprod := card_sup_of_inf_eq_bot hKX hKX₁
  have hle := Subgroup.card_le_of_le (sup_le le_sup_right hXEK : fr.K ⊔ X₁ ≤ fr.E ⊔ fr.K)
  rw [hprod, fr.card_K, h.card_E_sup_K] at hle
  exact (Subgroup.eq_of_le_of_card_ge hEX (by rw [fr.card_E]; omega)).symm

theorem card_centralizer_S_inf_le (h : Hyp fr) {y u : G} (hy : IsConj y fr.s₃)
    (hyS : y ∈ fr.S) (hu : orderOf u = 2) (hyu : y ∈ centralizer ({u} : Set G)) :
    Nat.card (centralizer (fr.S : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) ≤ 81 := by
  have h162 := (h.p7.isConj_s₃_iff u hu y hyu (h.pow_three_of_mem_M (h.S_le_M hyS))).mp hy
  have hd : Nat.card (centralizer (fr.S : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) ∣
      2 * 81 := by
    rw [show (2 : ℕ) * 81 = 162 by norm_num, ← h162]
    exact Subgroup.card_dvd_of_le (inf_le_inf_right _ (h.centralizer_S_le_centralizer hyS))
  have hodd : Odd (Nat.card (centralizer (fr.S : Set G) ⊓ centralizer ({u} : Set G) :
      Subgroup G)) :=
    Odd.of_dvd_nat h.odd_card_centralizer_S (Subgroup.card_dvd_of_le inf_le_left)
  exact Nat.le_of_dvd (by norm_num)
    ((Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left hd)

theorem centralizer_S (h : Hyp fr) : centralizer (fr.S : Set G) = fr.U := by
  set U₁ := centralizer (fr.S : Set G)
  obtain ⟨y, hy, hy1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bar (by norm_num)
  obtain ⟨y', hy', hy'1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bbar
    (by norm_num)
  have hyS : y ∈ fr.S := (le_sup_left : fr.P3bar ≤ fr.S) hy
  have hy'S : y' ∈ fr.S := (le_sup_right : fr.P3bbar ≤ fr.S) hy'
  have hbw := h.bw (W := U₁) (h.K_le_normalizer_centralizer_S h.t_mem_K)
    (h.K_le_normalizer_centralizer_S h.z_mem_K) h.odd_card_centralizer_S
  rw [h.inf_t_inf_z_eq h.centralizer_S_inf_z, h.card_P₂, h.centralizer_S_inf_z, fr.card_E] at hbw
  have h1 := h.card_centralizer_S_inf_le (h.isConj_s₃_of_mem_S hyS hy1) hyS fr.orderOf_t
    (Subgroup.mem_inf.mp hy).2
  have h2 := h.card_centralizer_S_inf_le (h.isConj_s₃_of_mem_S hy'S hy'1) hy'S h.orderOf_tz
    (Subgroup.mem_inf.mp hy').2
  have h3 := Nat.mul_le_mul (Nat.mul_le_mul_right 27 h1) h2
  rw [← hbw] at h3
  have hle : Nat.card U₁ ≤ 3 ^ 9 := by
    norm_num at h3 ⊢
    omega
  exact (Subgroup.eq_of_le_of_card_ge h.U_le_centralizer_S (by rw [h.card_U]; exact hle)).symm

theorem K_le_normalizer_U (h : Hyp fr) : fr.K ≤ normalizer (fr.U : Set G) := by
  rw [← h.centralizer_S]
  exact h.K_le_normalizer_centralizer_S

theorem U_inf_K (h : Hyp fr) : fr.U ⊓ fr.K = ⊥ := by
  rw [← h.centralizer_S, inf_comm]
  exact h.K_inf_centralizer_S

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
