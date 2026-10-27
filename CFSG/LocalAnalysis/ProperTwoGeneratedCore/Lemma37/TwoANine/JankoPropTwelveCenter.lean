module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveU

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem mem_inf_centralizer_conj_iff {U : Subgroup G} {g : G} (hg : g ∈ normalizer (U : Set G))
    (a y : G) : y ∈ U ⊓ centralizer ({g * a * g⁻¹} : Set G) ↔
      g⁻¹ * y * g ∈ U ⊓ centralizer ({a} : Set G) := by
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hU : y ∈ U ↔ g⁻¹ * y * g ∈ U := by
    have := Subgroup.mem_normalizer_iff.mp (inv_mem hg) y
    rwa [inv_inv] at this
  rw [← hU]
  refine and_congr_right fun _ => ⟨fun h1 => ?_, fun h1 => ?_⟩
  · calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [h1]
      _ = a * (g⁻¹ * y * g) := by group
  · calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * y := by group

namespace Hyp

variable {fr : JankoFrame G z}

theorem E_le_U_inf_z (h : Hyp fr) : fr.E ≤ fr.U ⊓ centralizer ({z} : Set G) := by
  rw [← h.p11.N_inf_centralizer_z]
  exact inf_le_inf_right _ h.N_le_U

theorem L_le_normalizer_U_inf_z (h : Hyp fr) :
    fr.L ≤ normalizer ((fr.U ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := fun _ hl =>
  inf_mem_normalizer (h.V_le_normalizer_U (h.L_le_normalizer_N hl))
    (mem_normalizer_centralizer_singleton (Subgroup.mem_centralizer_singleton_iff.mp
      (h.L_le_H hl)))

theorem U_inf_centralizer_z (h : Hyp fr) : fr.U ⊓ centralizer ({z} : Set G) = fr.E := by
  set Y := fr.U ⊓ centralizer ({z} : Set G)
  obtain ⟨b, hb9, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (h.card_U ▸ Subgroup.card_dvd_of_le (inf_le_left : Y ≤ fr.U))
  have hb3 : 3 ≤ b := by
    have h27 : 3 ^ 3 ∣ 3 ^ b := by
      have := Subgroup.card_dvd_of_le h.E_le_U_inf_z
      rw [fr.card_E, hb] at this
      simpa using this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h27
  have hYV : Y ≤ normalizer (fr.N : Set G) ⊓ centralizer ({z} : Set G) :=
    inf_le_inf_right _ h.U_le_V
  have hb4 : b ≤ 4 := by
    have hd := h.card_dvd_of_le_V_H hYV
    rw [hb] at hd
    have : 3 ^ b ∣ 3 ^ 4 := by
      have hc : Nat.Coprime (3 ^ b) (2 ^ 4) := Nat.Coprime.pow _ _ (by norm_num)
      exact hc.dvd_of_dvd_mul_left (by rw [show (2 : ℕ) ^ 4 * 3 ^ 4 = 1296 by norm_num]; exact hd)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hb3' : b = 3 := by
    by_contra hne
    have hb' : b = 4 := by omega
    rw [hb'] at hb
    have hYL : fr.L ⊓ Y = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
      rw [fr.card_L, hb]; norm_num))
    have hcYL : Nat.card (fr.L ⊔ Y : Subgroup G) = 1296 := by
      rw [card_sup_of_inf_eq_bot h.L_le_normalizer_U_inf_z hYL, fr.card_L, hb]
      all_goals norm_num
    have hle : fr.L ⊔ Y ≤ fr.E ⊔ fr.K := by
      refine sup_le (fr.L_le_K.trans le_sup_right) ?_
      rw [← fr.normalizer_E]
      exact hYV.trans h.normalizer_N_inf_H_le
    have heq : fr.L ⊔ Y = fr.E ⊔ fr.K :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcYL, h.card_E_sup_K])
    have hKY : fr.K ≤ normalizer (Y : Set G) := by
      refine (le_sup_right.trans heq.symm.le).trans (sup_le h.L_le_normalizer_U_inf_z ?_)
      exact Subgroup.le_normalizer
    have hKsup : fr.K ⊔ Y = fr.E ⊔ fr.K := by
      refine le_antisymm (sup_le le_sup_right ?_) (sup_le (h.E_le_U_inf_z.trans le_sup_right)
        le_sup_left)
      exact (le_sup_right : Y ≤ fr.L ⊔ Y).trans heq.le
    have hprod := card_sup_mul_card_inf hKY
    rw [hKsup, h.card_E_sup_K, fr.card_K, hb] at hprod
    have h3 : Nat.card (fr.K ⊓ Y : Subgroup G) = 3 := by omega
    exact fr.card_ne_three _ inf_le_left
      (fun k hk => inf_mem_normalizer (Subgroup.le_normalizer hk) (hKY hk)) h3
  rw [hb3'] at hb
  exact (Subgroup.eq_of_le_of_card_ge h.E_le_U_inf_z
    (by rw [hb, fr.card_E]; all_goals norm_num)).symm

theorem card_U_inf_t (h : Hyp fr) :
    Nat.card (fr.U ⊓ centralizer ({fr.t} : Set G) : Subgroup G) = 3 ^ 4 := by
  have hbw := h.bw h.t_mem_normalizer_U h.z_mem_normalizer_U h.odd_card_U
  rw [h.inf_t_inf_z_eq h.U_inf_centralizer_z, h.card_P₂, h.U_inf_centralizer_z, fr.card_E,
    h.card_U_inf_t_eq_tz, h.card_U] at hbw
  obtain ⟨e, he, hxe⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (h.card_U ▸ Subgroup.card_dvd_of_le (inf_le_left : fr.U ⊓ centralizer ({fr.t} : Set G) ≤ fr.U))
  rw [hxe] at hbw ⊢
  interval_cases e <;> omega

theorem card_U_inf_tz (h : Hyp fr) :
    Nat.card (fr.U ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) = 3 ^ 4 := by
  rw [h.card_U_inf_t_eq_tz, h.card_U_inf_t]

theorem U_inf_centralizer_s₁ (h : Hyp fr) :
    fr.U ⊓ centralizer ({fr.s₁} : Set G) = fr.N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : fr.N ≤ fr.U ⊓ centralizer ({fr.s₁} : Set G) := le_inf h.N_le_U h.N_le_centralizer_s₁
  have hU3 : IsPGroup 3 fr.U := IsPGroup.of_card h.card_U
  have hP : fr.U ⊓ centralizer ({fr.s₁} : Set G) ≤ normalizer (fr.P₁ : Set G) := by
    rw [← h.centralizer_P₁_eq]
    exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  exact (Subgroup.eq_of_le_of_card_ge hle
    (card_le_of_isSylowOf h.p11.isSylowOf_N (hU3.to_le inf_le_left) hP)).symm

theorem U_inf_centralizer_ZN (h : Hyp fr) {x : G} (hx : x ∈ fr.ZN) (hxS : x ∉ fr.S) :
    fr.U ⊓ centralizer ({x} : Set G) = fr.N := by
  obtain ⟨g, hg, rfl⟩ := h.mem_orbit_s₁ hx hxS
  ext y
  rw [mem_inf_centralizer_conj_iff (h.V_le_normalizer_U hg), h.U_inf_centralizer_s₁]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at this
  exact this.symm

theorem mem_normalizer_center_U (h : Hyp fr) {g : G} (hg : g ∈ normalizer (fr.N : Set G)) :
    g ∈ normalizer ((fr.U ⊓ centralizer (fr.U : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_inf_centralizer (h.V_le_normalizer_U hg)

theorem center_U_le_ZN (h : Hyp fr) : fr.U ⊓ centralizer (fr.U : Set G) ≤ fr.ZN := by
  intro x hx
  obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_centralizer_iff] at hxC
  have hxN : x ∈ fr.N := by
    rw [← h.U_inf_centralizer_s₁]
    refine Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (hxC _ (h.N_le_U ((le_sup_left : fr.E ≤ fr.N) h.s₁_mem_E))).symm
  refine Subgroup.mem_inf.mpr ⟨hxN, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
  exact hxC n (h.N_le_U hn)

theorem center_U_le_S (h : Hyp fr) : fr.U ⊓ centralizer (fr.U : Set G) ≤ fr.S := by
  intro x hx
  by_contra hxS
  have h1 := h.U_inf_centralizer_ZN (h.center_U_le_ZN hx) hxS
  have h2 : fr.U ⊓ centralizer ({x} : Set G) = fr.U := by
    refine inf_eq_left.mpr fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 u hu
  rw [h2] at h1
  have := congrArg (fun H : Subgroup G => Nat.card H) h1
  simp only [h.card_U, h.p11.card_N] at this
  exact absurd this (by norm_num)

theorem center_U (h : Hyp fr) : fr.U ⊓ centralizer (fr.U : Set G) = fr.S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ZU := fr.U ⊓ centralizer (fr.U : Set G)
  refine le_antisymm h.center_U_le_S ?_
  have hU3 : IsPGroup 3 fr.U := IsPGroup.of_card h.card_U
  have : Nontrivial fr.U := by
    rw [← Finite.one_lt_card_iff_nontrivial, h.card_U]
    norm_num
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (bot_lt_iff_ne_bot.mp hU3.bot_lt_center)
  set y : G := ((c : fr.U) : G)
  have hyZ : y ∈ ZU := by
    refine Subgroup.mem_inf.mpr ⟨(c : fr.U).2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨u, hu⟩)
  have hy1 : y ≠ 1 := fun h1 => hc1 (Subtype.ext (Subtype.ext h1))
  have hyS : y ∈ fr.S := h.center_U_le_S hyZ
  have htZ := h.mem_normalizer_center_U h.t_mem_V
  have hy'Z : fr.t * y * fr.t⁻¹ ∈ ZU := (Subgroup.mem_normalizer_iff.mp htZ y).mp hyZ
  have hcase : fr.P3bar ≤ ZU ∨ fr.P3bbar ≤ ZU := by
    by_cases ha : y * (fr.t * y * fr.t⁻¹) = 1
    · right
      have hty : fr.t * y * fr.t⁻¹ = y⁻¹ := eq_inv_of_mul_eq_one_right ha
      have hzy := h.z_inv_of_mem_S hyS
      have hyP : y ∈ fr.P3bbar := by
        refine Subgroup.mem_inf.mpr ⟨h.S_le_ZN hyS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hc : fr.t * z * y * (fr.t * z)⁻¹ = y := by
          calc fr.t * z * y * (fr.t * z)⁻¹ = fr.t * (z * y * z⁻¹) * fr.t⁻¹ := by group
            _ = (fr.t * y * fr.t⁻¹)⁻¹ := by rw [hzy]; group
            _ = y := by rw [hty, inv_inv]
        calc y * (fr.t * z) = (fr.t * z * y * (fr.t * z)⁻¹) * (fr.t * z) := by rw [hc]
          _ = fr.t * z * y := by group
      rw [CFSG.Walter.J1.eq_zpowers_of_card_prime Nat.prime_three h.p11.card_P3bbar hyP hy1]
      exact Subgroup.zpowers_le.mpr hyZ
    · left
      have hat : y * (fr.t * y * fr.t⁻¹) ∈ fr.P3bar := by
        refine Subgroup.mem_inf.mpr ⟨h.S_le_ZN (h.center_U_le_S (ZU.mul_mem hyZ hy'Z)),
          Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hcomm : (fr.t * y * fr.t⁻¹) * y = y * (fr.t * y * fr.t⁻¹) :=
          h.M_comm (h.S_le_M (h.center_U_le_S hy'Z)) (h.S_le_M hyS)
        have ht2 : fr.t * (fr.t * y * fr.t⁻¹) * fr.t⁻¹ = y := by
          calc fr.t * (fr.t * y * fr.t⁻¹) * fr.t⁻¹ = (fr.t * fr.t) * y * (fr.t * fr.t)⁻¹ := by
                group
            _ = y := by rw [h.t_mul_t]; group
        have hc : fr.t * (y * (fr.t * y * fr.t⁻¹)) * fr.t⁻¹ = y * (fr.t * y * fr.t⁻¹) := by
          calc fr.t * (y * (fr.t * y * fr.t⁻¹)) * fr.t⁻¹ =
                (fr.t * y * fr.t⁻¹) * (fr.t * (fr.t * y * fr.t⁻¹) * fr.t⁻¹) := by group
            _ = (fr.t * y * fr.t⁻¹) * y := by rw [ht2]
            _ = y * (fr.t * y * fr.t⁻¹) := hcomm
        calc y * (fr.t * y * fr.t⁻¹) * fr.t =
              (fr.t * (y * (fr.t * y * fr.t⁻¹)) * fr.t⁻¹) * fr.t := by rw [hc]
          _ = fr.t * (y * (fr.t * y * fr.t⁻¹)) := by group
      rw [CFSG.Walter.J1.eq_zpowers_of_card_prime Nat.prime_three h.p11.card_P3bar hat ha]
      exact Subgroup.zpowers_le.mpr (ZU.mul_mem hyZ hy'Z)
  have hℓ := h.mem_normalizer_center_U h.ℓ_sq_mem_normalizer_N
  have hP3 : fr.P3bar ≤ ZU ∧ fr.P3bbar ≤ ZU := by
    rcases hcase with h3 | h3
    · refine ⟨h3, fun w hw => ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp hℓ _).mp (h3 (h.ℓ_sq_inv_conj_mem_P3bar hw))
      rwa [show fr.ℓ ^ 2 * ((fr.ℓ ^ 2)⁻¹ * w * fr.ℓ ^ 2) * (fr.ℓ ^ 2)⁻¹ = w by group] at this
    · refine ⟨fun w hw => ?_, h3⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hℓ) _).mp (h3 (h.ℓ_sq_conj_mem_P3bbar hw))
      rwa [show (fr.ℓ ^ 2)⁻¹ * (fr.ℓ ^ 2 * w * (fr.ℓ ^ 2)⁻¹) * (fr.ℓ ^ 2)⁻¹⁻¹ = w by group]
        at this
  exact sup_le hP3.1 hP3.2

theorem isConj_s₁_of_mem_M (h : Hyp fr) {x : G} (hx : x ∈ fr.M) (hxM : x ∉ fr.Mbar) :
    IsConj x fr.s₁ := by
  by_cases hxP : x ∈ fr.P₁
  · have hx1 : x ≠ 1 := fun h1 => hxM (h1 ▸ one_mem _)
    rw [fr.P₁_eq] at hxP
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers fr.orderOf_s₁ hxP with h1 | h1 | h1
    · exact absurd h1 hx1
    · subst h1
      exact IsConj.refl _
    · subst h1
      exact (isConj_iff.mpr ⟨fr.t, h.t_conj_s₁⟩).symm
  · obtain ⟨y₀, hy₀P, hy₀1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bar
      (by norm_num)
    have hy₀S : y₀ ∈ fr.S := (le_sup_left : fr.P3bar ≤ fr.S) hy₀P
    have hx₀Z : fr.s₁ * y₀ ∈ fr.ZN := mul_mem h.s₁_mem_ZN (h.S_le_ZN hy₀S)
    have hx₀S : fr.s₁ * y₀ ∉ fr.S := fun hS => h.s₁_not_mem_S (by
      have := mul_mem hS (inv_mem hy₀S)
      rwa [mul_inv_cancel_right] at this)
    have hx₀P : fr.s₁ * y₀ ∉ fr.P₁ := fun hP => hy₀1 (h.eq_one_of_mem_P₁_of_mem_Mbar (by
      have := mul_mem (inv_mem h.s₁_mem_P₁) hP
      rwa [inv_mul_cancel_left] at this) (h.S_le_Mbar hy₀S))
    have hx₀M : fr.s₁ * y₀ ∉ fr.Mbar := fun hMb =>
      hx₀S (h.ZN_inf_Mbar ▸ Subgroup.mem_inf.mpr ⟨hx₀Z, hMb⟩)
    obtain ⟨g, -, hg⟩ := h.mem_orbit_s₁ hx₀Z hx₀S
    obtain ⟨k, -, hk⟩ := h.p11.exists_conj_M _ (h.p11.ZN_le_M hx₀Z) x hx hx₀P hx₀M hxP hxM
    exact (isConj_iff.mpr ⟨k, hk⟩).symm.trans (isConj_iff.mpr ⟨g, hg⟩).symm

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
