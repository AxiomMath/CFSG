module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Q

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup

namespace S56

variable {Γ : Type*} [Group Γ]

theorem exists_commSubgroup {E Z : Subgroup Γ} (n : Γ) (hZE : Z ≤ E)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∃ D : Subgroup Γ, ∀ e, e ∈ D ↔ e ∈ E ∧ n * e * n⁻¹ * e⁻¹ ∈ Z := by
  refine ⟨{ carrier := {e | e ∈ E ∧ n * e * n⁻¹ * e⁻¹ ∈ Z}
            one_mem' := ⟨one_mem _, by simpa using one_mem Z⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun e => Iff.rfl⟩
  · rintro e e' ⟨heE, he⟩ ⟨he'E, he'⟩
    refine ⟨mul_mem heE he'E, ?_⟩
    have h1 : e * (n * e' * n⁻¹ * e'⁻¹) * e⁻¹ = n * e' * n⁻¹ * e'⁻¹ := by
      rw [hEc e heE _ (hZE he')]
      group
    have h2 : n * (e * e') * n⁻¹ * (e * e')⁻¹ =
        (n * e * n⁻¹ * e⁻¹) * (e * (n * e' * n⁻¹ * e'⁻¹) * e⁻¹) := by group
    rw [h2, h1]
    exact mul_mem he he'
  · rintro e ⟨heE, he⟩
    refine ⟨inv_mem heE, ?_⟩
    have h1 : n * e⁻¹ * n⁻¹ * e⁻¹⁻¹ = e⁻¹ * (n * e * n⁻¹ * e⁻¹)⁻¹ * e := by group
    have hc := hEc e heE _ (hZE (inv_mem he))
    have h2 : e⁻¹ * (n * e * n⁻¹ * e⁻¹)⁻¹ * e = (n * e * n⁻¹ * e⁻¹)⁻¹ := by
      calc e⁻¹ * (n * e * n⁻¹ * e⁻¹)⁻¹ * e = e⁻¹ * ((n * e * n⁻¹ * e⁻¹)⁻¹ * e) := by group
        _ = e⁻¹ * (e * (n * e * n⁻¹ * e⁻¹)⁻¹) := by rw [hc]
        _ = (n * e * n⁻¹ * e⁻¹)⁻¹ := by group
    rw [h1, h2]
    exact inv_mem he

theorem comm_of_pow_five_of_comm_mem {Z : Subgroup Γ} {y e : Γ} (hZsq : ∀ w ∈ Z, w * w = 1)
    (hyZ : ∀ w ∈ Z, y * w = w * y) (hy : y ^ 5 = 1) (he : y * e * y⁻¹ * e⁻¹ ∈ Z) :
    y * e = e * y := by
  obtain ⟨w, hw⟩ : ∃ w, w = y * e * y⁻¹ * e⁻¹ := ⟨_, rfl⟩
  rw [← hw] at he
  have hye : y * e * y⁻¹ = w * e := by rw [hw]; group
  have hwy : Commute y w := hyZ w he
  have hk : ∀ k : ℕ, y ^ k * e * (y ^ k)⁻¹ = w ^ k * e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : y * w ^ k * y⁻¹ = w ^ k := by
        rw [(hwy.pow_right k).eq]
        group
      calc y ^ (k + 1) * e * (y ^ (k + 1))⁻¹
          = y * (y ^ k * e * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = (y * w ^ k * y⁻¹) * (y * e * y⁻¹) := by rw [ih]; group
        _ = w ^ (k + 1) * e := by rw [h1, hye]; group
  have h5 := hk 5
  have hww := hZsq w he
  have hw5 : w ^ 5 = w := by
    calc w ^ 5 = w * w * (w * w) * w := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = w := by rw [hww]; group
  rw [hy, hw5] at h5
  have hw1 : w = 1 := by simpa using h5.symm
  rw [hw1] at hye
  calc y * e = (y * e * y⁻¹) * y := by group
    _ = e * y := by rw [hye]; group

theorem mem_of_comm_mem_zpowers [Finite Γ] {E Z : Subgroup Γ} {x y e : Γ}
    (hZsq : ∀ w ∈ Z, w * w = 1) (hyZ : ∀ w ∈ Z, y * w = w * y) (hx : orderOf x = 5)
    (hfix : ∀ e ∈ E, e * x = x * e → e ∈ Z) (hy : y ∈ zpowers x) (hy1 : y ≠ 1) (heE : e ∈ E)
    (he : y * e * y⁻¹ * e⁻¹ ∈ Z) : e ∈ Z := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hy5 : y ^ 5 = 1 := by
    have h := orderOf_dvd_of_mem_zpowers hy
    rw [hx] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  have hyo : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  have hzp : zpowers y = zpowers x :=
    eq_of_le_of_card_ge (zpowers_le.2 hy) (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hyo])
  obtain ⟨k, hk⟩ : x ∈ zpowers y := hzp ▸ mem_zpowers x
  have hc : y * e = e * y := comm_of_pow_five_of_comm_mem hZsq hyZ hy5 he
  refine hfix e heE ?_
  rw [← hk]
  exact (Commute.zpow_right (show Commute e y from hc.symm) k).eq

theorem comm_comm_conj {n x h b : Γ} (hb : b = n * h * n⁻¹ * h⁻¹) (hnb : n * b = b * n)
    (hxb : x * b = b * x) :
    (n * x * n⁻¹ * x⁻¹) * (x * h * x⁻¹) * (n * x * n⁻¹ * x⁻¹)⁻¹ * (x * h * x⁻¹)⁻¹ =
      b⁻¹ * (n * (x * h * x⁻¹) * n⁻¹ * (x * h * x⁻¹)⁻¹) := by
  have hnh : n * h * n⁻¹ = b * h := by rw [hb]; group
  have hbn : n⁻¹ * b * n = b := by
    calc n⁻¹ * b * n = n⁻¹ * (b * n) := by group
      _ = n⁻¹ * (n * b) := by rw [hnb]
      _ = b := by group
  have h1 : n⁻¹ * h * n = b⁻¹ * h := by
    calc n⁻¹ * h * n = b⁻¹ * (n⁻¹ * b * n) * (n⁻¹ * h * n) := by rw [hbn]; group
      _ = b⁻¹ * (n⁻¹ * (b * h) * n) := by group
      _ = b⁻¹ * (n⁻¹ * (n * h * n⁻¹) * n) := by rw [hnh]
      _ = b⁻¹ * h := by group
  have h2 : x * b⁻¹ * x⁻¹ = b⁻¹ := by
    rw [(Commute.inv_right (show Commute x b from hxb)).eq]
    group
  have h3 : n * b⁻¹ * n⁻¹ = b⁻¹ := by
    rw [(Commute.inv_right (show Commute n b from hnb)).eq]
    group
  calc (n * x * n⁻¹ * x⁻¹) * (x * h * x⁻¹) * (n * x * n⁻¹ * x⁻¹)⁻¹ * (x * h * x⁻¹)⁻¹
      = n * x * (n⁻¹ * h * n) * x⁻¹ * n⁻¹ * (x * h * x⁻¹)⁻¹ := by group
    _ = n * x * (b⁻¹ * h) * x⁻¹ * n⁻¹ * (x * h * x⁻¹)⁻¹ := by rw [h1]
    _ = n * (x * b⁻¹ * x⁻¹) * (x * h * x⁻¹) * n⁻¹ * (x * h * x⁻¹)⁻¹ := by group
    _ = (n * b⁻¹ * n⁻¹) * (n * (x * h * x⁻¹) * n⁻¹ * (x * h * x⁻¹)⁻¹) := by rw [h2]; group
    _ = b⁻¹ * (n * (x * h * x⁻¹) * n⁻¹ * (x * h * x⁻¹)⁻¹) := by rw [h3]

theorem hyper_comm_x [Finite Γ] {E Z M H : Subgroup Γ} {x n : Γ}
    (hZsq : ∀ w ∈ Z, w * w = 1) (hZcard : Nat.card Z = 2) (hE : Nat.card E = 32)
    (hMN : M ≤ normalizer (E : Set Γ)) (hMZ : ∀ g ∈ M, ∀ w ∈ Z, g * w = w * g)
    (hx : orderOf x = 5) (hxM : x ∈ M) (hfix : ∀ e ∈ E, e * x = x * e → e ∈ Z)
    (hnM : n ∈ M) (hnx : n * x * n⁻¹ ∈ zpowers x) (hHE : H ≤ E) (hH : H.relIndex E ≤ 2)
    (hHn : ∀ h ∈ H, n * h * n⁻¹ * h⁻¹ ∈ Z) : n * x = x * n := by
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, y = n * x * n⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hy1 : y ≠ 1 := by
    intro h1
    apply hne
    rw [hy] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hyX : y ∈ zpowers x := by
    rw [hy]
    exact mul_mem hnx (inv_mem (mem_zpowers x))
  have hyM : y ∈ M := by
    rw [hy]
    exact mul_mem (mul_mem (mul_mem hnM hxM) (inv_mem hnM)) (inv_mem hxM)
  obtain ⟨H', hH'⟩ : ∃ H' : Subgroup Γ, H' = H.map (MulAut.conj x : Γ →* Γ) := ⟨_, rfl⟩
  have hEx : E.map (MulAut.conj x : Γ →* Γ) = E := mem_normalizer_iff_map_conj_eq.1 (hMN hxM)
  have hH'E : H' ≤ E := by
    rw [hH']
    have h := map_mono (f := (MulAut.conj x : Γ →* Γ)) hHE
    rwa [hEx] at h
  have hH'idx : H'.relIndex E ≤ 2 := by
    have h := relIndex_map_map_of_injective H E (f := (MulAut.conj x : Γ →* Γ))
      (MulAut.conj x).injective
    rw [hEx, ← hH'] at h
    exact h.le.trans hH
  have hidx : (H ⊓ H').relIndex E ≤ 4 := relIndex_inf_le.trans (Nat.mul_le_mul hH hH'idx)
  have hcard : 8 ≤ Nat.card (H ⊓ H' : Subgroup Γ) := by
    have h := relIndex_mul_card (H := H ⊓ H') (K := E)
    rw [inf_eq_left.2 (inf_le_left.trans hHE), hE] at h
    have h' := Nat.mul_le_mul_right (Nat.card (H ⊓ H' : Subgroup Γ)) hidx
    omega
  have hle : (H ⊓ H' : Subgroup Γ) ≤ Z := by
    intro e he
    obtain ⟨heH, heH'⟩ := mem_inf.1 he
    obtain ⟨h, hhH, hhe⟩ := mem_map.1 (hH' ▸ heH')
    have hhe' : e = x * h * x⁻¹ := by rw [← hhe]; simp [MulAut.conj_apply]
    have hb := hHn h hhH
    have ha := hHn e heH
    have key := comm_comm_conj (n := n) (x := x) (h := h) (b := n * h * n⁻¹ * h⁻¹) rfl
      (hMZ n hnM _ hb) (hMZ x hxM _ hb)
    rw [← hhe', ← hy] at key
    refine mem_of_comm_mem_zpowers hZsq (hMZ y hyM) hx hfix hyX hy1 (hH'E heH') ?_
    rw [key]
    exact mul_mem (inv_mem hb) ha
  have h2 := card_le_of_le hle
  omega

theorem hyper_comm_mem [Finite Γ] {E Z M H : Subgroup Γ} {x n : Γ} (hZE : Z ≤ E)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hZsq : ∀ w ∈ Z, w * w = 1)
    (hZcard : Nat.card Z = 2) (hE : Nat.card E = 32) (hMN : M ≤ normalizer (E : Set Γ))
    (hMZ : ∀ g ∈ M, ∀ w ∈ Z, g * w = w * g) (hx : orderOf x = 5) (hxM : x ∈ M)
    (hfix : ∀ e ∈ E, e * x = x * e → e ∈ Z) (hnM : n ∈ M) (hnx : n * x * n⁻¹ ∈ zpowers x)
    (hHE : H ≤ E) (hH : H.relIndex E ≤ 2) (hHn : ∀ h ∈ H, n * h * n⁻¹ * h⁻¹ ∈ Z) :
    ∀ e ∈ E, n * e * n⁻¹ * e⁻¹ ∈ Z := by
  have hnx' : n * x = x * n :=
    hyper_comm_x hZsq hZcard hE hMN hMZ hx hxM hfix hnM hnx hHE hH hHn
  obtain ⟨D, hD⟩ := exists_commSubgroup n hZE hEc
  have hHD : H ≤ D := fun h hh => (hD h).2 ⟨hHE hh, hHn h hh⟩
  have hDE : D ≤ E := fun e he => ((hD e).1 he).1
  have hZD : Z ≤ D := fun w hw => (hD w).2 ⟨hZE hw, by
    have h1 : n * w * n⁻¹ * w⁻¹ = 1 := by rw [hMZ n hnM w hw]; group
    rw [h1]
    exact one_mem Z⟩
  have hDidx : D.relIndex E ≤ 2 := by
    have hne : H.relIndex E ≠ 0 := by
      intro h0
      have h := relIndex_mul_card (H := H) (K := E)
      rw [h0, hE] at h
      omega
    exact (relIndex_le_of_le_left hHD hne).trans hH
  have hconj : ∀ g ∈ M, n * g = g * n → ∀ e ∈ D, g * e * g⁻¹ ∈ D := by
    intro g hgM hng e he
    obtain ⟨heE, hne⟩ := (hD e).1 he
    refine (hD _).2 ⟨(mem_normalizer_iff.1 (hMN hgM) e).1 heE, ?_⟩
    have hgn : g⁻¹ * n⁻¹ * g = n⁻¹ := by
      calc g⁻¹ * n⁻¹ * g = g⁻¹ * (n⁻¹ * g) := by group
        _ = g⁻¹ * (g * n⁻¹) := by rw [(Commute.inv_left (show Commute n g from hng)).eq]
        _ = n⁻¹ := by group
    have e1 : n * (g * e * g⁻¹) * n⁻¹ * (g * e * g⁻¹)⁻¹ = g * (n * e * n⁻¹ * e⁻¹) * g⁻¹ := by
      calc n * (g * e * g⁻¹) * n⁻¹ * (g * e * g⁻¹)⁻¹
          = (n * g) * e * (g⁻¹ * n⁻¹ * g) * e⁻¹ * g⁻¹ := by group
        _ = (g * n) * e * n⁻¹ * e⁻¹ * g⁻¹ := by rw [hng, hgn]
        _ = g * (n * e * n⁻¹ * e⁻¹) * g⁻¹ := by group
    have e2 : g * (n * e * n⁻¹ * e⁻¹) * g⁻¹ = n * e * n⁻¹ * e⁻¹ := by
      rw [hMZ g hgM _ hne]
      group
    rw [e1, e2]
    exact hne
  have hxD : x ∈ normalizer (D : Set Γ) := by
    rw [mem_normalizer_iff]
    intro e
    refine ⟨fun he => hconj x hxM hnx' e he, fun he => ?_⟩
    have h := hconj x⁻¹ (inv_mem hxM)
      (by rw [(Commute.inv_right (show Commute n x from hnx')).eq]) _ he
    simpa [mul_assoc] using h
  have hxZ : x ∈ normalizer (Z : Set Γ) := by
    apply Subgroup.centralizer_le_normalizer (Z : Set Γ)
    rw [mem_centralizer_iff]
    intro w hw
    exact (hMZ x hxM w hw).symm
  have hmod := card_modEq_of_centralizer_le hx hZD hDE hxZ hxD
    (fun c hc hcx => hfix c hc hcx.symm)
  rw [hZcard] at hmod
  have hDcard : D.relIndex E * Nat.card D = 32 := by
    have h := relIndex_mul_card (H := D) (K := E)
    rwa [inf_eq_left.2 hDE, hE] at h
  have h1 : D.relIndex E = 1 := by
    have hcm : Nat.card D % 5 = 2 := hmod
    generalize D.relIndex E = r at hDidx hDcard ⊢
    generalize Nat.card D = c at hDcard hcm
    interval_cases r <;> omega
  intro e he
  exact ((hD e).1 (relIndex_eq_one.1 h1 he)).2

end S56

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_mem_Q0_of_cent_hyperplane (h49 : d.Thm49Statement) (hd : d.Hyp) {m : G}
    (hm : m ∈ d.M) {H : Subgroup G} (hHE : H ≤ d.E) (hH : H.relIndex d.E ≤ 2)
    (hcen : ∀ h ∈ H, m * h = h * m) : m ∈ d.s56Q0 := by
  obtain ⟨hQ0, hN⟩ := (⟨hd.s56_Q0_le_M h49, s56_M_le_normalizer_Q0 d⟩ :
    d.s56Q0 ≤ d.M ∧ d.M ≤ normalizer (d.s56Q0 : Set G))
  obtain ⟨-, -, -, -, -, h20, -⟩ := hd.s56_structure_M h49
  obtain ⟨q, hq, n, hnM, hnX, rfl⟩ := S56.exists_mul_normalizer_of_index_twenty hQ0 hN
    (s56_Q0_isPGroup d) hd.s56_x5_mem_M hd.s56_orderOf_x5 h20 hm
  have hHn : ∀ h ∈ H, n * h * n⁻¹ * h⁻¹ ∈ zpowers d.z := fun h hh => by
    have e1 : n * h * n⁻¹ * h⁻¹ = q⁻¹ * h * q⁻¹⁻¹ * h⁻¹ := by
      calc n * h * n⁻¹ * h⁻¹ = q⁻¹ * (q * n * h) * n⁻¹ * h⁻¹ := by group
        _ = q⁻¹ * (h * (q * n)) * n⁻¹ * h⁻¹ := by rw [hcen h hh]
        _ = q⁻¹ * h * q⁻¹⁻¹ * h⁻¹ := by group
    rw [e1]
    exact ((hd.s56_mem_Q0_iff h49).1 (inv_mem hq)).2 h (hHE hh)
  have hzcard : Nat.card (zpowers d.z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hd.s56_z_sq) hd.s56_z_ne_one
  have hnx : n * d.x₅ * n⁻¹ ∈ zpowers d.x₅ :=
    (mem_normalizer_iff.1 hnX d.x₅).1 (mem_zpowers _)
  have hcomm := S56.hyper_comm_mem (zpowers_le.2 hd.s56_z_mem_E)
    (fun a ha b hb => hd.s56_E_comm ha hb) (fun w hw => hd.s56_zpowers_sq hw) hzcard
    hd.A_facts.1 hd.s56_ME (fun g hg w hw => hd.s56_M_comm_zpowers hg hw) hd.s56_orderOf_x5
    hd.s56_x5_mem_M (fun e he hc => hd.s56_E_cent_x5 he hc) hnM hnx hHE hH hHn
  exact mul_mem hq ((hd.s56_mem_Q0_iff h49).2 ⟨hnM, hcomm⟩)

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
