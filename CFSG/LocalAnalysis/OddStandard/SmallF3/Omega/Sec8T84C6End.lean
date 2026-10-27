module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Inv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Ord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Cen

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

variable {G : Type} [Group G] {E B : Subgroup G} {u : MulAut ↥E}
  {A H P : Subgroup (MulAut ↥E)}

private lemma pow_apply_of_fixed {X : Type*} [Group X] {g : MulAut X} {y : X}
    (h : g y = y) : ∀ n : ℕ, (g ^ n) y = y := by
  intro n
  induction n with
  | zero => rw [pow_zero, MulAut.one_apply]
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

private lemma pow_eq_self_of_sq_eq_one {X : Type*} [Group X] {a : X} (h2 : a * a = 1)
    {n : ℕ} (hn : Odd n) : a ^ n = a := by
  obtain ⟨k, rfl⟩ := hn
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact h2
  rw [pow_succ, pow_mul, ha2, one_pow, one_mul]

theorem HCtx.comm_A_P (hA5 : Sec8T84FactA5) (S : HCtx E B u A H) (O : OddNormal H P) :
    ∀ a ∈ A, ∀ p ∈ P, a * p = p * a := by
  haveI := O.finite
  exact A_comm_P S.A_iso (fun a ha p hp => O.norm a (S.A_H ha) p hp) (S.comm_P O)
    (HCtx.card_P_dvd hA5 S O)

theorem HCtx.exists_fix_not_mem (hA5 : Sec8T84FactA5) (hInv : Sec8T84FactInv)
    (S : HCtx E B u A H) (O : OddNormal H P) (hc : ∀ h ∈ H, h * u * h⁻¹ * u⁻¹ ∈ P)
    {a₀ : MulAut ↥E} (ha₀ : a₀ ∈ A) (h1 : a₀ ≠ 1) (h2 : a₀ * a₀ = 1) :
    ∃ y : ↥E, (u * a₀) y = y ∧ ∀ h ∈ H, ∀ b : ↥E, (b : G) ∈ B → h b ≠ y := by
  classical
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [S.hE.2]; norm_num)
  by_contra hcon
  push Not at hcon
  have hmem : ∀ y : ↥E, (u * a₀) y = y → (y : G) ∈ B ∧ a₀ y = y := by
    intro y hy
    obtain ⟨h, hh, b, hbB, hby⟩ := hcon y hy
    set q : MulAut ↥E := h * u * h⁻¹ * u⁻¹ with hq_def
    have hqP : q ∈ P := by rw [hq_def]; exact hc h hh
    have hcomm_aq : a₀ * q = q * a₀ := HCtx.comm_A_P hA5 S O a₀ ha₀ q hqP
    have hcomm_au : a₀ * u = u * a₀ := S.A_comm a₀ ha₀
    have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right S.u_sq
    have hinv_q : u * q * u⁻¹ = q⁻¹ := HCtx.inv_P S O q hqP
    have hub : u b = b := (S.fix b).mpr hbB
    have hb_eq : h⁻¹ y = b := by
      rw [← hby, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have hhuy : (h * u * h⁻¹) y = y := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hb_eq, hub, hby]
    have hconj_eq : h * u * h⁻¹ = q * u := by
      rw [hq_def]; group
    have hqu_y : (q * u) y = y := by
      rw [← hconj_eq]; exact hhuy
    have hαq : (u * a₀) * (q * u) = q⁻¹ * a₀ := by
      calc (u * a₀) * (q * u) = u * (a₀ * q) * u := by group
        _ = u * (q * a₀) * u := by rw [hcomm_aq]
        _ = u * q * (a₀ * u) := by group
        _ = u * q * (u * a₀) := by rw [hcomm_au]
        _ = (u * q * u) * a₀ := by group
        _ = (u * q * u⁻¹) * a₀ := by rw [hu_inv]
        _ = q⁻¹ * a₀ := by rw [hinv_q]
    have hαfix : ((u * a₀) * (q * u)) y = y := by
      rw [MulAut.mul_apply, hqu_y, hy]
    have hqia_y : (q⁻¹ * a₀) y = y := by
      rw [← hαq]; exact hαfix
    have hqn : q ^ Nat.card ↥P = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard P hqP)
    have hqinv : (q⁻¹) ^ Nat.card ↥P = 1 := by rw [inv_pow, hqn, inv_one]
    have hpow_a : a₀ ^ Nat.card ↥P = a₀ := pow_eq_self_of_sq_eq_one h2 O.odd
    have hcomm_aq' : Commute a₀ q := (commute_iff_eq a₀ q).mpr hcomm_aq
    have hqi_comm : Commute q⁻¹ a₀ := hcomm_aq'.symm.inv_left
    have hpow_eq : (q⁻¹ * a₀) ^ Nat.card ↥P = a₀ := by
      rw [hqi_comm.mul_pow (Nat.card ↥P), hqinv, hpow_a, one_mul]
    have ha0fix : a₀ y = y := by
      have h := pow_apply_of_fixed hqia_y (Nat.card ↥P)
      rwa [hpow_eq] at h
    have hualpha : u (a₀ y) = y := by
      have h := hy
      rwa [MulAut.mul_apply] at h
    have huy : u y = y := by rw [ha0fix] at hualpha; exact hualpha
    exact ⟨(S.fix y).mp huy, ha0fix⟩
  have hαH : u * a₀ ∈ H := H.mul_mem S.u_H (S.A_H ha₀)
  have hα1 : u * a₀ ≠ 1 := by
    intro h
    apply S.u_A
    have hu : u = a₀⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hu]
    exact A.inv_mem ha₀
  have hα2 : (u * a₀) * (u * a₀) = 1 := by
    calc (u * a₀) * (u * a₀) = u * (a₀ * u) * a₀ := by group
      _ = u * (u * a₀) * a₀ := by rw [S.A_comm a₀ ha₀]
      _ = (u * u) * (a₀ * a₀) := by group
      _ = 1 := by rw [S.u_sq, h2, one_mul]
  have h16 := HCtx.card_fix_of_invol hInv S O hc hαH hα1 hα2
  have h4 := HCtx.card_fixB_of_inv hInv S ha₀ h1 h2
  have hinj : Function.Injective
      (fun e : {e : ↥E // (u * a₀) e = e} =>
        (⟨e.1, hmem e.1 e.2⟩ : {e : ↥E // (e : G) ∈ B ∧ a₀ e = e})) := by
    intro x y hxy
    exact Subtype.ext (congrArg
      (fun z : {e : ↥E // (e : G) ∈ B ∧ a₀ e = e} => (z : ↥E)) hxy)
  have hle : Nat.card {e : ↥E // (u * a₀) e = e} ≤
      Nat.card {e : ↥E // (e : G) ∈ B ∧ a₀ e = e} :=
    Nat.card_le_card_of_injective _ hinj
  rw [h16, h4] at hle
  omega

end C10

end CFSG.OddStandard.SmallF3.Omega
