module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Tors
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Ker
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

structure HCtx {G : Type} [Group G] (E B : Subgroup G) (u : MulAut ↥E)
    (A H : Subgroup (MulAut ↥E)) : Prop where
  hE : IsElemAb2 E 8
  hB : IsElemAb2 B 4
  hBE : B ≤ E
  u_sq : u * u = 1
  fix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B
  A_iso : Nonempty (↥A ≃* alternatingGroup (Fin 6))
  A_comm : ∀ a ∈ A, a * u = u * a
  A_faith : ∀ a ∈ A, (∀ e : ↥E, (e : G) ∈ B → a e = e) → a = 1
  u_H : u ∈ H
  A_H : A ≤ H
  u_A : u ∉ A
  cent : ∀ c ∈ H, c * u = u * c → c ∈ A ⊔ zpowers u

structure OddNormal {Γ : Type} [Group Γ] (H P : Subgroup Γ) : Prop where
  le : P ≤ H
  norm : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P
  odd : Odd (Nat.card ↥P)

variable {G : Type} [Group G] {E B : Subgroup G} {u : MulAut ↥E}
  {A H P : Subgroup (MulAut ↥E)}

theorem OddNormal.finite {Γ : Type} [Group Γ] {H P : Subgroup Γ} (O : OddNormal H P) :
    Finite ↥P :=
  Nat.finite_of_card_ne_zero O.odd.pos.ne'

theorem HCtx.inf_A_P (S : HCtx E B u A H) (O : OddNormal H P) : A ⊓ P = ⊥ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥A := by
    obtain ⟨φ⟩ := S.A_iso
    exact φ.isSimpleGroup
  have hKnormal : ((A ⊓ P).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (H := A ⊓ P) (K := A) inf_le_left]
    intro h k hh hk
    exact ⟨A.mul_mem (A.mul_mem hk hh.1) (A.inv_mem hk),
      O.norm k (S.A_H hk) h hh.2⟩
  haveI : ((A ⊓ P).subgroupOf A).Normal := hKnormal
  rcases Subgroup.Normal.eq_bot_or_eq_top ((A ⊓ P).subgroupOf A) with hbot | htop
  · refine (Subgroup.eq_bot_iff_forall (A ⊓ P)).mpr ?_
    intro x hx
    have hxK : (⟨x, hx.1⟩ : ↥A) ∈ (⊥ : Subgroup ↥A) := by
      rw [← hbot]
      exact Subgroup.mem_subgroupOf.mpr hx
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxK)
  · exfalso
    have hAP : A ≤ A ⊓ P := by
      intro a ha
      have : (⟨a, ha⟩ : ↥A) ∈ (A ⊓ P).subgroupOf A := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have hAleP : A ≤ P := le_trans hAP inf_le_right
    have hdvd : Nat.card ↥A ∣ Nat.card ↥P := Subgroup.card_dvd_of_le hAleP
    have hA360 : Nat.card ↥A = 360 := by
      obtain ⟨φ⟩ := S.A_iso
      rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have h2 : 2 ∣ Nat.card ↥A := by rw [hA360]; decide
    obtain ⟨k, hk⟩ := O.odd
    obtain ⟨j, hj⟩ := dvd_trans h2 hdvd
    omega

theorem HCtx.cent_P (S : HCtx E B u A H) (O : OddNormal H P) :
    ∀ p ∈ P, p * u = u * p → p = 1 := by
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [S.hE.2]; norm_num)
  have hAcomm : ∀ a ∈ A, ∀ v ∈ zpowers u, a * v = v * a := by
    intro a ha v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact Commute.zpow_right (show Commute a u from S.A_comm a ha) i
  intro p hp hpu
  obtain ⟨a, ha, v, hv, hpav⟩ :=
    A3.exists_mul_of_comm hAcomm (S.cent p (O.le hp) hpu)
  have hcases : v = 1 ∨ v = u := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have h2 : orderOf u = 2 := by
      have hdvd : orderOf u ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact S.u_sq)
      have hne1 : orderOf u ≠ 1 := by
        intro h
        exact S.u_A (by rw [orderOf_eq_one_iff.mp h]; exact A.one_mem)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have h3 : u ^ (i % (orderOf u : ℤ)) = u ^ i := zpow_mod_orderOf u i
    rw [h2] at h3
    push_cast at h3
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · left; rw [← h3, h]; simp
    · right; rw [← h3, h]; simp
  rcases hcases with hv1 | hvu
  · have hpA : p ∈ A := by simpa [hpav, hv1] using ha
    have : p ∈ (⊥ : Subgroup (MulAut ↥E)) := by
      rw [← HCtx.inf_A_P S O]
      exact ⟨hpA, hp⟩
    exact Subgroup.mem_bot.mp this
  · have hpp_eq : p * p = a * a := by
      rw [hpav, hvu]
      calc (a * u) * (a * u) = a * (u * a) * u := by group
        _ = a * (a * u) * u := by rw [← S.A_comm a ha]
        _ = (a * a) * (u * u) := by group
        _ = a * a := by rw [S.u_sq, mul_one]
    have hppA : p * p ∈ A := by rw [hpp_eq]; exact A.mul_mem ha ha
    have hppP : p * p ∈ P := P.mul_mem hp hp
    have hpp1 : p * p = 1 := by
      have : p * p ∈ (⊥ : Subgroup (MulAut ↥E)) := by
        rw [← HCtx.inf_A_P S O]
        exact ⟨hppA, hppP⟩
      exact Subgroup.mem_bot.mp this
    have hdvd2 : orderOf p ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hpp1)
    have hne2 : orderOf p ≠ 2 :=
      O.odd.ne_two_of_dvd_nat (Subgroup.orderOf_dvd_natCard P hp)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd h hne2

theorem HCtx.inv_P (S : HCtx E B u A H) (O : OddNormal H P) :
    ∀ p ∈ P, u * p * u⁻¹ = p⁻¹ := by
  haveI := O.finite
  exact inv_of_fixedPointFree P u S.u_sq (fun p hp => O.norm u S.u_H p hp) (HCtx.cent_P S O)

theorem HCtx.comm_P (S : HCtx E B u A H) (O : OddNormal H P) :
    ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := by
  haveI := O.finite
  exact comm_of_fixedPointFree P u S.u_sq (fun p hp => O.norm u S.u_H p hp) (HCtx.cent_P S O)

theorem HCtx.exists_decomp (S : HCtx E B u A H) (O : OddNormal H P)
    (hc : ∀ h ∈ H, h * u * h⁻¹ * u⁻¹ ∈ P) :
    ∀ h ∈ H, ∃ p ∈ P, ∃ c ∈ H, c * u = u * c ∧ h = p * c := by
  intro h hh
  set q : MulAut ↥E := h * u * h⁻¹ * u⁻¹ with hq_def
  have hq : q ∈ P := by rw [hq_def]; exact hc h hh
  have hqn : q ^ Nat.card ↥P = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard P hq)
  set e : ℕ := (Nat.card ↥P + 1) / 2 with he_def
  have h2n : 2 * e = Nat.card ↥P + 1 := by
    obtain ⟨k, hk⟩ := O.odd
    rw [he_def, hk]
    omega
  have hq_sq : q ^ e * q ^ e = q := by
    rw [← pow_add, ← two_mul, h2n, pow_succ, hqn, one_mul]
  have hpu : u * (q ^ e)⁻¹ * u⁻¹ = q ^ e := by
    have hmem : q ^ e ∈ P := P.pow_mem hq e
    have hinv := HCtx.inv_P S O (q ^ e) hmem
    calc u * (q ^ e)⁻¹ * u⁻¹ = (u * q ^ e * u⁻¹)⁻¹ := by group
      _ = ((q ^ e)⁻¹)⁻¹ := by rw [hinv]
      _ = q ^ e := by group
  have hconj : q ^ e * u * (q ^ e)⁻¹ = h * u * h⁻¹ := by
    have h1 : q ^ e * u * (q ^ e)⁻¹ = q ^ e * (u * (q ^ e)⁻¹ * u⁻¹) * u := by group
    rw [h1, hpu]
    have h2 : q * u = h * u * h⁻¹ := by rw [hq_def]; group
    rw [hq_sq, h2]
  refine ⟨q ^ e, P.pow_mem hq e, (q ^ e)⁻¹ * h, ?_, ?_, ?_⟩
  · exact H.mul_mem (H.inv_mem (O.le (P.pow_mem hq e))) hh
  · have hcu : ((q ^ e)⁻¹ * h) * u * ((q ^ e)⁻¹ * h)⁻¹ = u := by
      calc ((q ^ e)⁻¹ * h) * u * ((q ^ e)⁻¹ * h)⁻¹
          = (q ^ e)⁻¹ * (h * u * h⁻¹) * (q ^ e) := by group
        _ = (q ^ e)⁻¹ * (q ^ e * u * (q ^ e)⁻¹) * (q ^ e) := by rw [← hconj]
        _ = u := by group
    calc ((q ^ e)⁻¹ * h) * u
        = (((q ^ e)⁻¹ * h) * u * ((q ^ e)⁻¹ * h)⁻¹) * ((q ^ e)⁻¹ * h) := by group
      _ = u * ((q ^ e)⁻¹ * h) := by rw [hcu]
  · group

theorem HCtx.exists_invol_conj (S : HCtx E B u A H) (O : OddNormal H P)
    (hc : ∀ h ∈ H, h * u * h⁻¹ * u⁻¹ ∈ P) {h : MulAut ↥E} (hh : h ∈ H) (hh2 : h * h = 1)
    (hh1 : h ≠ 1) :
    ∃ g ∈ H, ∃ c ∈ H, c * u = u * c ∧ c * c = 1 ∧ c ≠ 1 ∧ h = g * c * g⁻¹ := by
  obtain ⟨p, hp, c, hcH, hcu, hpc⟩ := S.exists_decomp O hc h hh
  have hpp : p * c * p * c = 1 := by
    have h := hh2
    rw [hpc] at h
    simpa only [mul_assoc] using h
  have hconj_cc : p * (c * p * c⁻¹) = (c * c)⁻¹ := by
    have h : p * (c * p * c⁻¹) = (p * c * p * c) * (c * c)⁻¹ := by group
    rw [h, hpp, one_mul]
  have hcc_eq : c * c = (p * (c * p * c⁻¹))⁻¹ := by rw [hconj_cc, inv_inv]
  have hccP : c * c ∈ P := by
    rw [hcc_eq]
    exact P.inv_mem (P.mul_mem hp (O.norm c hcH p hp))
  have hcc_comm : (c * c) * u = u * (c * c) := by
    calc (c * c) * u = c * (c * u) := by group
      _ = c * (u * c) := by rw [hcu]
      _ = (c * u) * c := by group
      _ = (u * c) * c := by rw [hcu]
      _ = u * (c * c) := by group
  have hcc1 : c * c = 1 := HCtx.cent_P S O (c * c) hccP hcc_comm
  have hc_ne : c ≠ 1 := by
    intro hc1
    have hhP : h ∈ P := by simpa [hpc, hc1] using hp
    have hdvd2 : orderOf h ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hh2)
    have hne2 : orderOf h ≠ 2 :=
      O.odd.ne_two_of_dvd_nat (Subgroup.orderOf_dvd_natCard P hhP)
    have hh_eq1 : h = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd h1 hne2
    exact hh1 hh_eq1
  have hc_inv : c⁻¹ = c := by
    calc c⁻¹ = c⁻¹ * 1 := by group
      _ = c⁻¹ * (c * c) := by rw [hcc1]
      _ = (c⁻¹ * c) * c := by group
      _ = c := by group
  have hcp : c * p * c⁻¹ = p⁻¹ := by
    have h1 : c * p * c = p⁻¹ := by
      have h2 := congrArg (fun z => p⁻¹ * z) hpp
      simpa [mul_assoc] using h2
    rw [hc_inv]
    exact h1
  set e : ℕ := (Nat.card ↥P + 1) / 2 with he_def
  have h2n : 2 * e = Nat.card ↥P + 1 := by
    obtain ⟨k, hk⟩ := O.odd
    rw [he_def, hk]
    omega
  have hpn : p ^ Nat.card ↥P = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard P hp)
  have hr_sq : p ^ e * p ^ e = p := by
    rw [← pow_add, ← two_mul, h2n, pow_succ, hpn, one_mul]
  have hcr : c * p ^ e * c⁻¹ = (p ^ e)⁻¹ := by rw [← conj_pow, hcp, inv_pow]
  have hfinal : p ^ e * c * (p ^ e)⁻¹ = h := by
    have h1 : p ^ e * c * (p ^ e)⁻¹ = p ^ e * (c * (p ^ e)⁻¹ * c⁻¹) * c := by group
    rw [h1]
    have h2 : c * (p ^ e)⁻¹ * c⁻¹ = p ^ e := by
      rw [show c * (p ^ e)⁻¹ * c⁻¹ = (c * p ^ e * c⁻¹)⁻¹ by group]
      rw [hcr, inv_inv]
    rw [h2, hr_sq, hpc]
  exact ⟨p ^ e, O.le (P.pow_mem hp e), c, hcH, hcu, hcc1, hc_ne, hfinal.symm⟩

end C10

end CFSG.OddStandard.SmallF3.Omega
