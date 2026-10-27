module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Ord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Prm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Tr

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

variable {G : Type} [Group G] {E B : Subgroup G} {u : MulAut ↥E}
  {A H P : Subgroup (MulAut ↥E)}

theorem dvd_2295_of_dvd_prod {n : ℕ} (hodd : Odd n) (hp : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ 255)
    (hd : 720 * n ∣ ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ))) : n ∣ 2295 := by
  have hprod : (∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)))
      = 720 * (2 ^ 24 * (3 ^ 3 * 5 * 7 ^ 2 * 17 * 31 * 127)) := by
    norm_num [Fin.prod_univ_eight]
  rw [hprod] at hd
  have hn : n ∣ 2 ^ 24 * (3 ^ 3 * 5 * 7 ^ 2 * 17 * 31 * 127) :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 720) hd
  have hcop2 : Nat.Coprime n (2 ^ 24) :=
    Nat.Coprime.pow_right 24 hodd.coprime_two_right
  have hn' : n ∣ 3 ^ 3 * 5 * 7 ^ 2 * 17 * 31 * 127 := hcop2.dvd_of_dvd_mul_left hn
  rw [show 3 ^ 3 * 5 * 7 ^ 2 * 17 * 31 * 127 = 2295 * (7 ^ 2 * 31 * 127) by norm_num] at hn'
  have h7 : Nat.Coprime n (7 ^ 2) := by
    have hndvd : ¬ 7 ∣ n := fun h => by
      have := hp 7 (by norm_num) h
      norm_num at this
    exact Nat.prime_seven.coprime_pow_of_not_dvd hndvd
  have h31 : Nat.Coprime n 31 := by
    have hndvd : ¬ 31 ∣ n := fun h => by
      have := hp 31 (by norm_num) h
      norm_num at this
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 31)).mpr hndvd |>.symm
  have h127 : Nat.Coprime n 127 := by
    have hndvd : ¬ 127 ∣ n := fun h => by
      have := hp 127 (by norm_num) h
      norm_num at this
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 127)).mpr hndvd |>.symm
  have hcopM : Nat.Coprime n (7 ^ 2 * 31 * 127) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨by rw [Nat.coprime_mul_iff_right]; exact ⟨h7, h31⟩, h127⟩
  exact hcopM.dvd_of_dvd_mul_right hn'

theorem HCtx.card_A_sup_u (S : HCtx E B u A H) : Nat.card ↥(A ⊔ zpowers u) = 720 := by
  classical
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [S.hE.2]; norm_num)
  haveI : Finite (MulAut ↥E) := inferInstance
  have hAcard : Nat.card ↥A = 360 := by
    obtain ⟨ψ⟩ := S.A_iso
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hu1 : u ≠ 1 := fun h => S.u_A (by rw [h]; exact A.one_mem)
  have huord : orderOf u = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using S.u_sq) hu1
  have hzucard : Nat.card ↥(zpowers u) = 2 := by rw [Nat.card_zpowers, huord]
  have hinf : A ⊓ zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx.2
    have hmod : u ^ (k % (2 : ℤ)) = u ^ k := by
      have h := zpow_mod_orderOf u k
      rwa [huord] at h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [← hk, ← hmod, h0, zpow_zero]
    · exfalso
      apply S.u_A
      rw [← hk, ← hmod, h1, zpow_one] at hx
      exact hx.1
  have hcent : A ≤
      Subgroup.centralizer ((zpowers u : Subgroup (MulAut ↥E)) : Set (MulAut ↥E)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute a u := S.A_comm a ha
    exact (hc.zpow_right k).eq.symm
  have hnorm : A ≤
      Subgroup.normalizer ((zpowers u : Subgroup (MulAut ↥E)) : Set (MulAut ↥E)) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hmain := card_sup_mul_card_inf_of_le_normalizer (A := A) (B := zpowers u) hnorm
  rw [Subgroup.card_eq_one.mpr hinf, mul_one, hAcard, hzucard] at hmain
  norm_num at hmain
  exact hmain

theorem HCtx.card_P_dvd (hA5 : Sec8T84FactA5) (S : HCtx E B u A H) (O : OddNormal H P) :
    Nat.card ↥P ∣ 2295 := by
  classical
  obtain ⟨⟨hEcomm, hEexp⟩, hEcard⟩ := S.hE
  haveI : IsMulCommutative ↥E := hEcomm
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (mul_comm_of_mem_isMulCommutative E a.2 b.2) }
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  haveI : Finite (MulAut ↥E) := inferInstance
  haveI : Finite ↥P := OddNormal.finite O
  let C : Subgroup (MulAut ↥E) := A ⊔ zpowers u
  have hCcard : Nat.card ↥C = 720 := HCtx.card_A_sup_u S
  have hCH : C ≤ H := sup_le S.A_H (Subgroup.zpowers_le.mpr S.u_H)
  have hAcent : A ≤ Subgroup.centralizer ({u} : Set (MulAut ↥E)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact S.A_comm a ha
  have hZcent : Subgroup.zpowers u ≤ Subgroup.centralizer ({u} : Set (MulAut ↥E)) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hCcent : C ≤ Subgroup.centralizer ({u} : Set (MulAut ↥E)) := sup_le hAcent hZcent
  have hPC : P ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    have hcomm : p * u = u * p :=
      Subgroup.mem_centralizer_singleton_iff.mp (hCcent hp.2)
    exact HCtx.cent_P S O p hp.1 hcomm
  have hPn : C ≤ Subgroup.normalizer (P : Set (MulAut ↥E)) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      exact O.norm c (hCH hc) p hp
    · intro hp
      have h1 := O.norm c⁻¹ (H.inv_mem (hCH hc)) (c * p * c⁻¹) hp
      have h2 : c⁻¹ * (c * p * c⁻¹) * (c⁻¹)⁻¹ = p := by group
      rwa [h2] at h1
  have hmain := card_sup_mul_card_inf_of_le_normalizer (A := C) (B := P) hPn
  have hPC' : C ⊓ P = ⊥ := by rw [inf_comm]; exact hPC
  rw [Subgroup.card_eq_one.mpr hPC', mul_one, hCcard] at hmain
  have hsq : ∀ v : ↥E, v * v = 1 :=
    fun v => Subtype.ext (by simpa [pow_two] using hEexp v v.2)
  have haut : Nat.card (MulAut ↥E) = ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)) :=
    CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two hsq 8 hEcard
  have hdvd : Nat.card ↥(C ⊔ P) ∣ ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)) := by
    have h := Subgroup.card_subgroup_dvd_card (C ⊔ P)
    rwa [haut] at h
  have hd : 720 * Nat.card ↥P ∣ ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)) := by
    rw [← hmain]
    exact hdvd
  refine dvd_2295_of_dvd_prod O.odd ?_ hd
  intro q hqprime hqdvd
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨Q, hQP, hQn, hQne, hexp⟩ :=
    exists_torsion_subgroup H P O.norm (HCtx.comm_P S O) q hqdvd
  have hoddQ : Odd (Nat.card ↥Q) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hQP
    have h := O.odd
    rw [hk] at h
    exact Nat.Odd.of_mul_left h
  have hF : Ctx ↥E u H (B.subgroupOf E) :=
    { sq := fun v => Subtype.ext (by simpa [pow_two] using hEexp v v.2)
      card := hEcard
      u_sq := S.u_sq
      u_mem := S.u_H
      fix := fun e => (S.fix e).trans Subgroup.mem_subgroupOf.symm
      card_B := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.hBE).toEquiv, S.hB.2]
        norm_num
      trans := fun x hx hx1 y hy hy1 =>
        trans_of_factA5 hA5 E B S.hB S.hBE u S.fix A H S.A_iso S.A_comm S.A_faith S.A_H x
          (Subgroup.mem_subgroupOf.mp hx) hx1 y (Subgroup.mem_subgroupOf.mp hy) hy1 }
  exact prime_dvd_255 hF hQne hoddQ hQn q hexp

end C10

end CFSG.OddStandard.SmallF3.Omega
