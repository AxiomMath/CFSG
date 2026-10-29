module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112S6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112D8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec11CData (t z : G) (L S : Subgroup G) (K1 K2 T : Subgroup G) : Prop where
  TM : T ≤ secM t S L
  AT : secA t S L ≤ T
  t2 : t * t = 1
  z2 : z * z = 1
  tz : t * z = z * t
  z1 : z ≠ 1
  tA : t ∈ secA t S L
  tC : t ∈ secCTQ K1 K2 T
  zC : z ∈ secCTQ K1 K2 T

theorem sec11_cdata [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    Sec11CData t z L S K1 K2 T := by
  obtain ⟨ht2, hz2, htzc, -, hz1, -, htS, hzS, -⟩ := sec11L114_data hp hctx
  have hQc := sec11L114_cent_Q hp hctx
  exact ⟨hctx.sylowT.1, sec11_A_le_T hp hctx, ht2, hz2, htzc, hz1, mem_sup_right (mem_zpowers t),
    ⟨hQc.1, hctx.S_le htS⟩, ⟨hQc.2, hctx.S_le hzS⟩⟩

theorem sec11_cTQ_comm {K1 K2 T : Subgroup G} {c : G} (hc : c ∈ secCTQ K1 K2 T) :
    ∀ q ∈ secQ K1 K2, c * q = q * c := fun q hq =>
  (Subgroup.mem_centralizer_iff.mp hc.1 q hq).symm

namespace Sec11Model

variable {t z : G} {L S : Subgroup G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem cent_le_pair (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    (h : ∀ c ∈ secCTQ K1 K2 T, hm.perm.rho c = 1) :
    secCTQ K1 K2 T ≤ zpowers t ⊔ zpowers z := by
  intro c hc
  rcases hm.cent_ker hTM hc.2 (sec11_cTQ_comm hc) (h c hc) with h1 | h1 | h1 | h1
  · rw [h1]
    exact one_mem _
  · rw [h1]
    exact mem_sup_left (mem_zpowers t)
  · rw [h1]
    exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right (mem_zpowers z))
  · rw [h1]
    exact mem_sup_right (mem_zpowers z)

theorem cent_A6 (hm : Sec11Model t L S z K1 K2 T Alt φ) (hd : Sec11CData t z L S K1 K2 T)
    (hAlt : Alt = alternatingGroup (Fin 6)) : secCTQ K1 K2 T = zpowers t ⊔ zpowers z := by
  refine le_antisymm (hm.cent_le_pair hd.TM fun c hc => ?_)
    (sup_le (zpowers_le.mpr hd.tC) (zpowers_le.mpr hd.zC))
  rcases hm.cent_rho hd.TM hc.2 (sec11_cTQ_comm hc) with h | h
  · exact h
  · exfalso
    have hmem := hm.perm.rho_mem (hd.TM hc.2)
    rw [h, hAlt, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hmem
    exact absurd hmem (by decide)

theorem exists_cent_swap [Finite G] (hm : Sec11Model t L S z K1 K2 T Alt φ)
    (hd : Sec11CData t z L S K1 K2 T) (h8 : 8 ≤ Nat.card ↥(secCTQ K1 K2 T)) :
    ∃ r ∈ secCTQ K1 K2 T, hm.perm.rho r = Equiv.swap 0 1 := by
  by_contra hno
  push Not at hno
  have hall : ∀ c ∈ secCTQ K1 K2 T, hm.perm.rho c = 1 := fun c hc =>
    (hm.cent_rho hd.TM hc.2 (sec11_cTQ_comm hc)).resolve_right (hno c hc)
  have h1 := Subgroup.card_le_of_le (hm.cent_le_pair hd.TM hall)
  have h2 := sec11L114_pair_card_le hd.t2 hd.z2 hd.tz
  omega

theorem exists_cent_inv (hm : Sec11Model t L S z K1 K2 T Alt φ) (hd : Sec11CData t z L S K1 K2 T)
    {r0 : G} (hr0C : r0 ∈ secCTQ K1 K2 T) (hρ0 : hm.perm.rho r0 = Equiv.swap 0 1) :
    ∃ r ∈ secCTQ K1 K2 T, hm.perm.rho r = Equiv.swap 0 1 ∧ r * r = 1 := by
  have hr0M : r0 ∈ secM t S L := hd.TM hr0C.2
  have hconj : ∀ v, r0 * φ v * r0⁻¹ = φ (permVec (Equiv.swap 0 1) v) := fun v => by
    have := hm.perm.conj_apply hr0M v
    rwa [hρ0] at this
  have hρsq : hm.perm.rho (r0 * r0) = 1 := by
    rw [hm.perm.rho_mul hr0M hr0M, hρ0, Equiv.swap_mul_self]
  have hsqC : r0 * r0 ∈ secCTQ K1 K2 T := (secCTQ K1 K2 T).mul_mem hr0C hr0C
  have hct := hm.conj_t hconj
  have hcz := hm.conj_z hconj
  have hne : t * z ≠ t := fun h => hd.z1 (mul_left_cancel (h.trans (mul_one t).symm))
  rcases hm.cent_ker hd.TM hsqC.2 (sec11_cTQ_comm hsqC) hρsq with h | h | h | h
  · exact ⟨r0, hr0C, hρ0, h⟩
  · exfalso
    have h1 : r0 * t * r0⁻¹ = t := by
      rw [← h]
      group
    exact hne (hct.symm.trans h1)
  · exfalso
    have h1 : r0 * (t * z) * r0⁻¹ = t * z := by
      rw [← h]
      group
    have h2 : r0 * (t * z) * r0⁻¹ = t := by
      calc r0 * (t * z) * r0⁻¹ = (r0 * t * r0⁻¹) * (r0 * z * r0⁻¹) := by group
        _ = t * z * z := by rw [hct, hcz]
        _ = t := by rw [mul_assoc, hd.z2, mul_one]
    exact hne (h1.symm.trans h2)
  · refine ⟨r0 * t, (secCTQ K1 K2 T).mul_mem hr0C hd.tC, ?_, ?_⟩
    · rw [hm.perm.rho_mul hr0M (hd.TM hd.tC.2), hρ0,
        hm.perm.rho_of_mem (hd.AT.trans hd.TM) hd.tA, mul_one]
    · calc r0 * t * (r0 * t) = (r0 * t * r0⁻¹) * (r0 * r0) * t := by group
        _ = t * z * z * t := by rw [hct, h]
        _ = 1 := by rw [mul_assoc t z z, hd.z2, mul_one, hd.t2]

theorem cent_finish (hm : Sec11Model t L S z K1 K2 T Alt φ) (hd : Sec11CData t z L S K1 K2 T)
    {r : G} (hrC : r ∈ secCTQ K1 K2 T) (hρ : hm.perm.rho r = Equiv.swap 0 1) (hr2 : r * r = 1) :
    orderOf r = 2 ∧ secCTQ K1 K2 T = zpowers t ⊔ zpowers r ∧ IsD8 (secCTQ K1 K2 T) ∧
      ∀ v, r * φ v * r⁻¹ = φ (permVec (Equiv.swap 0 1) v) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrM : r ∈ secM t S L := hd.TM hrC.2
  have hconj : ∀ v, r * φ v * r⁻¹ = φ (permVec (Equiv.swap 0 1) v) := fun v => by
    have := hm.perm.conj_apply hrM v
    rwa [hρ] at this
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hrt : r * t * r = t * z := by
    have := hm.conj_t hconj
    rwa [hrinv] at this
  have hsq : (t * r) ^ 2 = z := by
    calc (t * r) ^ 2 = t * (r * t * r) := by rw [pow_two]; group
      _ = (t * t) * z := by rw [hrt]; group
      _ = z := by rw [hd.t2, one_mul]
  have htr : t * r ∈ zpowers t ⊔ zpowers r :=
    mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right (mem_zpowers r))
  have hz : z ∈ zpowers t ⊔ zpowers r := by
    rw [← hsq, pow_two]
    exact mul_mem htr htr
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [hm.perm.rho_one] at hρ
    exact absurd hρ (by decide)
  have hker : ∀ c ∈ secCTQ K1 K2 T, hm.perm.rho c = 1 → c ∈ zpowers t ⊔ zpowers r := by
    intro c hc h1
    rcases hm.cent_ker hd.TM hc.2 (sec11_cTQ_comm hc) h1 with h | h | h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_sup_left (mem_zpowers t)
    · rw [h]
      exact mul_mem (mem_sup_left (mem_zpowers t)) hz
    · rw [h]
      exact hz
  have hC : secCTQ K1 K2 T = zpowers t ⊔ zpowers r := by
    refine le_antisymm (fun c hc => ?_) (sup_le (zpowers_le.mpr hd.tC) (zpowers_le.mpr hrC))
    rcases hm.cent_rho hd.TM hc.2 (sec11_cTQ_comm hc) with h | h
    · exact hker c hc h
    · have hcr : c * r ∈ secCTQ K1 K2 T := (secCTQ K1 K2 T).mul_mem hc hrC
      have hρcr : hm.perm.rho (c * r) = 1 := by
        rw [hm.perm.rho_mul (hd.TM hc.2) hrM, h, hρ, Equiv.swap_mul_self]
      have hmem := mul_mem (hker _ hcr hρcr) (mem_sup_right (mem_zpowers r))
      rwa [mul_assoc, hr2, mul_one] at hmem
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1, hC, ?_, hconj⟩
  rw [hC]
  refine sec11_isD8_of hd.t2 hr2 ?_ (by rw [hsq]; exact hd.z1)
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two, hd.z2]

end Sec11Model

theorem sec11_cent_T_Q [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}
    (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    (Alt = alternatingGroup (Fin 6) ∧ secCTQ K1 K2 T = zpowers t ⊔ zpowers z) ∨
      (Alt = ⊤ ∧ ∃ r : G, orderOf r = 2 ∧ secCTQ K1 K2 T = zpowers t ⊔ zpowers r ∧
        IsD8 (secCTQ K1 K2 T) ∧ ∀ v, r * φ v * r⁻¹ = φ (permVec (Equiv.swap 0 1) v)) := by
  have hd := sec11_cdata hp hctx
  rcases hm.alt with hA | hS
  · exact Or.inl ⟨hA, hm.cent_A6 hd hA⟩
  · refine Or.inr ⟨hS, ?_⟩
    obtain ⟨r0, hr0C, hρ0⟩ := hm.exists_cent_swap hd (sec11_cent_card_ge hp hctx hm hS)
    obtain ⟨r, hrC, hρ, hr2⟩ := hm.exists_cent_inv hd hr0C hρ0
    obtain ⟨h1, h2, h3, h4⟩ := hm.cent_finish hd hrC hρ hr2
    exact ⟨r, h1, h2, h3, h4⟩

end CFSG.OddStandard.SmallF3.Omega
