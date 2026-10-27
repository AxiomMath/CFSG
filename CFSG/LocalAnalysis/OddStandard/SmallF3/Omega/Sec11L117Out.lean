module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Eq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Q8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

private lemma mem_zpowers_eq_one_or {z e : G} (hz : z * z = 1) (he : e ∈ zpowers z) :
    e = 1 ∨ e = z := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp he
  rw [← hk]
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · left; rw [hk0]; exact zpow_zero z
  · right; rw [hk1]; exact zpow_one z

private lemma sq_eq_one_of_mem_zpowers {z e : G} (hz : z * z = 1) (he : e ∈ zpowers z) :
    e * e = 1 := by
  rcases mem_zpowers_eq_one_or hz he with h | h
  · rw [h, one_mul]
  · rw [h]; exact hz

private lemma sec11_comm_z_of_conj_mem {z ρ : G} {Q : Subgroup G} (hQ : Sec11Q8 G z Q)
    (hρQ : ∀ q ∈ Q, ρ * q * ρ⁻¹ ∈ Q) (hρiQ : ∀ q ∈ Q, ρ⁻¹ * q * ρ ∈ Q)
    (hρzQ : ρ * z * ρ⁻¹ ∈ Q) : ρ * z = z * ρ := by
  have hwcomm : ∀ q ∈ Q, (ρ * z * ρ⁻¹) * q = q * (ρ * z * ρ⁻¹) := by
    intro q hq
    have h1 : (ρ⁻¹ * q * ρ) * z = z * (ρ⁻¹ * q * ρ) := hQ.z_cent _ (hρiQ q hq)
    calc (ρ * z * ρ⁻¹) * q
        = ρ * (z * (ρ⁻¹ * q * ρ)) * ρ⁻¹ := by group
      _ = ρ * ((ρ⁻¹ * q * ρ) * z) * ρ⁻¹ := by rw [← h1]
      _ = q * (ρ * z * ρ⁻¹) := by group
  have hwmem : ρ * z * ρ⁻¹ ∈ zpowers z := hQ.center _ hρzQ hwcomm
  have hwne : ρ * z * ρ⁻¹ ≠ 1 := fun h => hQ.z_ne (conj_eq_one_iff.mp h)
  have hwz : ρ * z * ρ⁻¹ = z := by
    rcases mem_zpowers_eq_one_or hQ.z_sq hwmem with h | h
    · exact absurd h hwne
    · exact h
  have hcongr := congrArg (fun t => t * ρ) hwz
  simpa [mul_assoc] using hcongr

private lemma sec11_conj_agree_on_Q {x k0 ρ : G} {Q K : Subgroup G} (hQK : Q ≤ K)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (hk0Q : k0 ∈ Q)
    (hk0 : ∀ q ∈ Q, x * q * x⁻¹ = k0 * q * k0⁻¹) (hρK : ρ ∈ K) :
    ∀ q ∈ Q, (x * ρ * x⁻¹) * q * (x * ρ * x⁻¹)⁻¹
      = (k0 * ρ * k0⁻¹) * q * (k0 * ρ * k0⁻¹)⁻¹ := by
  intro q hq
  have hq' : k0⁻¹ * q * k0 ∈ Q := by
    simpa using hKQ k0⁻¹ (hQK (inv_mem hk0Q)) q hq
  have hxq : x * (k0⁻¹ * q * k0) * x⁻¹ = q := by
    have h := hk0 (k0⁻¹ * q * k0) hq'
    rw [h]; group
  have hxinv : x⁻¹ * q * x = k0⁻¹ * q * k0 := by
    have hcongr := congrArg (fun t => x⁻¹ * t * x) hxq
    simpa [mul_assoc] using hcongr.symm
  have hρq' : ρ * (k0⁻¹ * q * k0) * ρ⁻¹ ∈ Q := hKQ ρ hρK _ hq'
  have hstep := hk0 (ρ * (k0⁻¹ * q * k0) * ρ⁻¹) hρq'
  have hkey : (x * ρ * x⁻¹) * q * (x * ρ * x⁻¹)⁻¹
      = x * (ρ * (x⁻¹ * q * x) * ρ⁻¹) * x⁻¹ := by group
  rw [hkey, hxinv, hstep]
  group

theorem sec11_out_abs [Finite G] {z x : G} {Q K N : Subgroup G} (hQ : Sec11Q8 G z Q)
    (hQK : Q ≤ K) (hK : Nat.card K = 24) (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hKN : K ≤ normalizer (N : Set G)) (hNQ : ∀ n ∈ N, ∀ q ∈ Q, n * q = q * n)
    (hKN1 : ∀ g ∈ K, g ∈ N → g = 1)
    (hCK : ∀ k ∈ K, (∀ q ∈ Q, k * q = q * k) → k ∈ zpowers z)
    (hxX : x ∈ normalizer ((K ⊔ N : Subgroup G) : Set G)) (hxN : x ∈ normalizer (N : Set G))
    (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hxtriv : ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers z) :
    ∃ k ∈ K ⊔ N, ∀ y ∈ K ⊔ N, x * y * x⁻¹ * (k * y * k⁻¹)⁻¹ ∈ N := by
  obtain ⟨k0, hk0Q, hk0⟩ := hQ.inner_of_trivial hxQ hxtriv
  obtain ⟨ρ, hρK, hρ3, hKeq⟩ := sec11_exists_order_three hQK hQ.card hK
  have hρz : ρ * z = z * ρ :=
    sec11_comm_z_of_conj_mem hQ (fun q hq => hKQ ρ hρK q hq)
      (fun q hq => by simpa using hKQ ρ⁻¹ (inv_mem hρK) q hq) (hKQ ρ hρK z hQ.z_mem)
  have hQcent : Q ≤ centralizer ({z} : Set G) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hQ.z_cent q hq)
  have hρcent : zpowers ρ ≤ centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hρz)
  have hKcent : K ≤ centralizer ({z} : Set G) := by
    rw [hKeq]
    exact sup_le hQcent hρcent
  have hzK : ∀ k ∈ K, k * z = z * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKcent hk)
  have hρ1X : x * ρ * x⁻¹ ∈ K ⊔ N :=
    (Subgroup.mem_normalizer_iff.mp hxX ρ).mp (mem_sup_left hρK)
  have hρ2K : k0 * ρ * k0⁻¹ ∈ K := mul_mem (mul_mem (hQK hk0Q) hρK) (inv_mem (hQK hk0Q))
  have hC1 := sec11_conj_agree_on_Q hQK hKQ hk0Q hk0 hρK
  have hcq : ∀ q ∈ Q,
      ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * q
        * ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹))⁻¹ = q := by
    intro q hq
    calc ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * q
          * ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹))⁻¹
        = (k0 * ρ * k0⁻¹)⁻¹ * ((x * ρ * x⁻¹) * q * (x * ρ * x⁻¹)⁻¹) * (k0 * ρ * k0⁻¹) := by
          group
      _ = (k0 * ρ * k0⁻¹)⁻¹ * ((k0 * ρ * k0⁻¹) * q * (k0 * ρ * k0⁻¹)⁻¹) * (k0 * ρ * k0⁻¹) := by
          rw [hC1 q hq]
      _ = q := by group
  have hcX : (k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹) ∈ K ⊔ N :=
    mul_mem (inv_mem (mem_sup_left hρ2K)) hρ1X
  have hcX' : (k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹) ∈ (K : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K N hKN]
    exact hcX
  obtain ⟨k, hkK, n, hnN, hkn⟩ := Set.mem_mul.mp hcX'
  have hkNq : ∀ q ∈ Q, k * q = q * k := by
    intro q hq
    have hcq' : ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * q
        = q * ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) := by
      have hcongr := congrArg (fun t => t * ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹))) (hcq q hq)
      simpa [mul_assoc] using hcongr
    have hnq : n⁻¹ * q = q * n⁻¹ := hNQ n⁻¹ (inv_mem hnN) q hq
    have hkc : k = ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * n⁻¹ := by rw [← hkn]; group
    rw [hkc]
    calc ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * n⁻¹ * q
        = ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * (n⁻¹ * q) := by group
      _ = ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * (q * n⁻¹) := by rw [hnq]
      _ = (((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * q) * n⁻¹ := by group
      _ = (q * ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹))) * n⁻¹ := by rw [hcq']
      _ = q * (((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * n⁻¹) := by group
  have hkz : k ∈ zpowers z := hCK k hkK hkNq
  have hρ2N : k0 * ρ * k0⁻¹ ∈ normalizer (N : Set G) := hKN hρ2K
  have hρ23 : (k0 * ρ * k0⁻¹) * (k0 * ρ * k0⁻¹) * (k0 * ρ * k0⁻¹) = 1 := by
    have hpow : (k0 * ρ * k0⁻¹) * (k0 * ρ * k0⁻¹) * (k0 * ρ * k0⁻¹) = k0 * (ρ * ρ * ρ) * k0⁻¹ := by
      group
    rw [hpow, hρ3]; group
  have hk2 : k * k = 1 := sq_eq_one_of_mem_zpowers hQ.z_sq hkz
  have hkρ2 : k * (k0 * ρ * k0⁻¹) = (k0 * ρ * k0⁻¹) * k := by
    have hle : zpowers z ≤ centralizer ({(k0 * ρ * k0⁻¹)} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hzK _ hρ2K).symm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hkz)
  have hkNc : ∀ m ∈ N, k * m = m * k := by
    intro m hm
    have hmz : z * m = m * z := (hNQ m hm z hQ.z_mem).symm
    have hle : zpowers z ≤ centralizer ({m} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hmz)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hkz)
  have hknρ : (k0 * ρ * k0⁻¹) * k * n = x * ρ * x⁻¹ := by
    calc (k0 * ρ * k0⁻¹) * k * n
        = (k0 * ρ * k0⁻¹) * (k * n) := by group
      _ = (k0 * ρ * k0⁻¹) * ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) := by rw [hkn]
      _ = x * ρ * x⁻¹ := by group
  have hρ13 : (x * ρ * x⁻¹) * (x * ρ * x⁻¹) * (x * ρ * x⁻¹) = 1 := by
    have hpow : (x * ρ * x⁻¹) * (x * ρ * x⁻¹) * (x * ρ * x⁻¹) = x * (ρ * ρ * ρ) * x⁻¹ := by
      group
    rw [hpow, hρ3]; group
  have h3 : ((k0 * ρ * k0⁻¹) * k * n) * ((k0 * ρ * k0⁻¹) * k * n)
      * ((k0 * ρ * k0⁻¹) * k * n) = 1 := by
    rw [hknρ, hρ13]
  have hkNmem : k ∈ N := sec11_cube_mem hρ2N hρ23 hk2 hkρ2 hkNc hnN h3
  have hk1 : k = 1 := hKN1 k hkK hkNmem
  have hcN : (k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹) ∈ N := by
    rw [← hkn, hk1, one_mul]
    exact hnN
  have hCkey : (x * ρ * x⁻¹) * (k0 * ρ * k0⁻¹)⁻¹ ∈ N := by
    have hconj : (k0 * ρ * k0⁻¹) * ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * (k0 * ρ * k0⁻¹)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hρ2N _).mp hcN
    have heq : (k0 * ρ * k0⁻¹) * ((k0 * ρ * k0⁻¹)⁻¹ * (x * ρ * x⁻¹)) * (k0 * ρ * k0⁻¹)⁻¹
        = (x * ρ * x⁻¹) * (k0 * ρ * k0⁻¹)⁻¹ := by group
    rwa [heq] at hconj
  refine ⟨k0, mem_sup_left (hQK hk0Q), ?_⟩
  intro y hy
  have hgen : ∀ s ∈ ((Q : Set G) ∪ {ρ} ∪ (N : Set G)),
      x * s * x⁻¹ * (k0 * s * k0⁻¹)⁻¹ ∈ N := by
    intro s hs
    rcases hs with (hsQ | hsρ) | hsN
    · rw [hk0 s hsQ, mul_inv_cancel]
      exact N.one_mem
    · rw [Set.mem_singleton_iff] at hsρ
      subst hsρ
      exact hCkey
    · exact mul_mem ((Subgroup.mem_normalizer_iff.mp hxN s).mp hsN)
        (inv_mem ((Subgroup.mem_normalizer_iff.mp (hKN (hQK hk0Q)) s).mp hsN))
  have hS : ∀ s ∈ ((Q : Set G) ∪ {ρ} ∪ (N : Set G)), s ∈ normalizer (N : Set G) := by
    intro s hs
    rcases hs with (hsQ | hsρ) | hsN
    · exact hKN (hQK hsQ)
    · rw [Set.mem_singleton_iff] at hsρ
      subst hsρ
      exact hKN hρK
    · exact le_normalizer hsN
  have hmain := sec11_conj_agree_closure (u := x) (v := k0) hxN hS hgen
  have hKle : K ≤ Subgroup.closure ((Q : Set G) ∪ {ρ} ∪ (N : Set G)) := by
    rw [hKeq]
    refine sup_le ?_ ?_
    · intro q hq
      exact Subgroup.subset_closure (Or.inl (Or.inl hq))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hNle : N ≤ Subgroup.closure ((Q : Set G) ∪ {ρ} ∪ (N : Set G)) := fun n hn =>
    Subgroup.subset_closure (Or.inr hn)
  exact hmain y ((sup_le hKle hNle) hy)

end CFSG.OddStandard.SmallF3.Omega
