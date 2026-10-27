module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.General
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem IsExt2.exists_swap {R : Subgroup K} {t : K} (hR : IsExt2 R t) {y : K} (hy : y ∈ R)
    (hyt : y ∉ zpowers t) : ∃ r ∈ R, r * y * r⁻¹ = t * y := by
  obtain ⟨r, hr, hyr⟩ : ∃ r ∈ R, y * r ≠ r * y := by
    by_contra hcon
    exact hyt (hR.center_le y hy fun r hr => by
      by_contra hne
      exact hcon ⟨r, hr, hne⟩)
  have hcomm : ⁅r, y⁆ ∈ zpowers t := hR.comm_mem r hr y hy
  have hord : orderOf t = 2 := orderOf_eq_prime hR.t_sq hR.t_ne
  have hmem : ∀ x ∈ zpowers t, x = 1 ∨ x = t := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 := zpow_mod_orderOf t k
    rw [hord] at h1
    simp only [Nat.cast_ofNat] at h1
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [hk, zpow_zero] at h1
      exact h1.symm
    · right
      rw [hk, zpow_one] at h1
      exact h1.symm
  have hne : ⁅r, y⁆ ≠ 1 := by
    intro h
    apply hyr
    rw [commutatorElement_def] at h
    have h2 : r * y * r⁻¹ = y := mul_inv_eq_one.mp h
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hkey : ⁅r, y⁆ = t := (hmem _ hcomm).resolve_left hne
  refine ⟨r, hr, ?_⟩
  rw [commutatorElement_def] at hkey
  exact mul_inv_eq_iff_eq_mul.mp hkey

theorem card_le_pow_of_pRank_le {f : ℕ} (hf : f.Prime) {H E : Subgroup K} (hEH : E ≤ H)
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE' : ∀ a ∈ E, a ^ f = 1) {r : ℕ}
    (h : CFSG.Open.pRank f H ≤ r) : Nat.card E ≤ f ^ r := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hP : IsPGroup f E := by
    intro g
    exact ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hE' g.1 g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hP
  have hEab : CFSG.Open.IsElemAbelian f E :=
    ⟨⟨⟨fun a b => Subtype.ext (hE a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hE' x hx⟩
  have hkr : k ≤ CFSG.Open.pRank f H :=
    CFSG.SectionRank.le_pRank hf.one_lt hEH hEab hk
  rw [hk]
  exact Nat.pow_le_pow_right hf.pos (hkr.trans h)

theorem p_dvd_pow_sub_one {R : Subgroup K} {t z : K} {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hz : z ^ p = 1) (hzR : z ∈ normalizer (R : Set K)) (hR : IsExt2 R t) (hzt : z * t = t * z)
    (hk : Nat.card R = 2 ^ (1 + 2 * k)) (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t) :
    p ∣ 2 ^ (2 * k) - 1 := by
  have hord : orderOf t = 2 := orderOf_eq_prime hR.t_sq hR.t_ne
  have hEq : R ⊓ centralizer ({z} : Set K) = zpowers t := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.mp hx
      have hzx : z * x = x * z := (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
      exact hfix x hxR hzx
    · refine Subgroup.zpowers_le.mpr ?_
      exact Subgroup.mem_inf.mpr ⟨hR.t_mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hcard : Nat.card ↥(R ⊓ centralizer ({z} : Set K)) = 2 := by
    rw [hEq, Nat.card_zpowers, hord]
  have hmod := card_modEq_card_inf_centralizer hp hz hzR
  rw [hcard, hk, pow_add, pow_one] at hmod
  have hpos : 0 < 2 ^ (2 * k) := by positivity
  have hle : 2 ≤ 2 * 2 ^ (2 * k) := by omega
  have hdvd2 : p ∣ 2 * 2 ^ (2 * k) - 2 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  have hfac : 2 * 2 ^ (2 * k) - 2 = 2 * (2 ^ (2 * k) - 1) := by omega
  rw [hfac] at hdvd2
  rcases (Nat.Prime.dvd_mul hp).mp hdvd2 with h2 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2
  · exact h2

theorem p_cases {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk0 : 1 ≤ k) (hk3 : k ≤ 3)
    (hdvd : p ∣ 2 ^ (2 * k) - 1) (h3 : p = 3 → k = 1) (h7 : p = 7 → k = 3 → False) :
    (p = 3 ∧ k = 1) ∨ (p = 5 ∧ k = 2) := by
  interval_cases k
  ·
    have h' : p ∣ 3 := by simpa using hdvd
    exact Or.inl ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h', rfl⟩
  ·
    have h' : p ∣ 3 * 5 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h' with h | h
    · exact absurd (h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)) (by norm_num)
    · exact Or.inr ⟨(Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h, rfl⟩
  ·
    have h' : p ∣ 3 * 3 * 7 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h' with h | h
    · have h3' : p ∣ 3 := by
        rcases (Nat.Prime.dvd_mul hp).mp h with h'' | h'' <;> exact h''
      exact absurd (h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3')) (by norm_num)
    · exact (h7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h) rfl).elim
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
