module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

lemma mem_zpow_mul_of_index_five_sylow {Y : Type*} [Group Y] [Finite Y] (K : Subgroup Y)
    [K.Normal] (hidx : K.index = 5) (σ : Y) (hσ : orderOf σ = 5) (hσK : σ ∉ K)
    (S : Subgroup Y) (hσS : σ ∈ S) (s : Y) (hs : s ∈ S) :
    ∃ n : ℤ, ∃ p ∈ S ⊓ K, s = σ ^ n * p := by
  have hcard : Nat.card (Y ⧸ K) = 5 := by
    rw [← Subgroup.index_eq_card, hidx]
  have hord : orderOf ((QuotientGroup.mk' K) σ) = 5 := by
    have hdvd : orderOf ((QuotientGroup.mk' K) σ) ∣ 5 := by
      have := orderOf_map_dvd (QuotientGroup.mk' K) σ
      rwa [hσ] at this
    have hne : (QuotientGroup.mk' K) σ ≠ 1 := by
      intro h
      apply hσK
      rw [QuotientGroup.mk'_apply] at h
      exact (QuotientGroup.eq_one_iff σ).1 h
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hne
    · exact h1
  have htop : Subgroup.zpowers ((QuotientGroup.mk' K) σ) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  have hmem : (QuotientGroup.mk' K) s ∈ Subgroup.zpowers ((QuotientGroup.mk' K) σ) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hkey : (QuotientGroup.mk' K) (σ ^ (-k) * s) = 1 := by
    rw [map_mul, map_zpow, ← hk, zpow_neg, inv_mul_cancel]
  have hpK : σ ^ (-k) * s ∈ K := by
    rw [QuotientGroup.mk'_apply] at hkey
    exact (QuotientGroup.eq_one_iff _).1 hkey
  refine ⟨k, σ ^ (-k) * s, Subgroup.mem_inf.2 ⟨S.mul_mem (S.zpow_mem hσS _) hs, hpK⟩, ?_⟩
  group

theorem center_eq_of_abelian_sylow {Y : Type*} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal]
    (hidx : K.index = 5) (σ : Y) (hσ : orderOf σ = 5) (hσK : σ ∉ K)
    (S : Sylow 5 Y) (hσS : σ ∈ (S : Subgroup Y))
    (hPcard : Nat.card ((S : Subgroup Y) ⊓ K : Subgroup Y) = 5 ^ 4)
    (hPab : ∀ a ∈ ((S : Subgroup Y) ⊓ K), ∀ b ∈ ((S : Subgroup Y) ⊓ K), a * b = b * a)
    (hF : ∀ F : Subgroup Y, IsPGroup 5 F → F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
      Nat.card F ≤ 25)
    (E : Subgroup Y) (hE : E ≤ (S : Subgroup Y) ⊓ K) (hEσ : E ≤ Subgroup.centralizer ({σ} : Set Y))
    (hEcard : Nat.card E = 25) :
    (S : Subgroup Y) ⊓ Subgroup.centralizer ((S : Subgroup Y) : Set Y) = E := by
  set P : Subgroup Y := (S : Subgroup Y) ⊓ K with hPdef
  have hPS : P ≤ (S : Subgroup Y) := inf_le_left
  have hPK : P ≤ K := inf_le_right
  have hP5 : IsPGroup 5 P := IsPGroup.to_inf_left S.isPGroup'
  have hPσ_not : ¬ (P ≤ Subgroup.centralizer ({σ} : Set Y)) := by
    intro h
    have := hF P hP5 hPK h
    rw [hPcard] at this
    norm_num at this
  have hform : ∀ s ∈ (S : Subgroup Y), ∃ n : ℤ, ∃ p ∈ P, s = σ ^ n * p :=
    fun s hs => mem_zpow_mul_of_index_five_sylow K hidx σ hσ hσK (S : Subgroup Y) hσS s hs
  ext z
  constructor
  · intro hz
    obtain ⟨hzS, hzC⟩ := Subgroup.mem_inf.1 hz
    have hzC' : ∀ h ∈ (S : Subgroup Y), h * z = z * h :=
      fun h hh => Subgroup.mem_centralizer_iff.1 hzC h hh
    have hzP : z ∈ P := by
      by_contra hzP
      obtain ⟨n, p, hpP, hzeq⟩ := hform z hzS
      have hn : ¬ (5 : ℤ) ∣ n := by
        intro h5
        have h5' : ((orderOf σ : ℕ) : ℤ) ∣ n := by
          rw [hσ]
          exact h5
        have h1 : σ ^ n = 1 := orderOf_dvd_iff_zpow_eq_one.1 h5'
        apply hzP
        rw [hzeq, h1, one_mul]
        exact hpP
      have hcommP : ∀ q ∈ P, Commute (σ ^ n) q := by
        intro q hq
        have hzq : Commute z q := (hzC' q (hPS hq)).symm
        have hpq : Commute p q := hPab p hpP q hq
        have hzp : Commute (z * p⁻¹) q := hzq.mul_left hpq.inv_left
        have heq : z * p⁻¹ = σ ^ n := by
          rw [hzeq, mul_inv_cancel_right]
        rwa [heq] at hzp
      have hσcomm : ∀ q ∈ P, Commute σ q := by
        intro q hq
        have hc : Commute (σ ^ n) q := hcommP q hq
        have hprime : Irreducible (5 : ℤ) :=
          (Int.prime_iff_natAbs_prime.mpr (by norm_num)).irreducible
        have hcop : IsCoprime (5 : ℤ) n := hprime.coprime_iff_not_dvd.2 hn
        obtain ⟨a, b, hab⟩ := hcop.symm
        have hmod : n * a ≡ 1 [ZMOD (orderOf σ : ℤ)] := by
          rw [hσ, Int.modEq_iff_dvd]
          exact ⟨b, by push_cast; linear_combination -hab⟩
        have hpow : σ ^ (n * a) = σ ^ (1 : ℤ) := zpow_eq_zpow_iff_modEq.2 hmod
        rw [zpow_one] at hpow
        have h2 : Commute (σ ^ (n * a)) q := by
          rw [zpow_mul]
          exact hc.zpow_left a
        rw [hpow] at h2
        exact h2
      apply hPσ_not
      intro q hq
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff.1 hh]
      exact hσcomm q hq
    have hzσ : σ * z = z * σ := hzC' σ hσS
    have hzF : z ∈ P ⊓ Subgroup.centralizer ({σ} : Set Y) := by
      refine Subgroup.mem_inf.2 ⟨hzP, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff.1 hh]
      exact hzσ
    have hFle : E ≤ P ⊓ Subgroup.centralizer ({σ} : Set Y) :=
      fun e he => Subgroup.mem_inf.2 ⟨hE he, hEσ he⟩
    have hFcard : Nat.card ↥(P ⊓ Subgroup.centralizer ({σ} : Set Y)) ≤ 25 :=
      hF _ (IsPGroup.to_inf_left hP5) (inf_le_left.trans hPK) inf_le_right
    have hEF : E = P ⊓ Subgroup.centralizer ({σ} : Set Y) :=
      Subgroup.eq_of_le_of_card_ge hFle (by rw [hEcard]; exact hFcard)
    rw [hEF]
    exact hzF
  · intro hzE
    have hzP : z ∈ P := hE hzE
    have hzS : z ∈ (S : Subgroup Y) := hPS hzP
    have hzσ : σ * z = z * σ := Subgroup.mem_centralizer_iff.1 (hEσ hzE) σ (Set.mem_singleton σ)
    have hcσz : Commute σ z := hzσ
    refine Subgroup.mem_inf.2 ⟨hzS, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    obtain ⟨n, p, hpP, rfl⟩ := hform h hh
    have hc1 : Commute (σ ^ n) z := hcσz.zpow_left n
    have hc2 : Commute p z := hPab p hpP z hzP
    exact hc1.mul_left hc2

end CFSG.HardMathSupport.Malle.LocalAction

end
