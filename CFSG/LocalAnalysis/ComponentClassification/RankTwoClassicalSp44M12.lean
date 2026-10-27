module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44Defs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import Certificates.Certificate15068

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms

private theorem mem_of_pow_eq_one_of_coprime {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {n : ℕ} (hn : Nat.Coprime n N.index) {g : G} (hg : g ^ n = 1) : g ∈ N := by
  have h1 : orderOf (g : G ⧸ N) ∣ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one])
  have h2 : orderOf (g : G ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have h3 := (Nat.Coprime.coprime_dvd_left h1 hn).eq_one_of_dvd h2
  rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3

theorem m12_no_fifteen :
    ∀ g : NativeSporadic.M12, orderOf g ≠ 15 := by
  intro g hg
  have h := card_orderOf_eq (by norm_num) m12Certificate m12Certificate_check (m := 15)
    (by norm_num)
  rw [Certificates.certificate15068, m12Certificate_originalSubgroup] at h
  have : Nonempty {x : NativeSporadic.M12 // orderOf x = 15} := ⟨⟨g, hg⟩⟩
  have hpos := Nat.card_pos (α := {x : NativeSporadic.M12 // orderOf x = 15})
  omega

theorem m12AutThreeFive :
    M12AutThreeFive := by
  intro X _ hX α hα h hh hαh
  obtain ⟨k, hk⟩ := hα
  obtain ⟨φ⟩ := hX
  let ψ : X ≃* NativeSporadic.M12 := φ
  set α' : MulAut NativeSporadic.M12 := MulAut.congr ψ α with hα'
  have hk' : α' ^ 3 ^ k = 1 := by rw [hα', ← map_pow, hk, map_one]
  have hin : α' ∈ inner NativeSporadic.M12 := by
    refine mem_of_pow_eq_one_of_coprime ?_ hk'
    rw [Subgroup.index, M12Cover.card_outer]
    exact Nat.Coprime.pow_left k (by norm_num)
  obtain ⟨g, hg⟩ := hin
  change MulAut.conj g = α' at hg
  have hg3 : g ^ 3 ^ k = 1 := by
    have h1 : MulAut.conj (g ^ 3 ^ k) = 1 := by rw [map_pow, hg, hk']
    have h2 : g ^ 3 ^ k ∈ center NativeSporadic.M12 := by
      rw [mem_center_iff]
      intro y
      have h3 := congrArg (fun σ : MulAut NativeSporadic.M12 => σ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * g ^ 3 ^ k = g ^ 3 ^ k * y * (g ^ 3 ^ k)⁻¹ * g ^ 3 ^ k := by rw [h3]
        _ = g ^ 3 ^ k * y := by group
    rw [M12Cover.m12_center, mem_bot] at h2
    exact h2
  have hh' : orderOf (ψ h) = 5 := by rw [MulEquiv.orderOf_eq]; exact hh
  have hcomm : Commute g (ψ h) := by
    have h1 : α' (ψ h) = ψ h := by
      rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hαh]
    rw [← hg, MulAut.conj_apply] at h1
    calc g * ψ h = g * ψ h * g⁻¹ * g := by group
      _ = ψ h * g := by rw [h1]
  have hg1 : g = 1 := by
    by_contra hne
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hg3)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.mp (by rw [ha, pow_zero]))
    have hdvd : 3 ^ (a - 1) ∣ orderOf g := by
      rw [ha]
      exact pow_dvd_pow 3 (Nat.sub_le a 1)
    have hg' : orderOf (g ^ 3 ^ (a - 1)) = 3 := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, ha, Nat.pow_div (Nat.sub_le a 1) (by norm_num),
        show a - (a - 1) = 1 by omega, pow_one]
    have h15 : orderOf (g ^ 3 ^ (a - 1) * ψ h) = 15 := by
      rw [(hcomm.pow_left _).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hg', hh']; norm_num),
        hg', hh']
    exact m12_no_fifteen _ h15
  have h1 : α' = 1 := by rw [← hg, hg1, map_one]
  apply (MulAut.congr ψ).injective
  rw [map_one]
  exact h1

end CFSG.ComponentClassification.RankTwoClassical
