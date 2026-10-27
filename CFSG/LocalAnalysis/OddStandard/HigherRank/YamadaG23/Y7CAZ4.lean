module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAZ3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_exists_prime_part (ρ : Γ →* MulAut M) {z : Γ} (hρz : ρ z ≠ 1) :
    ∃ (r : ℕ) (z' : Γ), r.Prime ∧ z' ∈ Subgroup.zpowers z ∧ IsPGroup r ↥(Subgroup.zpowers z') ∧
      ρ z' ≠ 1 := by
  have ho_ne : orderOf (ρ z) ≠ 1 := by simpa [orderOf_eq_one_iff] using hρz
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd ho_ne
  have hz0 : orderOf z ≠ 0 := by
    intro h
    have h0 : Nat.card Γ = 0 := Nat.eq_zero_of_zero_dvd (h ▸ orderOf_dvd_natCard z)
    exact (Nat.card_pos (α := Γ)).ne' h0
  obtain ⟨e, n', hn'dvd, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hz0 r hr.ne_one
  have hn' : n' ≠ 0 := by
    intro h
    exact hz0 (by rw [hord, h, mul_zero])
  have hn'pos : 0 < n' := Nat.pos_of_ne_zero hn'
  have hdvd : n' ∣ orderOf z := ⟨r ^ e, by rw [hord, mul_comm]⟩
  have horder : orderOf (z ^ n') = r ^ e := by
    rw [orderOf_pow_of_dvd hn' hdvd, hord, Nat.mul_div_cancel (r ^ e) hn'pos]
  have hρne : ρ (z ^ n') ≠ 1 := by
    intro h
    have hpow : (ρ z) ^ n' = 1 := by simpa [map_pow] using h
    exact hn'dvd (hrdvd.trans (orderOf_dvd_of_pow_eq_one hpow))
  exact ⟨r, z ^ n', hr, Subgroup.npow_mem_zpowers z n',
    IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, horder]), hρne⟩

theorem y7c_two_group_fixed (hM : IsE 6 M) {σ : MulAut M} (hσ : IsPGroup 2 ↥(Subgroup.zpowers σ)) :
    ∃ m : M, m ≠ 1 ∧ σ m = m := by
  let G := ↥(Subgroup.zpowers σ)
  have hcard : Nat.card M = 2 ^ 6 := hM.2
  have hmod := hσ.card_modEq_card_fixedPoints M
  rw [hcard] at hmod
  have hdvd : 2 ∣ Nat.card (MulAction.fixedPoints G M) := by
    have h64 : 2 ^ 6 ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr ⟨2 ^ 5, by norm_num⟩
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h64)
  have h1mem : (1 : M) ∈ MulAction.fixedPoints G M := by
    rw [MulAction.mem_fixedPoints]
    intro g
    simp
  have hpos : 0 < Nat.card (MulAction.fixedPoints G M) :=
    Finite.card_pos_iff.mpr ⟨⟨1, h1mem⟩⟩
  have h2 : 1 < Nat.card (MulAction.fixedPoints G M) := by
    have := Nat.le_of_dvd hpos hdvd
    omega
  rw [Finite.one_lt_card_iff_nontrivial] at h2
  obtain ⟨⟨m, hm⟩, hne⟩ := exists_ne (⟨1, h1mem⟩ : MulAction.fixedPoints G M)
  refine ⟨m, fun h => hne (Subtype.ext h), ?_⟩
  have hfix := (MulAction.mem_fixedPoints.mp hm) ⟨σ, Subgroup.mem_zpowers σ⟩
  change σ m = m at hfix
  exact hfix

theorem y7c_odd_central (c : K7Abs ρ t J Q P M6 M7)
    (hq : CFSG.IsQuasisimple ↥(Subgroup.normalClosure (J : Set Γ))) {z : Γ}
    (hz : z ∈ Subgroup.normalClosure (J : Set Γ))
    (hzc : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), z * n = n * z) (hρz : ρ z ≠ 1) :
    ∃ (r : ℕ) (z' : Γ), r.Prime ∧ r ≠ 2 ∧ z' ∈ Subgroup.normalClosure (J : Set Γ) ∧
      (∀ n ∈ Subgroup.normalClosure (J : Set Γ), z' * n = n * z') ∧
      IsPGroup r ↥(Subgroup.zpowers z') ∧ ∀ m : M, ρ z' m = m → m = 1 := by
  obtain ⟨r, z', hr, hz'zp, hpg, hρz'⟩ := y7c_exists_prime_part ρ hρz
  have hz'N : z' ∈ Subgroup.normalClosure (J : Set Γ) := (Subgroup.zpowers_le.mpr hz) hz'zp
  have hz'c : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), z' * n = n * z' := by
    intro n hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'zp
    have hcomm : Commute z n := hzc n hn
    rw [← hk]
    exact (hcomm.zpow_left k).eq
  have hfpf := y7c_lemmaZ c hq hz'N hz'c hρz'
  have hr2 : r ≠ 2 := by
    intro hr2
    have hpg2 : IsPGroup 2 ↥(Subgroup.zpowers z') := hr2 ▸ hpg
    have hmap : IsPGroup 2 ↥(Subgroup.zpowers (ρ z')) := by
      have h := IsPGroup.map hpg2 ρ
      rwa [MonoidHom.map_zpowers] at h
    obtain ⟨m, hmne, hfix⟩ := y7c_two_group_fixed c.M_E (σ := ρ z') hmap
    exact hmne (hfpf m hfix)
  exact ⟨r, z', hr, hr2, hz'N, hz'c, hpg, hfpf⟩

end CFSG.OddStandard.HigherRank.YamadaG23
