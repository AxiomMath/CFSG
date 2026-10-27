module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.GH74.KGroups.L3EpsUniBlock

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps.Uni CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Engine

variable {Y : Type} [Group Y]

theorem ka_all_of_omega (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (Ω : Subgroup Y) (hΩC : Ω ≤ fixSub α)
    (hΩgen : Subgroup.closure {x : Y | x ∈ Ω ∧ Odd (orderOf x)} = Ω)
    (hΩp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≤ fixSub α →
      (∀ ω ∈ Ω, ω ∈ normalizer (X : Set Y)) → X = ⊥)
    (hOut : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P →
      (∀ e ∈ P, e ∈ innSub Y → e = 1) → P = ⊥) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  exfalso
  have hΩN := ka_normalizes_of_gen hnorm hΩC hΩgen
  have hX0p : IsPGroup p ↥(kaInner P) := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub α := kaInner_le_fixSub hinj hcomm
  have hbot : kaInner P = ⊥ :=
    hΩp p hp hp2 (kaInner P) hX0p hX0C fun ω hω => mem_normalizer_kaInner (hΩN ω hω)
  apply hP1
  refine hOut p hp hp2 P hPp ?_
  rintro e he ⟨y, rfl⟩
  have hy : y ∈ kaInner P := he
  rw [hbot, Subgroup.mem_bot] at hy
  rw [hy, map_one]

theorem ka_out_triv_of_sq_inner (hsq : ∀ σ : MulAut Y, σ * σ ∈ innSub Y) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P →
      (∀ e ∈ P, e ∈ innSub Y → e = 1) → P = ⊥ := by
  intro p hp hp2 P hPp hPi
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup (Y := MulAut Y) hp hp2 hPp he
  obtain ⟨m, hm⟩ := hodd
  have h1 : e = (e * e) ^ (m + 1) := by
    calc e = e ^ (2 * m + 1) * e := by rw [← hm, pow_orderOf_eq_one, one_mul]
      _ = e ^ (2 * (m + 1)) := by rw [← pow_succ]; congr 1
      _ = (e * e) ^ (m + 1) := by rw [pow_mul, sq]
  exact hPi e he (by rw [h1]; exact (innSub Y).pow_mem (hsq e) _)

end Engine

section Cover

variable {p f : ℕ} {F : Type} [Field F]

theorem cover_injective_q3 (h : UnitaryFieldData p f F) (hq3 : p ^ f = 3) {K : Type} [Group K]
    {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ) : Function.Injective θ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : g ∈ θ.ker := hg
  rw [hθ.ker, mem_unitaryScalars] at hg'
  obtain ⟨c, hc, hc3, hcg⟩ := hg'
  have hbar : h.bar (c : F) = (c : F) ^ 3 := by rw [UnitaryFieldData.bar_apply, hq3]
  have hc4 : (c : F) ^ 4 = 1 := by
    have := hc
    rw [UnitaryFieldData.norm, hbar] at this
    linear_combination this
  have hc3' : (c : F) ^ 3 = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hc3
  have hc1 : (c : F) = 1 := by linear_combination hc4 - (c : F) * hc3'
  have hc1' : c = 1 := Units.ext hc1
  apply Subtype.ext
  rw [hcg, hc1', map_one]
  rfl

theorem conj_injective_q3 (h : UnitaryFieldData p f F) (hp : p ≠ 2) (hq3 : p ^ f = 3) {K : Type}
    [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  have hθi := cover_injective_q3 h hq3 hθ
  rw [injective_iff_map_eq_one]
  intro k hk
  obtain ⟨g, rfl⟩ := hθ.surj k
  have hcen : g ∈ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun φ : MulAut K => φ (θ x)) hk
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    apply hθi
    rw [map_mul, map_mul]
    calc θ x * θ g = (θ g * θ x * (θ g)⁻¹) * θ g := by rw [h1]
      _ = θ g * θ x := by group
  rw [(CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp (le_refl 3)).2] at hcen
  have : g ∈ θ.ker := by
    rw [hθ.ker]
    exact hcen
  exact this

theorem card_eq_6048_of_equiv (h : UnitaryFieldData p f F) (hq3 : p ^ f = 3) {K : Type} [Group K]
    (e : K ≃* StatedProj (StatedSU 3 (p ^ f) F)) : Nat.card K = 6048 := by
  have h1 : Nat.card K = psu3Order (p ^ f) :=
    (Nat.card_congr e.toEquiv).trans (card_statedProj_su3 h)
  rw [h1, hq3]
  norm_num [psu3Order]

end Cover

section Orders

variable {Y : Type} [Group Y]

theorem pGroup_eq_bot_of_not_dvd [Finite Y] {p : ℕ} (hp : p.Prime) {X : Subgroup Y}
    (hX : IsPGroup p ↥X) (hnd : ¬ p ∣ Nat.card Y) : X = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  by_cases ha0 : a = 0
  · exact Subgroup.eq_bot_of_card_eq _ (by simpa [ha0] using ha)
  · exfalso
    apply hnd
    have h1 : p ∣ Nat.card ↥X := ha ▸ dvd_pow_self p ha0
    exact h1.trans (Subgroup.card_subgroup_dvd_card X)

theorem pow_seven_eq_one_of_pGroup [Finite Y] (hY : Nat.card Y = 6048) {X : Subgroup Y}
    (hX : IsPGroup 7 ↥X) : ∀ x ∈ X, x ^ 7 = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  have hdvd : Nat.card ↥X ∣ 6048 := hY ▸ Subgroup.card_subgroup_dvd_card X
  have ha1 : a ≤ 1 := by
    by_contra hne
    have h2 : 2 ≤ a := by omega
    have h49 : 7 ^ 2 ∣ 6048 := (pow_dvd_pow 7 h2).trans (ha ▸ hdvd)
    norm_num at h49
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
  have hc : Nat.card ↥X ∣ 7 := by
    rw [ha]
    interval_cases a <;> simp
  have h2 : (⟨x, hx⟩ : ↥X) ^ 7 = 1 := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, pow_mul, h1, one_pow]
  have := congrArg Subtype.val h2
  simpa using this

theorem card_eq_seven_of_pGroup [Finite Y] (hY : Nat.card Y = 6048) {X : Subgroup Y}
    (hX : IsPGroup 7 ↥X) (hX1 : X ≠ ⊥) : Nat.card ↥X = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  have hdvd : Nat.card ↥X ∣ 6048 := hY ▸ Subgroup.card_subgroup_dvd_card X
  have ha1 : a ≤ 1 := by
    by_contra hne
    have h2 : 2 ≤ a := by omega
    have h49 : 7 ^ 2 ∣ 6048 := (pow_dvd_pow 7 h2).trans (ha ▸ hdvd)
    norm_num at h49
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hX1 (Subgroup.eq_bot_of_card_eq _ (by simpa using ha))
  have : a = 1 := by omega
  rw [ha, this, pow_one]

theorem not_dvd_6048 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7) :
    ¬ p ∣ 6048 := by
  intro hd
  have h6048 : (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 := by norm_num
  rw [h6048] at hd
  rcases hp.dvd_mul.mp hd with h' | h'
  · rcases hp.dvd_mul.mp h' with h'' | h''
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h''))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h''))
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h')

end Orders

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
