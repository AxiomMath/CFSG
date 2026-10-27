module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Bad
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Surv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem not_cube_dvd_three_factorial_odd {q : ℕ} (hodd : q % 2 = 1) (hq5 : 5 ≤ q) :
    ¬ q ^ 3 ∣ 119750400 := by
  intro key
  have hle : q ^ 3 ≤ 119750400 := Nat.le_of_dvd (by norm_num) key
  have hq' : q ≤ 500 := by
    by_contra hcon
    have : 500 ^ 3 < q ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  clear hle
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  have hm : m ≤ 249 := by omega
  have hm1 : 2 ≤ m := by omega
  clear hodd hq5 hq'
  interval_cases m <;> omega

theorem isSimpleGroup_statedProj_three_odd [Fact p.Prime] (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f ≠ 2) : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ f) K)) :=
  CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 le_rfl (by
    intro h
    exact hq (Prod.mk.inj h).2)

omit [Finite K] in
theorem not_card_dvd_factorial_statedProj_three_odd [Fact p.Prime] (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hodd : p ^ f % 2 = 1) (hq5 : 5 ≤ p ^ f) :
    ¬ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) ∣ Nat.factorial 11 := by
  intro hdvd
  have hp : p.Prime := Fact.out
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (n := 3) hp hf hK
    (by norm_num)
  have e1 : (∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) =
      ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    have a1 : ((((p ^ f : ℕ) : ℤ)) ^ 2 - (-1) ^ 2).toNat = (p ^ f) ^ 2 - 1 := by
      have : (((p ^ f : ℕ) : ℤ)) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    have a2 : ((((p ^ f : ℕ) : ℤ)) ^ 3 - (-1) ^ 3).toNat = (p ^ f) ^ 3 + 1 := by
      have : (((p ^ f : ℕ) : ℤ)) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    rw [a1, a2]
  rw [e1] at hcard
  have hg3 : Nat.gcd 3 (p ^ f + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have hgd : Nat.gcd 3 (p ^ f + 1) ∣ (p ^ f) ^ 3 + 1 := by
    have h1 : p ^ f + 1 ∣ (p ^ f) ^ 3 + 1 ^ 3 :=
      Odd.nat_add_dvd_pow_add_pow (p ^ f) 1 (by decide)
    rw [one_pow] at h1
    exact dvd_trans (Nat.gcd_dvd_right _ _) h1
  have hmul : Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
    rw [hcard]
    exact Nat.div_mul_cancel
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hgd _) _)
  have key : (p ^ f) ^ 3 ∣ 3 * Nat.factorial 11 := by
    have h1 : (p ^ f) ^ 3 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) *
        Nat.gcd 3 (p ^ f + 1) := by
      rw [hmul]
      exact dvd_mul_right _ _
    rw [mul_comm 3]
    exact dvd_trans h1 (Nat.mul_dvd_mul hdvd hg3)
  have h3f : 3 * Nat.factorial 11 = 119750400 := by decide
  rw [h3f] at key
  exact not_cube_dvd_three_factorial_odd hodd hq5 key

theorem genericKill_of_su3_block [Fact p.Prime] [CharP K p] (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f) {P : Type} [Group P]
    (α : MulAut P) (θ : ↥(StatedSU 3 (p ^ f) K) →* P) (hθ : Function.Injective θ)
    (hfix : ∀ g, α (θ g) = θ g) : GenericKill P α := by
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hP3 := isPerfect_statedSU_three_odd (K := K) hK hp2
  have : Group.IsPerfect θ.range := Group.IsPerfect.range θ
  let c : ↥θ.range →* StatedProj (StatedSU 3 (p ^ f) K) :=
    (QuotientGroup.mk' _).comp (MonoidHom.ofInjective hθ).symm.toMonoidHom
  have hc : Function.Surjective c :=
    (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hθ).symm.surjective
  have hs := isSimpleGroup_statedProj_three_odd (K := K) hK (by omega)
  have : Group.IsPerfect (StatedProj (StatedSU 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : Nontrivial (StatedProj (StatedSU 3 (p ^ f) K)) := IsSimpleGroup.toNontrivial
  refine Or.inl ⟨θ.range, ‹_›, ?_, StatedProj (StatedSU 3 (p ^ f) K), inferInstance, hs, c, hc,
    Group.IsPerfect.not_isSolvable _, fun k => not_kindFactor hp2
      (involved_qdSL_statedProj_three hK)
      (not_card_dvd_factorial_statedProj_three_odd hf hK hodd hq5)⟩
  rintro _ ⟨g, rfl⟩
  exact hfix g

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
