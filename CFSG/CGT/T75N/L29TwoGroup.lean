module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups
open CFSG.LieType.Steinberg.CentralExt

@[expose] def twoPart {Y : Type} [Group Y] (K : Subgroup Y) (hK : K ≤ Subgroup.center Y) :
    Subgroup Y where
  carrier := {y | y ∈ K ∧ ∃ j : ℕ, y ^ (2 ^ j) = 1}
  one_mem' := ⟨K.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxK, i, hi⟩ ⟨hyK, j, hj⟩
    refine ⟨K.mul_mem hxK hyK, i + j, ?_⟩
    have hc : Commute x y := (Subgroup.mem_center_iff.1 (hK hxK) y).symm
    rw [hc.mul_pow, pow_add, pow_mul, hi, one_pow, mul_comm (2 ^ i), pow_mul, hj, one_pow,
      one_mul]
  inv_mem' := by
    rintro x ⟨hxK, i, hi⟩
    exact ⟨K.inv_mem hxK, i, by rw [inv_pow, hi, inv_one]⟩

instance twoPart_normal {Y : Type} [Group Y] (K : Subgroup Y) (hK : K ≤ Subgroup.center Y) :
    (twoPart K hK).Normal where
  conj_mem x hx g := by
    have h : g * x = x * g := Subgroup.mem_center_iff.1 (hK hx.1) g
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact hx

theorem isPGroup_two_ker
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (π : Y →* SpecialLinearGroup (Fin n) F) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center Y) : IsPGroup 2 π.ker := by
  classical
  have hK₂ker : twoPart π.ker hcen ≤ π.ker := fun y hy => hy.1
  let π₂ : Y ⧸ twoPart π.ker hcen →* SpecialLinearGroup (Fin n) F :=
    QuotientGroup.lift (twoPart π.ker hcen) π hK₂ker
  have hπ₂ : ∀ y : Y, π₂ (y : Y ⧸ twoPart π.ker hcen) = π y := fun y => rfl
  have hπ₂surj : Function.Surjective π₂ := fun g => by
    obtain ⟨y, rfl⟩ := hπ g
    exact ⟨y, rfl⟩
  have hperf₂ : Group.IsPerfect (Y ⧸ twoPart π.ker hcen) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (twoPart π.ker hcen))
      (QuotientGroup.mk'_surjective _)
  have hcen₂ : π₂.ker ≤ Subgroup.center (Y ⧸ twoPart π.ker hcen) := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : y ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₂]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hcen hy) y']
  have hodd₂ : Odd (Nat.card π₂.ker) := by
    by_contra hodd
    have h2 : 2 ∣ Nat.card π₂.ker := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := π₂.ker) 2 h2
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (x : Y ⧸ twoPart π.ker hcen)
    have hyK : y ∈ π.ker := by
      have := x.2
      rw [MonoidHom.mem_ker, ← hy, hπ₂] at this
      exact this
    have hx2 : (x : Y ⧸ twoPart π.ker hcen) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    rw [← hy, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hx2
    obtain ⟨-, j, hj⟩ := hx2
    have hyK₂ : y ∈ twoPart π.ker hcen := ⟨hyK, j + 1, by rw [pow_succ', pow_mul]; exact hj⟩
    have hx1 : x = 1 := Subtype.ext (by
      rw [← hy]
      exact (QuotientGroup.eq_one_iff y).2 hyK₂)
    rw [hx1, orderOf_one] at hx
    omega
  obtain ⟨s, hs, -, -⟩ := CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting
    hn hπ₂surj hcen₂ hodd₂
  have hbot : π₂.ker = ⊥ := SL2Closed.ker_eq_bot_of_section π₂ hcen₂ s hs
  intro x
  have hx : (x : Y) ∈ twoPart π.ker hcen := by
    have hx' : ((x : Y) : Y ⧸ twoPart π.ker hcen) ∈ π₂.ker := by
      rw [MonoidHom.mem_ker, hπ₂]
      exact x.2
    rw [hbot] at hx'
    exact (QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.1 hx')
  obtain ⟨-, j, hj⟩ := hx
  exact ⟨j, Subtype.ext hj⟩

end CFSG.CGT.T75N
