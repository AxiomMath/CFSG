module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.AGLEmbedding.TrialityTwo

open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_smul_subgroup_iff_of_apply_eq {α : MulAut G} {x : G} (hx : α x = x)
    (Y : Subgroup G) : x ∈ α • Y ↔ x ∈ Y := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  have h : α⁻¹ x = x := by
    conv_lhs => rw [← hx]
    exact MulAut.inv_apply_self G α x
  rw [h]

theorem exists_mem_smul_family_iff {α : MulAut G} {x : G} (hx : α x = x)
    (F : Set (Subgroup G)) : (∃ Y ∈ α • F, x ∈ Y) ↔ ∃ Y ∈ F, x ∈ Y := by
  constructor
  · rintro ⟨_, hZ, hxY⟩
    obtain ⟨Y, hY, rfl⟩ := Set.mem_smul_set.mp hZ
    exact ⟨Y, hY, (mem_smul_subgroup_iff_of_apply_eq hx Y).mp hxY⟩
  · rintro ⟨Y, hY, hxY⟩
    exact ⟨α • Y, Set.smul_mem_smul_set hY, (mem_smul_subgroup_iff_of_apply_eq hx Y).mpr hxY⟩

theorem inv_eq_sq_of_pow_three_eq_one {α : MulAut G} (h3 : α ^ 3 = 1) : α⁻¹ = α ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h3])

theorem apply_mem_iInf_of_smul_mem {α : MulAut G} (h3 : α ^ 3 = 1) {S : Set (Subgroup G)}
    (hS : ∀ Y ∈ S, α • Y ∈ S) {y : G} (hy : y ∈ ⨅ Y ∈ S, Y) : α y ∈ ⨅ Y ∈ S, Y := by
  simp only [Subgroup.mem_iInf] at hy ⊢
  intro Y hY
  have h2 : (α ^ 2) • Y ∈ S := by
    rw [pow_two, mul_smul]
    exact hS _ (hS Y hY)
  have h := Subgroup.smul_mem_pointwise_smul y α _ (hy _ h2)
  rwa [MulAut.smul_def, ← mul_smul, ← pow_succ', h3, one_smul] at h

theorem map_iInf_eq_of_smul_mem {α : MulAut G} (h3 : α ^ 3 = 1) {S : Set (Subgroup G)}
    (hS : ∀ Y ∈ S, α • Y ∈ S) : (⨅ Y ∈ S, Y).map α.toMonoidHom = ⨅ Y ∈ S, Y := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact apply_mem_iInf_of_smul_mem h3 hS hy
  · intro z hz
    refine ⟨α⁻¹ z, ?_, MulAut.apply_inv_self G α z⟩
    rw [inv_eq_sq_of_pow_three_eq_one h3, pow_two, MulAut.mul_apply]
    exact apply_mem_iInf_of_smul_mem h3 hS (apply_mem_iInf_of_smul_mem h3 hS hz)

@[expose] def restrictAut (α : MulAut G) (L : Subgroup G) (hL : L.map α.toMonoidHom = L) :
    MulAut L :=
  (α.subgroupMap L).trans (MulEquiv.subgroupCongr hL)

theorem restrictAut_apply (α : MulAut G) (L : Subgroup G) (hL : L.map α.toMonoidHom = L)
    (y : L) : (restrictAut α L hL y : G) = α y := rfl

theorem restrictAut_pow_apply (α : MulAut G) (L : Subgroup G) (hL : L.map α.toMonoidHom = L)
    (n : ℕ) (y : L) : ((restrictAut α L hL ^ n) y : G) = (α ^ n) y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, restrictAut_apply]

theorem restrictAut_pow_three (α : MulAut G) (h3 : α ^ 3 = 1) (L : Subgroup G)
    (hL : L.map α.toMonoidHom = L) : restrictAut α L hL ^ 3 = 1 := by
  ext y
  rw [restrictAut_pow_apply, h3]
  rfl

theorem exists_pow_orderOf_prime_of_coprime_six {x : G} {n : ℕ} (hn : Nat.Coprime 6 n)
    (hxn : x ^ n = 1) (hx : x ≠ 1) :
    ∃ (p k : ℕ), p.Prime ∧ 5 ≤ p ∧ orderOf (x ^ k) = p := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by decide)
  have hdvd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hxn
  have ho0 : orderOf x ≠ 0 := fun h => hn0 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have ho1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  set p := (orderOf x).minFac
  have hp : p.Prime := Nat.minFac_prime ho1
  have hpo : p ∣ orderOf x := Nat.minFac_dvd _
  have hcop : Nat.Coprime 6 p := Nat.Coprime.coprime_dvd_right (hpo.trans hdvd) hn
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h2 := hp.two_le
    interval_cases hp' : p
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hp (by norm_num)
  exact ⟨p, orderOf x / p, hp, hp5, orderOf_pow_orderOf_div ho0 hpo⟩

theorem prime_eq_five_or_seven_of_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ∣ 174182400) : p = 5 ∨ p = 7 := by
  have hN : (174182400 : ℕ) = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 := by norm_num
  rw [hN] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)

end CFSG.AGLEmbedding.TrialityTwo
