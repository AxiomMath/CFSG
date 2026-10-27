module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Perf

theorem pow_eq_self_of_pow_eq_one {Q : Type*} [Group Q] {q : Q} {m n : ℕ} (hq : q ^ m = 1)
    (hn : n % m = 1 % m) (hm : 1 < m) : q ^ n = q := by
  have h1 : q ^ n = q ^ (n % m) := by
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hq, one_pow, one_mul]
  rw [h1, hn, Nat.mod_eq_of_lt hm, pow_one]

theorem exists_lift_pow {Y Q : Type*} [Group Y] [Finite Y] [Group Q] (F : Y →* Q)
    (hker : IsPGroup 2 ↥F.ker) {q : Q} {m : ℕ} (hm : Odd m) (hq : q ^ m = 1)
    (hr : q ∈ F.range) : ∃ x : Y, F x = q ∧ x ^ m = 1 := by
  obtain ⟨x₁, hx₁⟩ := hr
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨1, ?_, by simp⟩
    rw [map_one]; simpa using hq.symm
  have hm2 : 1 < m := by
    rcases hm with ⟨k, rfl⟩
    omega
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hp : ∀ p ∈ F.ker, p ^ (2 ^ k) = 1 := by
    intro p hp
    have := pow_card_eq_one' (G := ↥F.ker) (x := ⟨p, hp⟩)
    rw [hk] at this
    simpa using congrArg Subtype.val this
  have hcop : Nat.Coprime (2 ^ k) m := by
    apply Nat.Coprime.pow_left
    exact Nat.coprime_two_left.mpr hm
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm2
  have hxm : x₁ ^ m ∈ F.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx₁, hq]
  refine ⟨x₁ ^ (2 ^ k * u), ?_, ?_⟩
  · rw [map_pow, hx₁]
    exact pow_eq_self_of_pow_eq_one hq (by rw [hu, Nat.mod_eq_of_lt hm2]) hm2
  · have : (x₁ ^ (2 ^ k * u)) ^ m = ((x₁ ^ m) ^ (2 ^ k)) ^ u := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [this, hp _ hxm, one_pow]

theorem conj_eq_of_central {Y Q : Type*} [Group Y] [Group Q] (F : Y →* Q)
    (hker : IsPGroup 2 ↥F.ker) (hc : F.ker ≤ Subgroup.center Y) {s t : Y} {m : ℕ} (hm : Odd m)
    (hs : s ^ m = 1) (hF : F (s * t * s⁻¹) = F t) : s * t * s⁻¹ = t := by
  set p : Y := s * t * s⁻¹ * t⁻¹ with hpdef
  have hpk : p ∈ F.ker := by
    rw [MonoidHom.mem_ker, hpdef]
    simp only [map_mul, map_inv, hF]
    group
  have hpc : ∀ y : Y, y * p = p * y := fun y =>
    Subgroup.mem_center_iff.mp (hc hpk) y
  have hj : ∀ j : ℕ, s ^ j * t * (s ^ j)⁻¹ = t * p ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : s ^ (j + 1) * t * (s ^ (j + 1))⁻¹ = s * (s ^ j * t * (s ^ j)⁻¹) * s⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [h1, ih]
      have h2 : s * (t * p ^ j) * s⁻¹ = (s * t * s⁻¹) * (s * p ^ j * s⁻¹) := by group
      have h3 : s * p ^ j * s⁻¹ = p ^ j := by
        rw [(Commute.pow_right (show Commute s p from hpc s) j).eq]; group
      have h4 : s * t * s⁻¹ = t * p := by
        have : s * t * s⁻¹ = p * t := by rw [hpdef]; group
        rw [this]; exact (hpc t).symm
      rw [h2, h3, h4, mul_assoc, ← pow_succ']
  have hpm : p ^ m = 1 := by
    have := hj m
    rw [hs] at this
    have h5 : t * p ^ m = t * 1 := by rw [mul_one, ← this]; group
    exact mul_left_cancel h5
  have hord : orderOf p ∣ m := orderOf_dvd_of_pow_eq_one hpm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hker) ⟨p, hpk⟩
  have hk' : orderOf p = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  rw [hk'] at hord
  have hcop : Nat.Coprime (2 ^ k) m := by
    apply Nat.Coprime.pow_left
    exact Nat.coprime_two_left.mpr hm
  have : 2 ^ k = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hord
  rw [this] at hk'
  have hp1 : p = 1 := orderOf_eq_one_iff.mp hk'
  rw [hpdef] at hp1
  exact mul_inv_eq_one.mp hp1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Perf
