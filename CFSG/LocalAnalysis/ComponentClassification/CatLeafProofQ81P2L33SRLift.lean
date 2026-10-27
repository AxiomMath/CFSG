module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRBase

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup

theorem exists_oddPow_of_not_isPGroup {G : Type*} [Group G] [Finite G] (h : ¬ IsPGroup 2 G) :
    ∃ x : G, ∃ m : ℕ, Odd m ∧ x ^ m = 1 ∧ x ≠ 1 := by
  have hG : ∃ g : G, ∀ k : ℕ, g ^ 2 ^ k ≠ 1 := by
    by_contra hc
    apply h
    intro g
    by_contra hg
    exact hc ⟨g, fun k hk => hg ⟨k, hk⟩⟩
  obtain ⟨g, hg⟩ := hG
  have hpos : 0 < orderOf g := orderOf_pos g
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  refine ⟨g ^ 2 ^ a, m, hm, ?_, hg a⟩
  rw [← pow_mul, ← hn, pow_orderOf_eq_one]

theorem not_isPGroup_inf_centralizer_of_central {G : Type*} [Group G] [Finite G] {Q : Type*}
    [Group Q] (M : Subgroup G) (κ : ↥M →* Q) (hκ : Function.Surjective κ)
    (hker : κ.ker ≤ center M) (hker2 : IsPGroup 2 ↥κ.ker) {s : G} (hs : s ∈ M)
    (hQ : ¬ IsPGroup 2 ↥(centralizer ({κ ⟨s, hs⟩} : Set Q))) :
    ¬ IsPGroup 2 ↥(M ⊓ centralizer ({s} : Set G)) := by
  have : Finite Q := Finite.of_surjective κ hκ
  obtain ⟨x, m, hm, hxm, hx1⟩ := exists_oddPow_of_not_isPGroup hQ
  obtain ⟨y0, hy0⟩ := hκ x
  have hk0 : y0 ^ m ∈ κ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy0]
    exact congrArg Subtype.val hxm
  obtain ⟨j, hj⟩ := hker2 ⟨y0 ^ m, hk0⟩
  have hj' : (y0 ^ m) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  set y := y0 ^ 2 ^ j with hydef
  have hym : y ^ m = 1 := by rw [hydef, ← pow_mul, mul_comm, pow_mul, hj']
  have hκy : κ y = (x : Q) ^ 2 ^ j := by rw [hydef, map_pow, hy0]
  have hcop : Nat.Coprime (orderOf (x : Q)) (2 ^ j) := by
    have h1 : orderOf (x : Q) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hxm
    exact Nat.Coprime.pow_right j ((Nat.coprime_two_right.mpr (Odd.of_dvd_nat hm h1)))
  have hy1 : κ y ≠ 1 := by
    rw [hκy]
    intro h2
    have h3 : orderOf (x : Q) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf (x : Q) = 1 := Nat.Coprime.eq_one_of_dvd hcop h3
    exact hx1 (Subtype.ext (orderOf_eq_one_iff.mp h4))
  have hcomm : κ y * κ ⟨s, hs⟩ = κ ⟨s, hs⟩ * κ y := by
    rw [hκy]
    have hx := mem_centralizer_singleton_iff.mp x.2
    exact (Commute.pow_left hx (2 ^ j)).eq
  set z := y * ⟨s, hs⟩ * y⁻¹ * (⟨s, hs⟩ : M)⁻¹ with hzdef
  have hz : z ∈ κ.ker := by
    rw [MonoidHom.mem_ker, hzdef, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hzc : z ∈ center M := hker hz
  have hconj : ∀ k : ℕ, y ^ k * ⟨s, hs⟩ * (y ^ k)⁻¹ = z ^ k * ⟨s, hs⟩ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzy : y * z ^ k = z ^ k * y := ((mem_center_iff.mp (pow_mem hzc k)) y)
      have hs' : y * ⟨s, hs⟩ * y⁻¹ = z * ⟨s, hs⟩ := by rw [hzdef]; group
      calc y ^ (k + 1) * ⟨s, hs⟩ * (y ^ (k + 1))⁻¹
          = y * (y ^ k * ⟨s, hs⟩ * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = y * (z ^ k * ⟨s, hs⟩) * y⁻¹ := by rw [ih]
        _ = z ^ k * (y * ⟨s, hs⟩ * y⁻¹) := by
          rw [← mul_assoc, hzy]
          group
        _ = z ^ (k + 1) * ⟨s, hs⟩ := by rw [hs', ← mul_assoc, ← pow_succ]
  have hzm : z ^ m = 1 := by
    have h := hconj m
    rw [hym, one_mul, inv_one, mul_one] at h
    exact (mul_eq_right.mp h.symm)
  have hz1 : z = 1 := by
    obtain ⟨i, hi⟩ := hker2 ⟨z, hz⟩
    have hi' : z ^ 2 ^ i = 1 := congrArg Subtype.val hi
    have hc : Nat.Coprime (orderOf z) (2 ^ i) := Nat.Coprime.pow_right i
      (Nat.coprime_two_right.mpr (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hzm)))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc (orderOf_dvd_of_pow_eq_one hi'))
  have hys : (y : G) * s = s * y := by
    have h := hconj 1
    rw [pow_one, pow_one, hz1, one_mul] at h
    have h' : (y : M) * ⟨s, hs⟩ = ⟨s, hs⟩ * y := by
      calc (y : M) * ⟨s, hs⟩ = y * ⟨s, hs⟩ * y⁻¹ * y := by group
        _ = ⟨s, hs⟩ * y := by rw [h]
    exact congrArg Subtype.val h'
  refine not_isPGroup_of_pow (g := (⟨(y : G), Subgroup.mem_inf.mpr ⟨y.2,
    mem_centralizer_singleton_iff.mpr hys⟩⟩ : ↥(M ⊓ centralizer ({s} : Set G)))) hm ?_ ?_
  · apply Subtype.ext
    simpa using congrArg Subtype.val hym
  · intro h1
    apply hy1
    have h2 : y = 1 := Subtype.ext (by simpa using congrArg Subtype.val h1)
    rw [h2, map_one]

end CFSG.ComponentClassification.HarrisLit.L33.SR
