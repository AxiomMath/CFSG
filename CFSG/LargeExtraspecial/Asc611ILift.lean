module

public import CFSG.LargeExtraspecial.AS35LInvA
public import CFSG.LargeExtraspecial.Asc611Uni

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem exists_scalar_of_mem_center (hm : 3 ≤ m) {g : SUid frob m}
    (hg : g ∈ center (SUid frob m)) : ∃ c : K, ∀ x : Fin m → K, g • x = c • x := by
  rw [center_SUid hm] at hg
  exact exists_smul_eq_of_mem_scalars hg

theorem exists_pow_scalar (hm : 3 ≤ m) {U : Subgroup (PG m)} (hU : IsPGroup 2 U)
    {g : SUid frob m} (hg : (QuotientGroup.mk g : PG m) ∈ U) :
    ∃ r : ℕ, ∃ c : K, ∀ x : Fin m → K, (g ^ 2 ^ r) • x = c • x := by
  obtain ⟨r, hr⟩ := hU ⟨_, hg⟩
  have h1 : (QuotientGroup.mk (g ^ 2 ^ r) : PG m) = 1 := by
    rw [QuotientGroup.mk_pow]
    simpa using congrArg Subtype.val hr
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hm ((QuotientGroup.eq_one_iff _).mp h1)
  exact ⟨r, c, hc⟩

theorem comm_of_mk_comm (hm : 3 ≤ m) {e a : SUid frob m} (he : e * e = 1)
    (h : (QuotientGroup.mk a : PG m) * QuotientGroup.mk e =
      QuotientGroup.mk e * QuotientGroup.mk a) : a * e = e * a := by
  set z := a * e * a⁻¹ * e⁻¹ with hz
  have hzc : z ∈ center (SUid frob m) := by
    rw [← QuotientGroup.eq_one_iff, hz, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h]
    group
  have hz3 := AS35U.pow_three_eq_one_of_mem_center hm hzc
  have hze : a * e * a⁻¹ = z * e := by rw [hz]; group
  have hz2 : z * z = 1 := by
    have h2 : (a * e * a⁻¹) * (a * e * a⁻¹) = 1 := by
      rw [show (a * e * a⁻¹) * (a * e * a⁻¹) = a * (e * e) * a⁻¹ by group, he, mul_one,
        mul_inv_cancel]
    rw [hze] at h2
    have hcomm : e * z = z * e := (Subgroup.mem_center_iff.mp hzc e)
    calc z * z = z * z * (e * e) := by rw [he, mul_one]
      _ = z * (z * e) * e := by group
      _ = z * (e * z) * e := by rw [hcomm]
      _ = z * e * (z * e) := by group
      _ = 1 := h2
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2, inv_one, one_mul]
  have : a * e * a⁻¹ * e⁻¹ = 1 := hz1
  calc a * e = a * e * a⁻¹ * e⁻¹ * (e * a) := by group
    _ = e * a := by rw [this, one_mul]

theorem three_dvd_two_pow_add_one (r : ℕ) : 3 ∣ 2 ^ (2 * r + 1) + 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨4 * t - 1, ?_⟩
    have : 2 ^ (2 * (r + 1) + 1) = 4 * 2 ^ (2 * r + 1) := by ring
    omega

theorem exists_lift (hm : 3 ≤ m) {e : SUid frob m} (he : e * e = 1) {U : Subgroup (PG m)}
    (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)))
    {u : PG m} (hu : u ∈ U) :
    ∃ k : SUid frob m, (QuotientGroup.mk k : PG m) = u ∧ k * e = e * k ∧
      ∃ r : ℕ, k ^ 2 ^ r = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨r, hr⟩ := hU ⟨_, hu⟩
  have hg1 : (QuotientGroup.mk g : PG m) ^ 2 ^ r = 1 := by
    simpa using congrArg Subtype.val hr
  have hzc : g ^ 2 ^ r ∈ center (SUid frob m) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hg1]
  set k := g ^ (2 ^ (2 * r + 1) + 1) with hk
  have hmk : (QuotientGroup.mk k : PG m) = QuotientGroup.mk g := by
    rw [hk, QuotientGroup.mk_pow, pow_succ, show 2 ^ (2 * r + 1) = 2 ^ r * 2 ^ (r + 1) by ring,
      pow_mul, hg1, one_pow, one_mul]
  refine ⟨k, hmk, ?_, r, ?_⟩
  · apply comm_of_mk_comm hm he
    rw [hmk]
    exact mem_centralizer_singleton_iff.mp (hUC hu)
  · obtain ⟨t, ht⟩ := three_dvd_two_pow_add_one r
    rw [hk, ← pow_mul, mul_comm, pow_mul, ht, pow_mul,
      AS35U.pow_three_eq_one_of_mem_center hm hzc, one_pow]

theorem mk_comm_mem {e : SUid frob m} {U : Subgroup (PG m)}
    (hUN : ∀ c ∈ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)), ∀ u ∈ U,
      c * u * c⁻¹ ∈ U)
    {k c : SUid frob m} (hk : (QuotientGroup.mk k : PG m) ∈ U) (hc : c * e = e * c) :
    (QuotientGroup.mk (k * c * k⁻¹ * c⁻¹) : PG m) ∈ U := by
  have hcC : (QuotientGroup.mk c : PG m) ∈
      centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m)) := by
    rw [mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
  have := Asc611.commutator_mem (hUN _ hcC) hk
  simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this

end CFSG.LargeExtraspecial.Asc611I
