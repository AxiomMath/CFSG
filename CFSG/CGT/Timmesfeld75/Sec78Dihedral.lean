module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.Sec7One

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Dihedral

variable {G : Type*} [Group G] {x y : G} {k r : ℕ}

theorem dih_pow_two_mul (ho : orderOf (x * y) = 2 * k) : (x * y) ^ (2 * k) = 1 := by
  rw [← ho]
  exact pow_orderOf_eq_one _

theorem dih_conj (hx2 : x * x = 1) (hy2 : y * y = 1) (hk : Odd k) (ho : orderOf (x * y) = 2 * k) :
    (x * y) ^ ((k + 1) / 2) * y * ((x * y) ^ ((k + 1) / 2))⁻¹ = x * (x * y) ^ k := by
  have h := dihedral_center_mul_conj hx2 hy2 hk (dih_pow_two_mul ho)
  rw [← h]
  exact (dihedral_center_comm hx2 hy2 (dih_pow_two_mul ho)).1.symm

theorem dih_odd_conj (hx2 : x * x = 1) (hy2 : y * y = 1) (hr : Odd r)
    (ho : orderOf (x * y) = r) :
    (x * y) ^ ((r + 1) / 2) * y * ((x * y) ^ ((r + 1) / 2))⁻¹ = x := by
  have h1 : (x * y) ^ r = 1 := by
    rw [← ho]
    exact pow_orderOf_eq_one _
  have h2 : (x * y) ^ (2 * r) = 1 := by rw [mul_comm, pow_mul, h1, one_pow]
  have h := dihedral_center_mul_conj hx2 hy2 hr h2
  rw [h1, one_mul] at h
  exact h.symm

end Dihedral

structure BadConfig78 {G : Type} [Group G] (T : Subgroup G) (x z y : G) (k : ℕ) : Prop where
  xT : x ∈ T
  x1 : x ≠ 1
  zN : z ∈ normD T
  zT : z ∉ T
  xz : x * z = z * x
  xzD : x * z ∉ classD T
  yD : y ∈ classD T
  yc : y * (x * z) = (x * z) * y
  odd : Odd k
  three : 3 ≤ k
  ord : orderOf (x * y) = 2 * k
  cz : (x * y) ^ k = x * z

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.badConfig_of_pair (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {x y : G} (hxT : x ∈ T) (hx1 : x ≠ 1)
    (hy : y ∈ classD T) {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) (ho : orderOf (x * y) = 2 * k) :
    BadConfig78 T x (x * (x * y) ^ k) y k := by
  have hTwc := hc.hy.pair.wc
  have hTab := hTwc.1
  have hx2 : x * x = 1 := elemAbelian_mul_self hTab hxT
  have hy2 : y * y = 1 := mul_self_eq_one_of_mem_classD hTab hy
  have hxD : x ∈ classD T := mem_classD_of_mem hxT hx1
  obtain ⟨hcx, hcy⟩ := dihedral_center_comm hx2 hy2 (dih_pow_two_mul ho)
  have hxc : x * (x * (x * y) ^ k) = (x * y) ^ k := by
    rw [← mul_assoc, hx2, one_mul]
  have hxz : x * (x * (x * y) ^ k) = (x * (x * y) ^ k) * x := by
    rw [mul_assoc, ← hcx]
  have hzD : x * (x * y) ^ k ∈ classD T := by
    rw [← dih_conj hx2 hy2 hk ho]
    exact classD_conj_mul hy _
  have hzN : x * (x * y) ^ k ∈ Subgroup.normalizer (T : Set G) :=
    hTwc.centralizer_le_normalizer hxT hx1 (Subgroup.mem_centralizer_singleton_iff.2 hxz.symm)
  refine ⟨hxT, hx1, ⟨hzD, hzN⟩, fun hzT => ?_, hxz, ?_, hy, ?_, hk, hk3, ho, hxc.symm⟩
  · apply hc.false_of_center_mem_T h1 h62 h63 hA8 hnat hxD hy hk3 ho
    rw [← hxc]
    exact T.mul_mem hxT hzT
  · rw [hxc]
    intro hD
    exact hc.false_of_center_mem_D h1 h62 h63 hA8 hnat hxD hy hk3 ho hD
  · rw [hxc]
    exact hcy

end CFSG.CGT.Timmesfeld75
