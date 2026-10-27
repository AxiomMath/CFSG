module

public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Util

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

section Twist

variable {G : Type*} [Group G]

theorem exists_fixed_of_twist {z r x : G} (hz : z * z = 1) (hx : x = r⁻¹ * (z * r * z⁻¹))
    (hodd : Odd (orderOf x)) : ∃ y ∈ Subgroup.zpowers x, z * (r * y) * z⁻¹ = r * y := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzx : z * x * z⁻¹ = x⁻¹ := by
    have h1 : x⁻¹ = z * r⁻¹ * z * r := by
      rw [hx, hz']
      simp [mul_assoc, hz']
    rw [h1, hx, hz']
    calc z * (r⁻¹ * (z * r * z)) * z = z * r⁻¹ * z * r * (z * z) := by group
      _ = z * r⁻¹ * z * r := by rw [hz, mul_one]
  obtain ⟨k, hk⟩ := hodd
  set y := x ^ (k + 1) with hy
  have hy2 : y * y = x := by
    have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    calc y * y = x ^ (k + 1) * x ^ (k + 1) := rfl
      _ = x ^ (2 * k + 1) * x := by rw [← pow_add, ← pow_succ]; ring_nf
      _ = x := by rw [← hk, h1, one_mul]
  have hzy : z * y * z⁻¹ = y⁻¹ := by
    have : z * x ^ (k + 1) * z⁻¹ = (z * x * z⁻¹) ^ (k + 1) := (conj_pow).symm
    rw [hy, this, hzx, inv_pow]
  refine ⟨y, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, ?_⟩
  have hzr : z * r * z⁻¹ = r * x := by rw [hx]; group
  calc z * (r * y) * z⁻¹ = (z * r * z⁻¹) * (z * y * z⁻¹) := by group
    _ = (r * x) * y⁻¹ := by rw [hzr, hzy]
    _ = r * y := by rw [← hy2]; group

end Twist

section Lift

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_toBar_eq_one (z : G) {x : ↥(Cen z)} (hx : x * x = 1) (h : toBar z x = 1) :
    x = 1 := by
  have hmem : x ∈ (toBar z).ker := h
  have h1 : orderOf x ∣ Nat.card (toBar z).ker := Subgroup.orderOf_dvd_natCard _ hmem
  exact eq_one_of_mul_self_of_odd hx ((odd_card_ker_toBar z).of_dvd_nat h1)

theorem eq_one_or_eq_z_of_toBar (z : G) (hz : z * z = 1) {x : ↥(Cen z)} (hx : x * x = 1)
    (h : toBar z x = 1 ∨ toBar z x = toBar z ⟨z, mem_Cen_self z⟩) :
    x = 1 ∨ x = ⟨z, mem_Cen_self z⟩ := by
  rcases h with h | h
  · exact Or.inl (eq_one_of_toBar_eq_one z hx h)
  · right
    set zc : ↥(Cen z) := ⟨z, mem_Cen_self z⟩ with hzc
    have hzc2 : zc * zc = 1 := Subtype.ext hz
    have hcomm : x * zc = zc * x :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2 z (Set.mem_singleton z)).symm
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have h1 : x⁻¹ * zc = 1 := by
      apply eq_one_of_toBar_eq_one z
      · rw [hx']
        calc x * zc * (x * zc) = x * (zc * x) * zc := by group
          _ = x * (x * zc) * zc := by rw [hcomm]
          _ = (x * x) * (zc * zc) := by group
          _ = 1 := by rw [hx, hzc2, one_mul]
      · rw [map_mul, map_inv, h, inv_mul_cancel]
    exact inv_mul_eq_one.1 h1

theorem exists_lift_centralizer (z : G) {t : ↥(Cen z)} (ht : t * t = 1) {m : CentralizerBar z}
    (hm : m * toBar z t = toBar z t * m) : ∃ x : ↥(Cen z), toBar z x = m ∧ x * t = t * x := by
  obtain ⟨x₀, rfl⟩ := toBar_surjective z m
  have hx : x₀⁻¹ * (t * x₀ * t⁻¹) ∈ (toBar z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv]
    calc (toBar z x₀)⁻¹ * (toBar z t * toBar z x₀ * (toBar z t)⁻¹)
        = (toBar z x₀)⁻¹ * (toBar z x₀ * toBar z t * (toBar z t)⁻¹) := by rw [← hm]
      _ = 1 := by group
  have hodd : Odd (orderOf (x₀⁻¹ * (t * x₀ * t⁻¹))) :=
    (odd_card_ker_toBar z).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  obtain ⟨y, hy, hfix⟩ := exists_fixed_of_twist (z := t) (r := x₀) ht rfl hodd
  have hyker : y ∈ (toBar z).ker := (Subgroup.zpowers_le.2 hx) hy
  refine ⟨x₀ * y, ?_, ?_⟩
  · rw [map_mul, MonoidHom.mem_ker.1 hyker, mul_one]
  · exact (mul_inv_eq_iff_eq_mul.1 hfix).symm

end Lift

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
