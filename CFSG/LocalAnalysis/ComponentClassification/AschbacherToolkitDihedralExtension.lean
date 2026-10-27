module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {Q : Type*} [Group Q]

theorem dihedral_central_extension_card_le (f : P →* Q) (hf : Function.Surjective f)
    (hK : f.ker ≤ Subgroup.center P) (hQ : HasDihedralGenerators Q) :
    Nat.card (f.ker ⊓ commutator P : Subgroup P) ≤ 2 := by
  classical
  have : Finite Q := Finite.of_surjective f hf
  obtain ⟨xb, yb, hgenb, hyb2, hybx, -⟩ := hQ
  obtain ⟨x, hx⟩ := hf xb
  obtain ⟨y, hy⟩ := hf yb
  set c := y * x * y⁻¹ * x with hc
  have hcK : c ∈ f.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, hx, hy, hybx,
      inv_mul_cancel]
  have hcz : ∀ g : P, g * c = c * g := Subgroup.mem_center_iff.mp (hK hcK)
  have hcz' : ∀ g : P, g * c⁻¹ = c⁻¹ * g :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (hK hcK))
  have hyx : y * x * y⁻¹ = c * x⁻¹ := by rw [hc]; group
  set w := x * x * c⁻¹ with hw
  have hxw : x * w * x⁻¹ = w := by
    calc x * w * x⁻¹ = x * x * (x * c⁻¹) * x⁻¹ := by rw [hw]; group
      _ = x * x * (c⁻¹ * x) * x⁻¹ := by rw [hcz' x]
      _ = w := by rw [hw]; group
  have hyw : y * w * y⁻¹ = w⁻¹ := by
    calc y * w * y⁻¹ = (y * x * y⁻¹) * (y * x * y⁻¹) * (y * c⁻¹ * y⁻¹) := by rw [hw]; group
      _ = c * x⁻¹ * (c * x⁻¹) * (c⁻¹ * y * y⁻¹) := by rw [hyx, hcz' y]
      _ = c * (x⁻¹ * c) * x⁻¹ * c⁻¹ := by group
      _ = c * (c * x⁻¹) * x⁻¹ * c⁻¹ := by rw [hcz x⁻¹]
      _ = c * c * (x⁻¹ * x⁻¹ * c⁻¹) := by group
      _ = c * c * (c⁻¹ * (x⁻¹ * x⁻¹)) := by rw [hcz' (x⁻¹ * x⁻¹)]
      _ = w⁻¹ := by rw [hw]; group
  have hxy : ⁅x, y⁆ = w := by
    calc ⁅x, y⁆ = x * (y * x * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      _ = x * (c * x⁻¹)⁻¹ := by rw [hyx]
      _ = x * (x * c⁻¹) := by group
      _ = w := by rw [hw]; group
  let S : Set P := insert x (insert y (f.ker : Set P))
  have hS : Subgroup.closure S = ⊤ := by
    have hmap : (Subgroup.closure S).map f = ⊤ := by
      rw [eq_top_iff, ← hgenb]
      apply sup_le
      · rw [Subgroup.zpowers_le]
        exact ⟨x, Subgroup.subset_closure (by simp [S]), hx⟩
      · rw [Subgroup.zpowers_le]
        exact ⟨y, Subgroup.subset_closure (by simp [S]), hy⟩
    have hker : f.ker ≤ Subgroup.closure S := fun k hk =>
      Subgroup.subset_closure (by simp [S, hk])
    have h := Subgroup.comap_map_eq f (Subgroup.closure S)
    rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hker] at h
    exact h.symm
  have hnorm : (Subgroup.zpowers w).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hS, Subgroup.closure_le]
    rintro s (rfl | rfl | hs)
    · exact mem_normalizer_zpowers_of_conj (Or.inl hxw)
    · exact mem_normalizer_zpowers_of_conj (Or.inr hyw)
    · refine mem_normalizer_zpowers_of_conj (Or.inl ?_)
      have := Subgroup.mem_center_iff.mp (hK hs) w
      rw [← this]
      group
  have hcentral : ∀ s t : P, s ∈ f.ker → ⁅s, t⁆ = 1 ∧ ⁅t, s⁆ = 1 := by
    intro s t hs
    have := Subgroup.mem_center_iff.mp (hK hs) t
    exact ⟨commutatorElement_eq_one_iff_mul_comm.mpr this.symm,
      commutatorElement_eq_one_iff_mul_comm.mpr this⟩
  have hD : commutator P ≤ Subgroup.zpowers w := by
    refine commutator_le_of_closure_eq_top _ hS ?_
    intro s hs t ht
    rcases hs with rfl | rfl | hs
    · rcases ht with rfl | rfl | ht
      · rw [commutatorElement_self]; exact Subgroup.one_mem _
      · rw [hxy]; exact Subgroup.mem_zpowers _
      · rw [(hcentral t s ht).2]; exact Subgroup.one_mem _
    · rcases ht with rfl | rfl | ht
      · rw [← commutatorElement_inv, hxy]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · rw [commutatorElement_self]; exact Subgroup.one_mem _
      · rw [(hcentral t s ht).2]; exact Subgroup.one_mem _
    · rw [(hcentral s t hs).1]; exact Subgroup.one_mem _
  set N := orderOf xb with hN
  have hxN : x ^ N ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx, hN, pow_orderOf_eq_one]
  have hxNz : ∀ g : P, g * x ^ N = x ^ N * g := Subgroup.mem_center_iff.mp (hK hxN)
  have hkey : (c * x⁻¹) ^ N = x ^ N := by
    rw [← hyx, conj_pow]
    calc y * x ^ N * y⁻¹ = (y * x ^ N) * y⁻¹ := rfl
      _ = (x ^ N * y) * y⁻¹ := by rw [hxNz y]
      _ = x ^ N := by group
  have hcomm1 : Commute c x⁻¹ := (hcz x⁻¹).symm
  have hcomm2 : Commute (x * x) c⁻¹ := hcz' (x * x)
  have hcn : c ^ N = x ^ N * x ^ N := by
    rw [hcomm1.mul_pow, inv_pow] at hkey
    calc c ^ N = c ^ N * (x ^ N)⁻¹ * x ^ N := by group
      _ = x ^ N * x ^ N := by rw [hkey]
  have hwN : w ^ N = 1 := by
    rw [hw, hcomm2.mul_pow, (Commute.refl x).mul_pow, inv_pow, ← hcn, mul_inv_cancel]
  have hfw : f w = xb ^ 2 := by
    rw [hw, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hcK, hx, inv_one, mul_one, sq]
  set m := orderOf (f w) with hm
  have hle : f.ker ⊓ commutator P ≤ Subgroup.zpowers (w ^ m) := by
    intro z hz
    obtain ⟨hzK, hzD⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hD hzD)
    rw [MonoidHom.mem_ker, map_zpow] at hzK
    obtain ⟨j, hj⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hzK
    rw [hj, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
  have hNm : N ∣ 2 * m := by
    have h1 : m = N / Nat.gcd N 2 := by
      rw [hm, hfw, orderOf_pow' _ two_ne_zero]
    have h2 : m * Nat.gcd N 2 = N := by
      rw [h1]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left N 2)
    calc N = m * Nat.gcd N 2 := h2.symm
      _ ∣ m * 2 := Nat.mul_dvd_mul_left m (Nat.gcd_dvd_right N 2)
      _ = 2 * m := mul_comm m 2
  have hwm : (w ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm]
    obtain ⟨q, hq⟩ := hNm
    rw [hq, pow_mul, hwN, one_pow]
  calc Nat.card (f.ker ⊓ commutator P : Subgroup P)
      ≤ Nat.card (Subgroup.zpowers (w ^ m)) := Subgroup.card_le_of_le hle
    _ = orderOf (w ^ m) := Nat.card_zpowers _
    _ ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hwm)

end CFSG.ComponentClassification.AschbacherToolkit
