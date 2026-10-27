module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

open Subgroup

variable {G : Type*} [Group G]

@[expose] def dsub (w t : G) : Subgroup G := zpowers w ⊔ zpowers t

structure BareDatum (e : ℕ) (w t : G) : Prop where
  order_w : orderOf w = 2 ^ (e + 1)
  t_sq : t * t = 1
  t_inv : t * w * t = w⁻¹
  t_not_mem : t ∉ zpowers w

namespace BareDatum

variable {e : ℕ} {w t : G} (hd : BareDatum e w t)
include hd

theorem inv_t : t⁻¹ = t := inv_eq_of_mul_eq_one_right hd.t_sq

theorem t_zpow (i : ℤ) : t * w ^ i = w ^ (-i) * t := by
  have h := hd.t_inv
  have h2 : t * w * t⁻¹ = w⁻¹ := by rw [hd.inv_t]; exact h
  have h3 : t * w ^ i * t⁻¹ = (w ^ i)⁻¹ := by rw [← conj_zpow, h2, inv_zpow']; simp
  calc t * w ^ i = t * w ^ i * t⁻¹ * t := by group
    _ = w ^ (-i) * t := by rw [h3, zpow_neg]

theorem zpow_t (i : ℤ) : w ^ i * t = t * w ^ (-i) := by
  rw [hd.t_zpow (-i), neg_neg]

theorem refl_sq (i : ℤ) : (w ^ i * t) * (w ^ i * t) = 1 := by
  calc (w ^ i * t) * (w ^ i * t) = w ^ i * (t * w ^ i) * t := by group
    _ = w ^ i * (w ^ (-i) * t) * t := by rw [hd.t_zpow]
    _ = w ^ i * w ^ (-i) * (t * t) := by group
    _ = 1 := by rw [hd.t_sq, ← zpow_add]; simp

theorem refl_ne_one (i : ℤ) : w ^ i * t ≠ 1 := by
  intro h
  apply hd.t_not_mem
  have : t = (w ^ i)⁻¹ := by
    calc t = (w ^ i)⁻¹ * (w ^ i * t) := by group
      _ = (w ^ i)⁻¹ := by rw [h, mul_one]
  rw [this]
  exact inv_mem (zpow_mem_zpowers w i)

def explicit : Subgroup G where
  carrier := {g | ∃ i : ℤ, g = w ^ i ∨ g = w ^ i * t}
  mul_mem' := by
    rintro _ _ ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
    · exact ⟨i + j, Or.inl (zpow_add w i j).symm⟩
    · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · refine ⟨i - j, Or.inr ?_⟩
      calc w ^ i * t * w ^ j = w ^ i * (t * w ^ j) := by rw [mul_assoc]
        _ = w ^ i * (w ^ (-j) * t) := by rw [hd.t_zpow]
        _ = w ^ (i - j) * t := by rw [← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨i - j, Or.inl ?_⟩
      calc w ^ i * t * (w ^ j * t) = w ^ i * (t * w ^ j) * t := by group
        _ = w ^ i * (w ^ (-j) * t) * t := by rw [hd.t_zpow]
        _ = w ^ i * w ^ (-j) * (t * t) := by group
        _ = w ^ (i - j) := by rw [hd.t_sq, mul_one, ← zpow_add, sub_eq_add_neg]
  one_mem' := ⟨0, Or.inl (by simp)⟩
  inv_mem' := by
    rintro _ ⟨i, rfl | rfl⟩
    · exact ⟨-i, Or.inl (zpow_neg w i).symm⟩
    · refine ⟨i, Or.inr ?_⟩
      calc (w ^ i * t)⁻¹ = t⁻¹ * (w ^ i)⁻¹ := by rw [mul_inv_rev]
        _ = t * w ^ (-i) := by rw [hd.inv_t, zpow_neg]
        _ = w ^ i * t := (hd.zpow_t i).symm

theorem mem_dsub_iff {g : G} : g ∈ dsub w t ↔ ∃ i : ℤ, g = w ^ i ∨ g = w ^ i * t := by
  constructor
  · intro hg
    have hle : dsub w t ≤ hd.explicit := by
      apply sup_le
      · rw [zpowers_le]; exact ⟨1, Or.inl (by simp)⟩
      · rw [zpowers_le]; exact ⟨0, Or.inr (by simp)⟩
    exact hle hg
  · rintro ⟨i, rfl | rfl⟩
    · exact mem_sup_left (zpow_mem_zpowers w i)
    · exact mul_mem (mem_sup_left (zpow_mem_zpowers w i)) (mem_sup_right (mem_zpowers t))

theorem w_pow_order : w ^ (2 ^ (e + 1)) = 1 := by
  rw [← hd.order_w]; exact pow_orderOf_eq_one w

theorem center_sq : w ^ (2 ^ e) * w ^ (2 ^ e) = 1 := by
  rw [← pow_add, ← two_mul, ← pow_succ']
  exact hd.w_pow_order

theorem center_ne_one : w ^ (2 ^ e) ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hd.order_w] at this
  have h2 : 2 ^ (e + 1) ≤ 2 ^ e := Nat.le_of_dvd (by positivity) this
  have h3 : 2 ^ e < 2 ^ (e + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem eq_center_or_refl {g : G} (hg : g ∈ dsub w t) (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    g = w ^ (2 ^ e) ∨ ∃ i : ℤ, g = w ^ i * t := by
  obtain ⟨i, rfl | rfl⟩ := (hd.mem_dsub_iff).mp hg
  · left
    have h1 : w ^ (i + i) = 1 := by rw [zpow_add]; exact hg2
    have h2 : ((2 ^ (e + 1) : ℕ) : ℤ) ∣ i + i := by
      rw [← hd.order_w]; exact orderOf_dvd_iff_zpow_eq_one.mpr h1
    obtain ⟨j, hj⟩ : ((2 ^ e : ℕ) : ℤ) ∣ i := by
      refine Int.dvd_of_mul_dvd_mul_left (a := 2) (by norm_num) ?_
      have e1 : ((2 ^ (e + 1) : ℕ) : ℤ) = 2 * ((2 ^ e : ℕ) : ℤ) := by push_cast; ring
      rw [e1, ← two_mul] at h2
      exact h2
    have hc : w ^ i = (w ^ (2 ^ e)) ^ j := by
      rw [hj, zpow_mul, zpow_natCast]
    have hcc : (w ^ (2 ^ e)) ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hd.center_sq
    rw [hc] at hg1 ⊢
    rcases Int.even_or_odd' j with ⟨k, rfl | rfl⟩
    · exfalso; apply hg1
      rw [zpow_mul, hcc, one_zpow]
    · rw [zpow_add, zpow_mul, hcc, one_zpow, one_mul, zpow_one]
  · right; exact ⟨i, rfl⟩

theorem isPGroup : IsPGroup 2 (dsub w t) := by
  intro g
  refine ⟨e + 1, Subtype.ext ?_⟩
  obtain ⟨i, h | h⟩ := (hd.mem_dsub_iff).mp g.2
  · have : (g : G) ^ (2 ^ (e + 1)) = (w ^ (2 ^ (e + 1))) ^ i := by
      rw [h, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [Subgroup.coe_pow, this, hd.w_pow_order, one_zpow]
    rfl
  · have h2 : (g : G) * g = 1 := by rw [h]; exact hd.refl_sq i
    have h3 : (g : G) ^ 2 = 1 := by rw [pow_two]; exact h2
    rw [Subgroup.coe_pow, pow_succ', pow_mul, h3, one_pow]
    rfl

theorem nonempty_mulEquiv_dihedral [Finite G] :
    Nonempty (dsub w t ≃* DihedralGroup (2 ^ (e + 1))) := by
  classical
  let D : Subgroup G := dsub w t
  have hw : w ∈ D := mem_sup_left (mem_zpowers w)
  have ht : t ∈ D := mem_sup_right (mem_zpowers t)
  let ρ : D := ⟨w, hw⟩
  let σ : D := ⟨t, ht⟩
  have hgen : (⊤ : Subgroup D) = zpowers ρ ⊔ zpowers σ := by
    apply le_antisymm
    · intro x _
      have hmap : (zpowers ρ ⊔ zpowers σ).map D.subtype = dsub w t := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
      have hxmap : (x : G) ∈ (zpowers ρ ⊔ zpowers σ).map D.subtype := by
        rw [hmap]; exact x.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
      exact (Subtype.ext hyx) ▸ hy
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simpa [σ, pow_two] using hd.t_sq)
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simpa [σ, ρ, hd.inv_t] using hd.t_inv)
  have hσρ : σ ∉ zpowers ρ := by
    intro hmem
    apply hd.t_not_mem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact ⟨k, congrArg Subtype.val hk⟩
  have key := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = 2 ^ (e + 1) := by
    rw [← hd.order_w]; exact (orderOf_injective D.subtype D.subtype_injective ρ).symm
  rwa [hord] at key

end BareDatum


theorem bareDatum_zero {z t : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hzt : z ≠ t) (hcomm : z * t = t * z) : BareDatum 0 z t where
  order_w := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [orderOf_eq_prime (by rw [sq]; exact hz2) hz1]; norm_num
  t_sq := ht2
  t_inv := by
    rw [← hcomm, mul_assoc, ht2, mul_one, inv_eq_of_mul_eq_one_right hz2]
  t_not_mem := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
    intro hmem
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hmem
    have hmod : z ^ i = z ^ (i % 2) := by
      have := zpow_mod_orderOf z i
      rw [hord] at this
      simpa using this.symm
    have : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases this with h | h
    · rw [hmod, h] at hi; exact ht1 (by simpa using hi.symm)
    · rw [hmod, h] at hi; exact hzt (by simpa using hi)

structure Datum (𝒞 : Set G) (e : ℕ) (w t : G) : Prop extends BareDatum e w t where
  inv_mem : ∀ g ∈ dsub w t, g * g = 1 → g ≠ 1 → g ∈ 𝒞

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof
