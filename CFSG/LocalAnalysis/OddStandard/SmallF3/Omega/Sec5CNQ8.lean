module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNPi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNSL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {π : SL23 × SL23 →* G} {K₃ K₄ : Subgroup G} {z : G}

theorem sec5cn_pi_mul_mk (π : SL23 × SL23 →* G) (u v p q : SL23) :
    π (u, v) * π (p, q) = π (u * p, v * q) := by
  rw [← map_mul]
  rfl

theorem sec5cn_pi_pow_mk (π : SL23 × SL23 →* G) (u v : SL23) (n : ℕ) :
    π (u, v) ^ n = π (u ^ n, v ^ n) := by
  rw [← map_pow]
  rfl

theorem sec5cn_pi_inv_mk (π : SL23 × SL23 →* G) (u v : SL23) :
    (π (u, v))⁻¹ = π (u⁻¹, v⁻¹) := by
  rw [← map_inv]
  rfl

theorem Sec5CNPi.neg_left (h : Sec5CNPi π K₃ K₄ z) (u v : SL23) :
    π (-u, v) = z * π (u, v) := by
  have : ((-u : SL23), v) = ((-1 : SL23), (1 : SL23)) * (u, v) :=
    Prod.ext (sec5cn_neg_eq u) (one_mul v).symm
  rw [this, map_mul, h.left]

theorem Sec5CNPi.neg_right (h : Sec5CNPi π K₃ K₄ z) (u v : SL23) :
    π (u, -v) = z * π (u, v) := by
  have : (u, (-v : SL23)) = ((1 : SL23), (-1 : SL23)) * (u, v) :=
    Prod.ext (one_mul u).symm (sec5cn_neg_eq v)
  rw [this, map_mul, h.right]

theorem Sec5CNPi.neg_both (h : Sec5CNPi π K₃ K₄ z) (u v : SL23) :
    π (-u, -v) = π (u, v) := by
  rw [h.neg_left, h.neg_right, ← mul_assoc, h.z_sq, one_mul]

theorem Sec5CNPi.mk_mem (h : Sec5CNPi π K₃ K₄ z) (u v : SL23) : π (u, v) ∈ K₃ ⊔ K₄ :=
  h.mem_iff.mpr ⟨(u, v), rfl⟩

theorem Sec5CNPi.comm_iff (h : Sec5CNPi π K₃ K₄ z) (u v p q : SL23) :
    π (u, v) * π (p, q) = π (p, q) * π (u, v) ↔
      (p * u = u * p ∧ q * v = v * q) ∨ (p * u = -(u * p) ∧ q * v = -(v * q)) := by
  rw [sec5cn_pi_mul_mk, sec5cn_pi_mul_mk, h.eq_iff]
  constructor
  · rintro (h1 | h1)
    · left
      exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
    · right
      have h2 := congrArg Prod.fst h1
      have h3 := congrArg Prod.snd h1
      simp only [Prod.fst_mul, Prod.snd_mul] at h2 h3
      rw [sec5cn_mul_neg_one] at h2 h3
      exact ⟨h2, h3⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      exact Prod.ext h1 h2
    · right
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul]
        rw [sec5cn_mul_neg_one]
        exact h1
      · simp only [Prod.snd_mul]
        rw [sec5cn_mul_neg_one]
        exact h2

theorem Sec5CNPi.pow4_iff (h : Sec5CNPi π K₃ K₄ z) (u v : SL23) :
    π (u, v) ^ 4 = 1 ↔ u ^ 4 = 1 ∧ v ^ 4 = 1 := by
  constructor
  · intro h4
    have h1 : π ((u, v) ^ 4) = 1 := by rw [map_pow]; exact h4
    rcases h.ker _ h1 with h2 | h2
    · exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
    · exact absurd (congrArg Prod.fst h2) (sec5cn_pow4_ne_neg u)
  · rintro ⟨hu, hv⟩
    rw [sec5cn_pi_pow_mk, hu, hv]
    exact (map_one π : π 1 = 1)

theorem Sec5CNPi.invol (h : Sec5CNPi π K₃ K₄ z) {x : G} (hx : x ∈ K₃ ⊔ K₄) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hxz : x ≠ z) :
    ∃ u v : SL23, u * u = -1 ∧ v * v = -1 ∧ π (u, v) = x := by
  obtain ⟨⟨u, v⟩, rfl⟩ := h.mem_iff.mp hx
  have h1 : π ((u, v) * (u, v)) = 1 := by rw [map_mul]; exact hx2
  rcases h.ker _ h1 with h2 | h2
  · exfalso
    have hu : u * u = 1 := congrArg Prod.fst h2
    have hv : v * v = 1 := congrArg Prod.snd h2
    rcases h.sign_mem (sl23_unique_involution u hu) (sl23_unique_involution v hv) with h3 | h3
    · exact hx1 h3
    · exact hxz h3
  · exact ⟨u, v, congrArg Prod.fst h2, congrArg Prod.snd h2, rfl⟩

theorem Sec5CNPi.conj_q (h : Sec5CNPi π K₃ K₄ z) {x s : G} (hx : x ∈ K₃ ⊔ K₄)
    (hs : s ∈ K₃ ⊔ K₄) (hx4 : x ^ 4 = 1) (hs4 : s ^ 4 = 1) :
    x⁻¹ * s * x = s ∨ x⁻¹ * s * x = s * z := by
  obtain ⟨⟨p, q⟩, rfl⟩ := h.mem_iff.mp hx
  obtain ⟨⟨a, b⟩, rfl⟩ := h.mem_iff.mp hs
  obtain ⟨hp, hq⟩ := (h.pow4_iff p q).mp hx4
  obtain ⟨ha, hb⟩ := (h.pow4_iff a b).mp hs4
  have e : (π (p, q))⁻¹ * π (a, b) * π (p, q) = π (p⁻¹ * a * p, q⁻¹ * b * q) := by
    rw [sec5cn_pi_inv_mk, sec5cn_pi_mul_mk, sec5cn_pi_mul_mk]
  have hzc : z * π (a, b) = π (a, b) * z := h.z_comm (h.mk_mem a b)
  rw [e]
  rcases sec5cn_conj_q8 a p ha hp with h1 | h1 <;> rcases sec5cn_conj_q8 b q hb hq with h2 | h2
  · left
    rw [h1, h2]
  · right
    rw [h1, h2, h.neg_right, hzc]
  · right
    rw [h1, h2, h.neg_left, hzc]
  · left
    rw [h1, h2, h.neg_both]

theorem Sec5CNPi.comm_q (h : Sec5CNPi π K₃ K₄ z) {x y : G} (hx : x ∈ K₃ ⊔ K₄)
    (hy : y ∈ K₃ ⊔ K₄) (hx4 : x ^ 4 = 1) (hy4 : y ^ 4 = 1) :
    x * y = y * x ∨ x * y = z * (y * x) := by
  obtain ⟨⟨p, q⟩, rfl⟩ := h.mem_iff.mp hx
  obtain ⟨⟨a, b⟩, rfl⟩ := h.mem_iff.mp hy
  obtain ⟨hp, hq⟩ := (h.pow4_iff p q).mp hx4
  obtain ⟨ha, hb⟩ := (h.pow4_iff a b).mp hy4
  rw [sec5cn_pi_mul_mk, sec5cn_pi_mul_mk]
  rcases sec5cn_comm_q8 p a hp ha with h1 | h1 <;> rcases sec5cn_comm_q8 q b hq hb with h2 | h2
  · left
    rw [h1, h2]
  · right
    rw [h1, h2, h.neg_right]
  · right
    rw [h1, h2, h.neg_left]
  · left
    rw [h1, h2, h.neg_both]

theorem Sec5CNPi.div_q (h : Sec5CNPi π K₃ K₄ z) {x y : G} (hx : x ∈ K₃ ⊔ K₄)
    (hy : y ∈ K₃ ⊔ K₄) (hx4 : x ^ 4 = 1) (hy4 : y ^ 4 = 1) : (x⁻¹ * y) ^ 4 = 1 := by
  obtain ⟨⟨p, q⟩, rfl⟩ := h.mem_iff.mp hx
  obtain ⟨⟨a, b⟩, rfl⟩ := h.mem_iff.mp hy
  obtain ⟨hp, hq⟩ := (h.pow4_iff p q).mp hx4
  obtain ⟨ha, hb⟩ := (h.pow4_iff a b).mp hy4
  rw [sec5cn_pi_inv_mk, sec5cn_pi_mul_mk]
  exact (h.pow4_iff _ _).mpr ⟨sec5cn_q8_div p a hp ha, sec5cn_q8_div q b hq hb⟩

theorem Sec5CNPi.exists_swap (h : Sec5CNPi π K₃ K₄ z) {t : G} (ht : t ∈ K₃ ⊔ K₄)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z) :
    ∃ c ∈ K₃ ⊔ K₄, c ^ 4 = 1 ∧ c⁻¹ * t * c = t * z := by
  obtain ⟨u, v, hu, hv, rfl⟩ := h.invol ht ht2 ht1 htz
  obtain ⟨c₃, hc₃, hc₃'⟩ := sec5cn_exists_anti u hu
  refine ⟨π (c₃, 1), h.mk_mem c₃ 1, ?_, ?_⟩
  · exact (h.pow4_iff c₃ 1).mpr ⟨hc₃, one_pow 4⟩
  · rw [sec5cn_pi_inv_mk, sec5cn_pi_mul_mk, sec5cn_pi_mul_mk, hc₃', inv_one, one_mul, mul_one,
      h.neg_left]
    exact h.z_comm (h.mk_mem u v)

theorem Sec5CNPi.cent_q (h : Sec5CNPi π K₃ K₄ z) {k : G} (hk : k ∈ K₃ ⊔ K₄)
    (hc : ∀ q ∈ K₃ ⊔ K₄, q ^ 4 = 1 → k * q = q * k) : k = 1 ∨ k = z := by
  obtain ⟨⟨u, v⟩, rfl⟩ := h.mem_iff.mp hk
  have hu : ∀ p : SL23, p ^ 4 = 1 → u * p = p * u := by
    intro p hp
    have h1 := hc (π (p, 1)) (h.mk_mem p 1) ((h.pow4_iff p 1).mpr ⟨hp, one_pow 4⟩)
    rcases (h.comm_iff u v p 1).mp h1 with ⟨h2, -⟩ | ⟨h2, h3⟩
    · exact h2.symm
    · exfalso
      rw [one_mul, mul_one] at h3
      exact sec5cn_neg_ne v h3.symm
  have hv : ∀ p : SL23, p ^ 4 = 1 → v * p = p * v := by
    intro p hp
    have h1 := hc (π (1, p)) (h.mk_mem 1 p) ((h.pow4_iff 1 p).mpr ⟨one_pow 4, hp⟩)
    rcases (h.comm_iff u v 1 p).mp h1 with ⟨-, h2⟩ | ⟨h2, h3⟩
    · exact h2.symm
    · exfalso
      rw [one_mul, mul_one] at h2
      exact sec5cn_neg_ne u h2.symm
  exact h.sign_mem (sec5cn_centralizer_q8 u hu) (sec5cn_centralizer_q8 v hv)

end CFSG.OddStandard.SmallF3.Omega
