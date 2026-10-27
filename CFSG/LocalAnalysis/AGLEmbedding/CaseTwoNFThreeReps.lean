module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup

public section

namespace CFSG.AGLEmbedding

variable {X : Type*} [Group X]

structure ThreeReps (A₀ A₁ A₂ : Subgroup X) (ρ₀ ρ₁ ρ₂ : X) : Prop where
  c01 : A₀ ≤ Subgroup.centralizer (A₁ : Set X)
  c02 : A₀ ≤ Subgroup.centralizer (A₂ : Set X)
  c12 : A₁ ≤ Subgroup.centralizer (A₂ : Set X)
  z0 : ∀ ζ ∈ A₀, ζ ∈ Subgroup.centralizer (A₀ : Set X) → ζ ^ 3 = 1 → ζ = 1
  z1 : ∀ ζ ∈ A₁, ζ ∈ Subgroup.centralizer (A₁ : Set X) → ζ ^ 3 = 1 → ζ = 1
  z2 : ∀ ζ ∈ A₂, ζ ∈ Subgroup.centralizer (A₂ : Set X) → ζ ^ 3 = 1 → ζ = 1
  m0 : ρ₀ ∈ A₀
  m1 : ρ₁ ∈ A₁
  m2 : ρ₂ ∈ A₂
  p0 : ρ₀ ^ 3 = 1
  p1 : ρ₁ ^ 3 = 1
  p2 : ρ₂ ^ 3 = 1
  n0 : ρ₀ ∉ Subgroup.centralizer (A₀ : Set X)
  n1 : ρ₁ ∉ Subgroup.centralizer (A₁ : Set X)
  n2 : ρ₂ ∉ Subgroup.centralizer (A₂ : Set X)

namespace ThreeReps

variable {A₀ A₁ A₂ : Subgroup X} {ρ₀ ρ₁ ρ₂ : X} (h : ThreeReps A₀ A₁ A₂ ρ₀ ρ₁ ρ₂)
include h

omit h in
theorem orderOf_eq_three {A : Subgroup X} {ρ : X} (hp : ρ ^ 3 = 1)
    (hn : ρ ∉ Subgroup.centralizer (A : Set X)) : orderOf ρ = 3 := by
  refine orderOf_eq_prime hp fun h1 => hn ?_
  rw [h1]; exact Subgroup.one_mem _

theorem comm01 : Commute ρ₀ ρ₁ := Subgroup.mem_centralizer_iff.mp (h.c01 h.m0) ρ₁ h.m1 |>.symm

theorem comm02 : Commute ρ₀ ρ₂ := Subgroup.mem_centralizer_iff.mp (h.c02 h.m0) ρ₂ h.m2 |>.symm

theorem comm12 : Commute ρ₁ ρ₂ := Subgroup.mem_centralizer_iff.mp (h.c12 h.m1) ρ₂ h.m2 |>.symm

theorem card_sup : Nat.card (Subgroup.zpowers ρ₀ ⊔ Subgroup.zpowers ρ₁ ⊔
    Subgroup.zpowers ρ₂ : Subgroup X) = 3 ^ 3 := by
  have h0 := orderOf_eq_three h.p0 h.n0
  have h1 := orderOf_eq_three h.p1 h.n1
  have h2 := orderOf_eq_three h.p2 h.n2
  have hA1 : Subgroup.zpowers ρ₀ ≤ Subgroup.centralizer (A₁ : Set X) :=
    (Subgroup.zpowers_le).mpr (h.c01 h.m0)
  have hA2 : Subgroup.zpowers ρ₀ ⊔ Subgroup.zpowers ρ₁ ≤ Subgroup.centralizer (A₂ : Set X) :=
    sup_le ((Subgroup.zpowers_le).mpr (h.c02 h.m0)) ((Subgroup.zpowers_le).mpr (h.c12 h.m1))
  have hc1 : Subgroup.zpowers ρ₀ ≤ Subgroup.centralizer (Subgroup.zpowers ρ₁ : Set X) :=
    hA1.trans (Subgroup.centralizer_le ((Subgroup.zpowers_le).mpr h.m1))
  have hc2 : Subgroup.zpowers ρ₀ ⊔ Subgroup.zpowers ρ₁ ≤
      Subgroup.centralizer (Subgroup.zpowers ρ₂ : Set X) :=
    hA2.trans (Subgroup.centralizer_le ((Subgroup.zpowers_le).mpr h.m2))
  have e1 := card_sup_zpowers Nat.prime_three hA1 h1 h.n1 hc1
  have e2 := card_sup_zpowers Nat.prime_three hA2 h2 h.n2 hc2
  rw [e2, e1, Nat.card_zpowers, h0]
  norm_num

theorem sup_le_centralizer {B : Subgroup X} (h0 : A₀ ≤ Subgroup.centralizer (B : Set X))
    (h1 : A₁ ≤ Subgroup.centralizer (B : Set X)) (h2 : A₂ ≤ Subgroup.centralizer (B : Set X)) :
    Subgroup.zpowers ρ₀ ⊔ Subgroup.zpowers ρ₁ ⊔ Subgroup.zpowers ρ₂ ≤
      Subgroup.centralizer (B : Set X) :=
  sup_le (sup_le ((Subgroup.zpowers_le).mpr (h0 h.m0)) ((Subgroup.zpowers_le).mpr (h1 h.m1)))
    ((Subgroup.zpowers_le).mpr (h2 h.m2))

theorem parts {i j k : ℤ} {v : X} (hv : v = ρ₀ ^ i * ρ₁ ^ j * ρ₂ ^ k) :
    (ρ₀ ^ i)⁻¹ * v ∈ Subgroup.centralizer (A₀ : Set X) ∧
      (ρ₁ ^ j)⁻¹ * v ∈ Subgroup.centralizer (A₁ : Set X) ∧
      (ρ₂ ^ k)⁻¹ * v ∈ Subgroup.centralizer (A₂ : Set X) := by
  have c10 : A₁ ≤ Subgroup.centralizer (A₀ : Set X) := Subgroup.le_centralizer_iff.mp h.c01
  have c20 : A₂ ≤ Subgroup.centralizer (A₀ : Set X) := Subgroup.le_centralizer_iff.mp h.c02
  have c21 : A₂ ≤ Subgroup.centralizer (A₁ : Set X) := Subgroup.le_centralizer_iff.mp h.c12
  have e01 := (h.comm01.zpow_zpow i j)
  have e02 := (h.comm02.zpow_zpow i k)
  have e12 := (h.comm12.zpow_zpow j k)
  refine ⟨?_, ?_, ?_⟩
  · have : (ρ₀ ^ i)⁻¹ * v = ρ₁ ^ j * ρ₂ ^ k := by rw [hv]; group
    rw [this]
    exact Subgroup.mul_mem _ (c10 (A₁.zpow_mem h.m1 j)) (c20 (A₂.zpow_mem h.m2 k))
  · have : (ρ₁ ^ j)⁻¹ * v = ρ₀ ^ i * ρ₂ ^ k := by
      rw [hv, show ρ₀ ^ i * ρ₁ ^ j = ρ₁ ^ j * ρ₀ ^ i from e01.eq]; group
    rw [this]
    exact Subgroup.mul_mem _ (h.c01 (A₀.zpow_mem h.m0 i)) (c21 (A₂.zpow_mem h.m2 k))
  · have : (ρ₂ ^ k)⁻¹ * v = ρ₀ ^ i * ρ₁ ^ j := by
      rw [hv, show ρ₀ ^ i * ρ₁ ^ j * ρ₂ ^ k = ρ₂ ^ k * (ρ₀ ^ i * ρ₁ ^ j) from
        (e02.mul_left e12).eq]
      group
    rw [this]
    exact Subgroup.mul_mem _ (h.c02 (A₀.zpow_mem h.m0 i)) (h.c12 (A₁.zpow_mem h.m1 j))

omit h in
theorem zpow_pow_three {ρ : X} (hp : ρ ^ 3 = 1) (i : ℤ) : (ρ ^ i) ^ 3 ^ 1 = 1 := by
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp, one_zpow]

theorem eq_prod {u : X} (hu : u ∈ Subgroup.zpowers ρ₀ ⊔ Subgroup.zpowers ρ₁ ⊔
    Subgroup.zpowers ρ₂) (hc0 : ρ₀⁻¹ * u ∈ Subgroup.centralizer (A₀ : Set X))
    (hc1 : ρ₁⁻¹ * u ∈ Subgroup.centralizer (A₁ : Set X))
    (hc2 : ρ₂⁻¹ * u ∈ Subgroup.centralizer (A₂ : Set X)) : u = ρ₀ * ρ₁ * ρ₂ := by
  obtain ⟨i, j, k, hv⟩ := exists_zpow_of_mem_sup h.comm01 h.comm02 h.comm12 hu
  obtain ⟨q0, q1, q2⟩ := h.parts hv
  have r0 : ρ₀ ^ i = ρ₀ := rep_unique_p h.z0 (A₀.zpow_mem h.m0 i) h.m0
    (zpow_pow_three h.p0 i) (by rw [pow_one]; exact h.p0) q0 hc0
  have r1 : ρ₁ ^ j = ρ₁ := rep_unique_p h.z1 (A₁.zpow_mem h.m1 j) h.m1
    (zpow_pow_three h.p1 j) (by rw [pow_one]; exact h.p1) q1 hc1
  have r2 : ρ₂ ^ k = ρ₂ := rep_unique_p h.z2 (A₂.zpow_mem h.m2 k) h.m2
    (zpow_pow_three h.p2 k) (by rw [pow_one]; exact h.p2) q2 hc2
  rw [hv, r0, r1, r2]

omit h in
theorem zpow_eq_of_zpow_eq {ρ σ : X} (hρ : orderOf ρ = 3) (hσ : σ ^ 3 = 1) {a b : ℤ}
    (hab : ρ ^ a = ρ ^ b) : σ ^ a = σ ^ b := by
  have h3 : (3 : ℤ) ∣ a - b := by
    have h1 : ρ ^ (a - b) = 1 := by rw [zpow_sub, hab, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hρ] at this
    exact_mod_cast this
  obtain ⟨c, hc⟩ := h3
  have e : a = b + 3 * c := by omega
  rw [e, zpow_add, zpow_mul, zpow_ofNat, hσ, one_zpow, mul_one]

theorem mem_zpowers_prod {g v : X} (hv : v ∈ Subgroup.zpowers ρ₀ ⊔ Subgroup.zpowers ρ₁ ⊔
    Subgroup.zpowers ρ₂) (hg0 : g * ρ₀ * g⁻¹ = ρ₁) (hg1 : g * ρ₁ * g⁻¹ = ρ₂)
    (hg2 : g * ρ₂ * g⁻¹ = ρ₀) (hgv : g * v * g⁻¹ = v) :
    v ∈ Subgroup.zpowers (ρ₀ * ρ₁ * ρ₂) := by
  obtain ⟨i, j, k, hvd⟩ := exists_zpow_of_mem_sup h.comm01 h.comm02 h.comm12 hv
  have hconj : ∀ (a : X) (n : ℤ), g * a ^ n * g⁻¹ = (g * a * g⁻¹) ^ n := fun a n => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  have hv2 : v = ρ₀ ^ k * ρ₁ ^ i * ρ₂ ^ j := by
    have e : g * v * g⁻¹ = ρ₁ ^ i * ρ₂ ^ j * ρ₀ ^ k := by
      rw [hvd]
      calc g * (ρ₀ ^ i * ρ₁ ^ j * ρ₂ ^ k) * g⁻¹ =
          (g * ρ₀ ^ i * g⁻¹) * (g * ρ₁ ^ j * g⁻¹) * (g * ρ₂ ^ k * g⁻¹) := by group
        _ = ρ₁ ^ i * ρ₂ ^ j * ρ₀ ^ k := by rw [hconj, hconj, hconj, hg0, hg1, hg2]
    rw [← hgv, e, mul_assoc, ((h.comm02.zpow_zpow k j).symm).eq, ← mul_assoc,
      ((h.comm01.zpow_zpow k i).symm).eq]
  obtain ⟨a0, a1, a2⟩ := h.parts hvd
  obtain ⟨b0, b1, b2⟩ := h.parts hv2
  have o1 := orderOf_eq_three h.p1 h.n1
  have e1 : ρ₁ ^ j = ρ₁ ^ i := rep_unique_p h.z1 (A₁.zpow_mem h.m1 j) (A₁.zpow_mem h.m1 i)
    (zpow_pow_three h.p1 j) (zpow_pow_three h.p1 i) a1 b1
  have e1' : ρ₂ ^ j = ρ₂ ^ i := zpow_eq_of_zpow_eq o1 h.p2 e1
  have e2 : ρ₂ ^ k = ρ₂ ^ j := rep_unique_p h.z2 (A₂.zpow_mem h.m2 k) (A₂.zpow_mem h.m2 j)
    (zpow_pow_three h.p2 k) (zpow_pow_three h.p2 j) a2 b2
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  have hc : Commute (ρ₀ * ρ₁) ρ₂ := h.comm02.mul_left h.comm12
  rw [hc.mul_zpow, h.comm01.mul_zpow, hvd, e1, e2, e1']

end ThreeReps

end CFSG.AGLEmbedding
