module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.E64Ker

open CFSG.ClassicalInvolution.Generic

variable {X : Type} [Group X]

@[expose] def threeCent (z : X) : Subgroup X :=
  Subgroup.closure {w | w * z = z * w ∧ ∃ a : ℕ, w ^ (3 ^ a) = 1}

private theorem gk_conj_pow_one (g w : X) (n : ℕ) (h : w ^ n = 1) :
    (g * w * g⁻¹) ^ n = 1 := by
  rw [conj_pow, h, mul_one, mul_inv_cancel]

private theorem gk_inv_conj_pow_one (g w : X) (n : ℕ) (h : w ^ n = 1) :
    (g⁻¹ * w * g) ^ n = 1 := by
  have h' := gk_conj_pow_one g⁻¹ w n h
  rwa [inv_inv] at h'

private theorem gk_conj_eq {K : Subgroup X} {z g : X} (hz : IsUniqueInvolution K z)
    (hg : g * z * g⁻¹ ∈ K) : g * z * g⁻¹ = z := by
  have ht2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have ht1 : g * z * g⁻¹ ≠ 1 := by
    intro h1
    apply hz.ne_one
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h1]
      _ = 1 := by group
  exact (hz.unique _ hg ht2).resolve_left ht1

theorem mem_threeCent_of {z w : X} (hw : w * z = z * w) {a : ℕ} (ha : w ^ (3 ^ a) = 1) :
    w ∈ threeCent z := by
  unfold threeCent
  exact Subgroup.subset_closure ⟨hw, a, ha⟩

theorem exists_three_lift {Y : Type} [Group Y] [Finite X] (φ : X →* Y) {y : Y} (hy : y ^ 3 = 1)
    (hyr : y ∈ φ.range) : ∃ w : X, φ w = y ∧ ∃ a : ℕ, w ^ (3 ^ a) = 1 := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hyr
  subst hx
  obtain ⟨a, m, hm, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  have hpowmod : ∀ k : ℕ, φ x ^ k = φ x ^ (k % 3) := by
    intro k
    calc φ x ^ k = φ x ^ (3 * (k / 3) + k % 3) := by rw [Nat.div_add_mod]
      _ = (φ x ^ 3) ^ (k / 3) * φ x ^ (k % 3) := by rw [pow_add, pow_mul]
      _ = φ x ^ (k % 3) := by rw [hy, one_pow, one_mul]
  have hmod : m * m % 3 = 1 := by
    have h1 : m % 3 ≠ 0 := fun h => hm (Nat.dvd_of_mod_eq_zero h)
    have h2 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rw [Nat.mul_mod]
    rcases h2 with h2 | h2 <;> simp [h2]
  have hexp : m * m * 3 ^ a = orderOf x * m := by
    rw [hnm]; ring
  refine ⟨x ^ (m * m), ?_, a, ?_⟩
  · rw [map_pow, hpowmod, hmod, pow_one]
  · rw [← pow_mul, hexp, pow_mul, pow_orderOf_eq_one, one_pow]

theorem mem_threeCent_of_normalizes {K : Subgroup X} {z y z₀ : X} (hz : IsUniqueInvolution K z)
    (hexp : ∀ k ∈ K, k ^ 4 = 1) {a : ℕ} (hy3 : y ^ (3 ^ a) = 1)
    (hyn : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hynt : ∃ k ∈ K, y * k ≠ k * y)
    (hKz : ∀ k ∈ K, k * z₀ = z₀ * k) (hyz : y * z₀ = z₀ * y) : z ∈ threeCent z₀ := by
  obtain ⟨q, hqK, hqy⟩ := hynt
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.sq
  have hyzy : y * z * y⁻¹ = z := gk_conj_eq hz (hyn z hz.mem)
  have hyzn : ∀ n : ℕ, y * z ^ n * y⁻¹ = z ^ n := by
    intro n
    rw [← conj_pow, hyzy]
  have hzpow : z ^ (3 ^ a) = z := by
    obtain ⟨k, hk⟩ : Odd (3 ^ a) := Odd.pow (by decide)
    rw [hk, pow_succ, pow_mul, sq, hz.sq, one_pow, one_mul]
  have hq0 : Commute q z₀ := hKz q hqK
  have hy0 : Commute y z₀ := hyz
  have hc1 : q * y * q⁻¹ * z₀ = z₀ * (q * y * q⁻¹) :=
    (hq0.mul_left hy0).mul_left hq0.inv_left
  have hc2 : y⁻¹ * z₀ = z₀ * y⁻¹ := hy0.inv_left
  have hp1 : (q * y * q⁻¹) ^ (3 ^ a) = 1 := by
    rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  have hp2 : y⁻¹ ^ (3 ^ a) = 1 := by
    rw [inv_pow, hy3, inv_one]
  have hm1 : q * y * q⁻¹ ∈ threeCent z₀ := mem_threeCent_of hc1 hp1
  have hm2 : y⁻¹ ∈ threeCent z₀ := mem_threeCent_of hc2 hp2
  obtain ⟨w, hw⟩ : ∃ w : X, w = q * y * q⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hwq : w = q * (y * q⁻¹ * y⁻¹) := by
    rw [hw]; group
  have hwmem : w ∈ threeCent z₀ := by
    rw [hw]; exact mul_mem hm1 hm2
  have hwK : w ∈ K := by
    rw [hwq]
    exact K.mul_mem hqK (hyn q⁻¹ (K.inv_mem hqK))
  have hw1 : w ≠ 1 := by
    intro h1
    have h2 : q * (y * q⁻¹ * y⁻¹) = 1 := by
      rw [← hwq]; exact h1
    have h3 : q * y = y * q := by
      calc q * y = q * (y * q⁻¹ * y⁻¹) * (y * q) := by group
        _ = 1 * (y * q) := by rw [h2]
        _ = y * q := one_mul _
    exact hqy h3.symm
  have hwz : w ≠ z := by
    intro hwe
    have h1 : y * q⁻¹ * y⁻¹ = q⁻¹ * z := by
      calc y * q⁻¹ * y⁻¹ = q⁻¹ * (q * (y * q⁻¹ * y⁻¹)) := by group
        _ = q⁻¹ * w := by rw [hwq]
        _ = q⁻¹ * z := by rw [hwe]
    have h2 : y * q * y⁻¹ = z * q := by
      calc y * q * y⁻¹ = (y * q⁻¹ * y⁻¹)⁻¹ := by group
        _ = (q⁻¹ * z)⁻¹ := by rw [h1]
        _ = z * q := by rw [mul_inv_rev, inv_inv, hzinv]
    have key : ∀ n : ℕ, y ^ n * q * (y ^ n)⁻¹ = z ^ n * q := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc y ^ (n + 1) * q * (y ^ (n + 1))⁻¹
            = y * (y ^ n * q * (y ^ n)⁻¹) * y⁻¹ := by
              rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
          _ = y * (z ^ n * q) * y⁻¹ := by rw [ih]
          _ = (y * z ^ n * y⁻¹) * (y * q * y⁻¹) := by group
          _ = z ^ n * (z * q) := by rw [hyzn n, h2]
          _ = z ^ (n + 1) * q := by rw [pow_succ, mul_assoc]
    have h3 := key (3 ^ a)
    rw [hy3, inv_one, one_mul, mul_one, hzpow] at h3
    have h4 : z * q = 1 * q := by
      rw [one_mul]; exact h3.symm
    exact hz.ne_one (mul_right_cancel h4)
  have hwfour : (w * w) * (w * w) = 1 := by
    have h4 : w ^ 4 = 1 := hexp w hwK
    calc (w * w) * (w * w) = w ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]
      _ = 1 := h4
  have hwsq : w * w ∈ K := K.mul_mem hwK hwK
  rcases hz.unique (w * w) hwsq hwfour with h | h
  · rcases hz.unique w hwK h with h' | h'
    · exact absurd h' hw1
    · exact absurd h' hwz
  · rw [← h]
    exact mul_mem hwmem hwmem

theorem threeCent_conj (g z : X) : threeCent (g * z * g⁻¹) = conjSub g (threeCent z) := by
  unfold threeCent conjSub
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hw, a, ha⟩
    refine ⟨g⁻¹ * w * g, ⟨?_, a, gk_inv_conj_pow_one g w _ ha⟩, ?_⟩
    · calc g⁻¹ * w * g * z = g⁻¹ * (w * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹ * w) * g := by rw [hw]
        _ = z * (g⁻¹ * w * g) := by group
    · group
  · rintro ⟨x, ⟨hx, a, hxa⟩, rfl⟩
    refine ⟨?_, a, gk_conj_pow_one g x _ hxa⟩
    calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [hx]
      _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group

end CFSG.ClassicalInvolution.Q3.E64Ker
