module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713G

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

variable {G : Type} [Group G]

section S3

variable {Q : Type*} [Group Q] {x y α : Q}

theorem s3_fix (hx : x * x = 1) (hy : y * y = 1) (hxy : (x * y) ^ 3 = 1)
    (hαx : α * x * α⁻¹ = y) (hα : α * α = 1) : α * (x * y * x) * α⁻¹ = x * y * x := by
  have hαy : α * y * α⁻¹ = x := by
    rw [← hαx]
    calc α * (α * x * α⁻¹) * α⁻¹ = (α * α) * x * (α * α)⁻¹ := by group
      _ = x := by rw [hα]; group
  calc α * (x * y * x) * α⁻¹ = (α * x * α⁻¹) * (α * y * α⁻¹) * (α * x * α⁻¹) := by group
    _ = y * x * y := by rw [hαx, hαy]
    _ = x * y * x := braid_of_order_three hx hy hxy

theorem s3_conj_x (hx : x * x = 1) : x * (x * y * x) * x⁻¹ = y := by
  calc x * (x * y * x) * x⁻¹ = (x * x) * y * (x * x⁻¹) := by group
    _ = y := by rw [hx, mul_inv_cancel]; group

theorem s3_conj_inv (hx : x * x = 1) (hy : y * y = 1) (hxy : (x * y) ^ 3 = 1) :
    (x * y * x)⁻¹ * y * (x * y * x)⁻¹⁻¹ = x := by
  have hb := braid_of_order_three hx hy hxy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc (x * y * x)⁻¹ * y * (x * y * x)⁻¹⁻¹ = (x⁻¹ * y⁻¹ * x⁻¹) * y * (x * y * x) := by group
    _ = (y * x * y) * y * (x * y * x) := by rw [hxi, hyi, hb]
    _ = y * x * (y * y) * x * y * x := by group
    _ = y * (x * x) * y * x := by rw [hy]; group
    _ = (y * y) * x := by rw [hx]; group
    _ = x := by rw [hy, one_mul]

theorem s3_cent (hx : x * x = 1) (hy : y * y = 1) (hxy : (x * y) ^ 3 = 1)
    (hαx : α * x * α⁻¹ = y) (hα : α * α = 1) :
    (α * (x * y * x))⁻¹ * x * (α * (x * y * x)) * x⁻¹ = 1 := by
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have h1 : α⁻¹ * x * α = y := by rw [← hαx, hαi]
  have h2 := s3_conj_inv hx hy hxy
  calc (α * (x * y * x))⁻¹ * x * (α * (x * y * x)) * x⁻¹ =
      (x * y * x)⁻¹ * (α⁻¹ * x * α) * (x * y * x)⁻¹⁻¹ * x⁻¹ := by group
    _ = x * x⁻¹ := by rw [h1, h2]
    _ = 1 := mul_inv_cancel x

theorem s3_comm_contra (hx : x * x = 1) (hy : y * y = 1) (hxy : (x * y) ^ 3 = 1)
    (h : x * (x * y * x) * x⁻¹ * (x * y * x)⁻¹ = 1) : x * y = 1 := by
  rw [s3_conj_x hx] at h
  have h1 : y = x * y * x := mul_inv_eq_one.mp h
  have hc : x * y = y * x := by
    calc x * y = x * (x * y * x) := by rw [← h1]
      _ = (x * x) * y * x := by group
      _ = y * x := by rw [hx, one_mul]
  have h2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  calc x * y = (x * y) ^ 3 * ((x * y) * (x * y))⁻¹ := by rw [pow_three]; group
    _ = 1 := by rw [hxy, h2]; group

end S3

theorem odd_of_zpowers_eq {g h : G} (heq : Subgroup.zpowers g = Subgroup.zpowers h)
    (h2 : 2 ∣ orderOf g) {i : ℤ} (hi : g ^ i = h) : Odd i := by
  have hg : g ∈ Subgroup.zpowers h := heq ▸ Subgroup.mem_zpowers g
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h1 : g ^ (i * l - 1) = 1 := by
    rw [zpow_sub, zpow_one, zpow_mul, hi, hl, mul_inv_cancel]
  have h3 : (orderOf g : ℤ) ∣ i * l - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  have h4 : (2 : ℤ) ∣ i * l - 1 := (by exact_mod_cast h2 : (2 : ℤ) ∣ orderOf g).trans h3
  rw [← Int.not_even_iff_odd]
  intro hev
  have h5 : Odd (i * l - 1) := (hev.mul_right l).sub_odd odd_one
  exact (Int.not_even_iff_odd.mpr h5) (even_iff_two_dvd.mpr h4)

theorem even_of_relations {W X₀ : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hWX : ∀ w ∈ W, w ∈ X₀ → w = 1) {u v r t a x₁ : G} {k : ℕ} (hk : 2 ≤ k) (huW : u ∈ W)
    (hvW : v ∈ W) (hu : 2 ∣ orderOf u) (htu : t⁻¹ * u * t = u * v)
    (htv : t⁻¹ * v * t = v⁻¹) (hrv : r * v * r⁻¹ = v * u) {i m j : ℤ} (hi : Odd i)
    (hau : a * u * a⁻¹ = (v * u) ^ i) (ha2 : a * a = 1)
    (hc2 : a * t * (a * t) = v ^ (m + 2 ^ (k - 1))) (hx₁ : x₁ ∈ X₀)
    (hrc : r * (a * t) * r⁻¹ = a * t * (u ^ j * x₁))
    (hcX : a * t ∈ Subgroup.normalizer (X₀ : Set G))
    (huX : u ∈ Subgroup.normalizer (X₀ : Set G)) : Even m := by
  set c := a * t with hc
  obtain ⟨M, hM⟩ : ∃ M : ℤ, m + 2 ^ (k - 1) = M := ⟨_, rfl⟩
  rw [hM] at hc2
  have hvu : v * u = u * v := hWab v hvW u huW
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hcu : c⁻¹ * u * c = u ^ i := by
    have h1 : c⁻¹ * u * c = t⁻¹ * (a * u * a⁻¹) * t⁻¹⁻¹ := by
      rw [inv_inv, hc, mul_inv_rev]
      calc t⁻¹ * a⁻¹ * u * (a * t) = t⁻¹ * (a⁻¹ * u * a) * t := by group
        _ = t⁻¹ * (a * u * a⁻¹) * t := by rw [hai]
    have h2 : t⁻¹ * (v * u) * t⁻¹⁻¹ = u := by
      calc t⁻¹ * (v * u) * t⁻¹⁻¹ = (t⁻¹ * v * t) * (t⁻¹ * u * t) := by group
        _ = v⁻¹ * (u * v) := by rw [htv, htu]
        _ = u := by rw [← hvu]; group
    rw [h1, hau, ← conj_zpow, h2]
  have hcuj : c⁻¹ * u ^ j * c = u ^ (i * j) := by
    have h1 : c⁻¹ * u ^ j * c = (c⁻¹ * u * c⁻¹⁻¹) ^ j := by rw [conj_zpow, inv_inv]
    rw [h1, inv_inv, hcu, ← zpow_mul]
  have hsq1 : (r * c * r⁻¹) * (r * c * r⁻¹) = v ^ M * u ^ M := by
    have h1 : (r * c * r⁻¹) * (r * c * r⁻¹) = r * (c * c) * r⁻¹ := by group
    have hcomm : Commute v u := hvu
    rw [h1, hc2, ← conj_zpow, hrv, hcomm.mul_zpow]
  have hcinv : c⁻¹ ∈ Subgroup.normalizer (X₀ : Set G) := Subgroup.inv_mem _ hcX
  set x₂ := c⁻¹ * x₁ * c with hx₂
  have hx₂X : x₂ ∈ X₀ := by
    have := (Subgroup.mem_normalizer_iff.mp hcinv x₁).mp hx₁
    rwa [inv_inv] at this
  obtain ⟨x₃, hx₃⟩ : ∃ x : G, (u ^ (-j) * x₂ * u ^ j) * x₁ = x := ⟨_, rfl⟩
  have hx₃X : x₃ ∈ X₀ := by
    have hu' : u ^ (-j) ∈ Subgroup.normalizer (X₀ : Set G) := Subgroup.zpow_mem _ huX _
    have := (Subgroup.mem_normalizer_iff.mp hu' x₂).mp hx₂X
    rw [show (u ^ (-j))⁻¹ = u ^ j by rw [zpow_neg, inv_inv]] at this
    exact hx₃ ▸ X₀.mul_mem this hx₁
  have hsq2 : (c * (u ^ j * x₁)) * (c * (u ^ j * x₁)) = v ^ M * u ^ (i * j + j) * x₃ := by
    calc (c * (u ^ j * x₁)) * (c * (u ^ j * x₁))
        = (c * c) * (c⁻¹ * u ^ j * c) * (c⁻¹ * x₁ * c) * u ^ j * x₁ := by group
      _ = v ^ M * u ^ (i * j) * x₂ * u ^ j * x₁ := by rw [hc2, hcuj]
      _ = v ^ M * u ^ (i * j) * u ^ j * ((u ^ (-j) * x₂ * u ^ j) * x₁) := by group
      _ = v ^ M * u ^ (i * j + j) * x₃ := by
        rw [← hx₃, zpow_add u (i * j) j]; simp only [mul_assoc]
  have heq : v ^ M * u ^ M = v ^ M * u ^ (i * j + j) * x₃ := by rw [← hsq1, ← hsq2, hrc]
  have hx₃eq : x₃ = u ^ (M - (i * j + j)) := by
    have h1 : x₃ = (v ^ M * u ^ (i * j + j))⁻¹ * (v ^ M * u ^ M) := by rw [heq]; group
    rw [h1, zpow_sub]
    group
  have hx₃W : x₃ ∈ W := hx₃eq ▸ Subgroup.zpow_mem _ huW _
  have hx₃1 : x₃ = 1 := hWX x₃ hx₃W hx₃X
  rw [hx₃eq] at hx₃1
  have hdvd : (orderOf u : ℤ) ∣ M - (i * j + j) := orderOf_dvd_iff_zpow_eq_one.mpr hx₃1
  have h2 : (2 : ℤ) ∣ M - (i * j + j) := (by exact_mod_cast hu : (2 : ℤ) ∣ orderOf u).trans hdvd
  have hij : Even (i * j + j) := by
    have : i * j + j = (i + 1) * j := by ring
    rw [this]
    exact Even.mul_right (hi.add_one) j
  have hMe : Even M := by
    have h3 : Even (M - (i * j + j)) := even_iff_two_dvd.mpr h2
    have := h3.add hij
    simpa using this
  have hk1 : Even ((2 : ℤ) ^ (k - 1)) :=
    (Int.even_pow).mpr ⟨even_two, by omega⟩
  have := hMe.sub hk1
  rw [← hM] at this
  simpa using this

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
