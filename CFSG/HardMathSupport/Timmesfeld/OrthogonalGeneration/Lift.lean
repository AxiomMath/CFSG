module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

variable {Y : Type*} [Group Y]

theorem commute_of_mem_center {z : Y} (hz : z ∈ Subgroup.center Y) (g : Y) : Commute g z :=
  Subgroup.mem_center_iff.mp hz g

theorem eq_one_of_sq_eq_one_of_mem_center [Finite Y] (hZ : Odd (Nat.card (Subgroup.center Y)))
    {u : Y} (hu : u ∈ Subgroup.center Y) (hsq : u ^ 2 = 1) : u = 1 := by
  obtain ⟨k, hk⟩ := hZ
  have hord : (⟨u, hu⟩ : Subgroup.center Y) ^ (2 * k + 1) = 1 := by
    rw [← hk]; exact pow_card_eq_one'
  have h1 : u ^ (2 * k + 1) = 1 := by simpa using congrArg (fun x : Subgroup.center Y => (x : Y)) hord
  have : u ^ (2 * k + 1) = u := by
    calc u ^ (2 * k + 1) = (u ^ 2) ^ k * u := by rw [← pow_mul, ← pow_succ]
      _ = u := by rw [hsq]; simp
  rw [← this, h1]

theorem exists_central_sq_eq [Finite Y] (hZ : Odd (Nat.card (Subgroup.center Y))) {z : Y}
    (hz : z ∈ Subgroup.center Y) : ∃ w ∈ Subgroup.center Y, w ^ 2 = z := by
  obtain ⟨k, hk⟩ := hZ
  refine ⟨z ^ (k + 1), Subgroup.pow_mem _ hz _, ?_⟩
  have h1 : (⟨z, hz⟩ : Subgroup.center Y) ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_card_eq_one'
  have h2 : z ^ (2 * k + 1) = 1 := by
    simpa using congrArg (fun x : Subgroup.center Y => (x : Y)) h1
  calc (z ^ (k + 1)) ^ 2 = z ^ (2 * k + 1) * z := by rw [← pow_mul, ← pow_succ]; ring_nf
    _ = z := by rw [h2, one_mul]

theorem existsUnique_involution_lift [Finite Y] (hZ : Odd (Nat.card (Subgroup.center Y))) {y : Y}
    (hy : y ^ 2 ∈ Subgroup.center Y) :
    ∃! t : Y, t ^ 2 = 1 ∧ t⁻¹ * y ∈ Subgroup.center Y := by
  obtain ⟨w, hw, hwz⟩ := exists_central_sq_eq hZ hy
  have hc : Commute y w⁻¹ := commute_of_mem_center (Subgroup.inv_mem _ hw) y
  have hsq : (y * w⁻¹) ^ 2 = 1 := by
    rw [hc.mul_pow, inv_pow, hwz]; group
  refine ⟨y * w⁻¹, ⟨hsq, ?_⟩, ?_⟩
  · have : (y * w⁻¹)⁻¹ * y = w := by group
    rw [this]; exact hw
  · rintro t ⟨ht2, htz⟩
    have hu : t⁻¹ * (y * w⁻¹) ∈ Subgroup.center Y := by
      have : t⁻¹ * (y * w⁻¹) = (t⁻¹ * y) * w⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ htz (Subgroup.inv_mem _ hw)
    set u := t⁻¹ * (y * w⁻¹) with hu_def
    have htu : y * w⁻¹ = t * u := by rw [hu_def]; group
    have hc2 : Commute t u := (commute_of_mem_center hu t)
    have hu2 : u ^ 2 = 1 := by
      have h1 := hsq
      rw [htu, hc2.mul_pow, ht2, one_mul] at h1
      exact h1
    have hu1 : u = 1 := eq_one_of_sq_eq_one_of_mem_center hZ hu hu2
    rw [hu1, mul_one] at htu
    exact htu.symm

theorem map_mem_center (φ : Y ≃* Y) {z : Y} (hz : z ∈ Subgroup.center Y) :
    φ z ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz g']

theorem map_involution_lift [Finite Y] (hZ : Odd (Nat.card (Subgroup.center Y))) (φ : Y ≃* Y)
    {y t : Y} (ht2 : t ^ 2 = 1) (htz : t⁻¹ * y ∈ Subgroup.center Y)
    (hφ : (φ y)⁻¹ * y ∈ Subgroup.center Y) : φ t = t := by
  have hy : y ^ 2 ∈ Subgroup.center Y := by
    have h1 : y = t * (t⁻¹ * y) := by group
    have hc : Commute t (t⁻¹ * y) := (commute_of_mem_center htz t)
    rw [h1, hc.mul_pow, ht2, one_mul]
    exact Subgroup.pow_mem _ htz _
  obtain ⟨t₀, -, huniq⟩ := existsUnique_involution_lift hZ hy
  have h1 : φ t = t₀ := by
    refine huniq (φ t) ⟨by rw [← map_pow, ht2, map_one], ?_⟩
    have : (φ t)⁻¹ * y = φ (t⁻¹ * y) * ((φ y)⁻¹ * y) := by
      rw [map_mul, map_inv]; group
    rw [this]
    exact Subgroup.mul_mem _ (map_mem_center φ htz) hφ
  have h2 : t = t₀ := huniq t ⟨ht2, htz⟩
  rw [h1, h2]

theorem commutatorElement_mul_central_left {n z : Y} (hz : z ∈ Subgroup.center Y) (g : Y) :
    ⁅n * z, g⁆ = ⁅n, g⁆ := by
  have h : z * g * z⁻¹ = g := by
    rw [(commute_of_mem_center hz g).symm.eq]; group
  simp only [commutatorElement_def, mul_inv_rev]
  calc n * z * g * (z⁻¹ * n⁻¹) * g⁻¹ = n * (z * g * z⁻¹) * n⁻¹ * g⁻¹ := by group
    _ = n * g * n⁻¹ * g⁻¹ := by rw [h]

theorem commutatorElement_mul_central_right {n z : Y} (hz : z ∈ Subgroup.center Y) (g : Y) :
    ⁅g, n * z⁆ = ⁅g, n⁆ := by
  have h : z * g⁻¹ * z⁻¹ = g⁻¹ := by
    rw [(commute_of_mem_center hz g⁻¹).symm.eq]; group
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * (n * z) * g⁻¹ * (z⁻¹ * n⁻¹) = g * n * (z * g⁻¹ * z⁻¹) * n⁻¹ := by group
    _ = g * n * g⁻¹ * n⁻¹ := by rw [h]

theorem commutatorElement_mul_central {n n' z z' : Y} (hz : z ∈ Subgroup.center Y)
    (hz' : z' ∈ Subgroup.center Y) : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
  rw [commutatorElement_mul_central_left hz, commutatorElement_mul_central_right hz']

theorem eq_top_of_sup_center_eq_top (hY : commutator Y = ⊤) {N : Subgroup Y}
    (hN : N ⊔ Subgroup.center Y = ⊤) : N = ⊤ := by
  have hle : commutator Y ≤ N := by
    rw [commutator]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    have ha : a ∈ N ⊔ Subgroup.center Y := by rw [hN]; trivial
    have hb : b ∈ N ⊔ Subgroup.center Y := by rw [hN]; trivial
    obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨n', hn', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    rw [commutatorElement_mul_central hz hz']
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')
  rw [hY] at hle
  exact top_le_iff.mp hle

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
