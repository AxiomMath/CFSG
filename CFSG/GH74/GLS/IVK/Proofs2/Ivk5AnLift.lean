module

public import CFSG.GH74.GLS.IVK.Lifted.Alt51Lift

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup Equiv CFSG CFSG.GH74.GLS.IVK.Lifted

variable {H : Type} [Group H] {K : Subgroup H} {n : ℕ} {R : PermRep K n} {z : H}

theorem comm_eq_sq3 (hz : R.KerData z) {u v : H} (hu : R.ρ u * R.ρ u = 1) (hv : R.ρ v * R.ρ v = 1)
    (huv : R.ρ u * R.ρ v = R.ρ v * R.ρ u) :
    u * v * u⁻¹ * v⁻¹ = (u * u) * (v * v) * ((u * v) * (u * v)) := by
  have hc : R.ρ (u * v * u⁻¹ * v⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    calc R.ρ u * R.ρ v * (R.ρ u)⁻¹ * (R.ρ v)⁻¹ = R.ρ v * R.ρ u * (R.ρ u)⁻¹ * (R.ρ v)⁻¹ := by rw [huv]
      _ = 1 := by group
  have ha : R.ρ (u * u) = 1 := by rw [map_mul]; exact hu
  have hb : R.ρ (v * v) = 1 := by rw [map_mul]; exact hv
  have hd : R.ρ ((u * v) * (u * v)) = 1 := by
    simp only [map_mul]
    calc R.ρ u * R.ρ v * (R.ρ u * R.ρ v) = R.ρ u * (R.ρ v * R.ρ u) * R.ρ v := by group
      _ = R.ρ u * (R.ρ u * R.ρ v) * R.ρ v := by rw [huv]
      _ = (R.ρ u * R.ρ u) * (R.ρ v * R.ρ v) := by group
      _ = 1 := by rw [hu, hv, one_mul]
  obtain ⟨hcc, hc2⟩ := hz.sq_central hc
  obtain ⟨hac, ha2⟩ := hz.sq_central ha
  obtain ⟨hbc, hb2⟩ := hz.sq_central hb
  obtain ⟨hdc, hd2⟩ := hz.sq_central hd
  set c := u * v * u⁻¹ * v⁻¹ with hcdef
  have h1 : (u * v) * (u * v) = c * (u * u) * (v * v) := by
    have e : u * v = c * v * u := by rw [hcdef]; group
    calc (u * v) * (u * v) = (c * v * u) * (u * v) := by rw [← e]
      _ = c * v * (u * u) * v := by group
      _ = c * ((u * u) * v) * v := by rw [← hac v]; group
      _ = c * (u * u) * (v * v) := by group
  have h2 : c = ((u * v) * (u * v)) * (u * u) * (v * v) := by
    rw [h1]
    calc c = c * (u * u) * (u * u) * (v * v) * (v * v) := by
          calc c = c * ((u * u) * (u * u)) * ((v * v) * (v * v)) := by rw [ha2, hb2]; group
            _ = _ := by group
      _ = c * (u * u) * (v * v) * (u * u) * (v * v) := by
          calc c * (u * u) * (u * u) * (v * v) * (v * v) = c * (u * u) * ((u * u) * (v * v)) * (v * v) := by group
            _ = c * (u * u) * ((v * v) * (u * u)) * (v * v) := by rw [hbc (u * u)]
            _ = _ := by group
  rw [h2]
  calc ((u * v) * (u * v)) * (u * u) * (v * v)
      = ((u * u) * ((u * v) * (u * v))) * (v * v) := by rw [hdc (u * u)]
    _ = (u * u) * (((u * v) * (u * v)) * (v * v)) := by simp only [mul_assoc]
    _ = (u * u) * ((v * v) * ((u * v) * (u * v))) := by rw [hdc (v * v)]
    _ = (u * u) * (v * v) * ((u * v) * (u * v)) := by simp only [mul_assoc]

theorem comm_of_squares (hz : R.KerData z) {u v : H} (hu : R.ρ u * R.ρ u = 1) (hv : R.ρ v * R.ρ v = 1)
    (huv : R.ρ u * R.ρ v = R.ρ v * R.ρ u) {a b c : H} (ha : u * u = a) (hb : v * v = b)
    (hc : (u * v) * (u * v) = c) : u * v * u⁻¹ * v⁻¹ = a * b * c := by
  rw [comm_eq_sq3 hz hu hv huv, ha, hb, hc]

theorem commute_of_squares_one (hz : R.KerData z) {u v : H} (hu : R.ρ u * R.ρ u = 1)
    (hv : R.ρ v * R.ρ v = 1) (huv : R.ρ u * R.ρ v = R.ρ v * R.ρ u) (ha : u * u = 1) (hb : v * v = 1)
    (hc : (u * v) * (u * v) = 1) : u * v = v * u := by
  have h := comm_of_squares hz hu hv huv ha hb hc
  simp only [mul_one] at h
  calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
    _ = v * u := by rw [h, one_mul]

theorem conj_mem_ker (hz : R.KerData z) {g u v : H} (h : R.ρ (g * u * g⁻¹) = R.ρ v) :
    g * u * g⁻¹ = v ∨ g * u * g⁻¹ = v * z := by
  have hker : R.ρ (v⁻¹ * (g * u * g⁻¹)) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases hz.ker _ hker with h1 | h1
  · left
    calc g * u * g⁻¹ = v * (v⁻¹ * (g * u * g⁻¹)) := by group
      _ = v := by rw [h1, mul_one]
  · right
    calc g * u * g⁻¹ = v * (v⁻¹ * (g * u * g⁻¹)) := by group
      _ = v * z := by rw [h1]

theorem commute_of_pow_three (hz : R.KerData z) {x u : H} (hx : x ^ 3 = 1)
    (h : R.ρ u * R.ρ x = R.ρ x * R.ρ u) : u * x = x * u := by
  have hc : R.ρ (u * x * u⁻¹ * x⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    calc R.ρ u * R.ρ x * (R.ρ u)⁻¹ * (R.ρ x)⁻¹ = R.ρ x * R.ρ u * (R.ρ u)⁻¹ * (R.ρ x)⁻¹ := by rw [h]
      _ = 1 := by group
  obtain ⟨hcc, hc2⟩ := hz.sq_central hc
  set c := u * x * u⁻¹ * x⁻¹ with hcdef
  have h1 : (c * x) ^ 3 = 1 := by
    have e : c * x = u * x * u⁻¹ := by rw [hcdef]; group
    rw [e]
    calc (u * x * u⁻¹) ^ 3 = u * x ^ 3 * u⁻¹ := conj_pow
      _ = 1 := by rw [hx]; group
  have h2 : (c * x) ^ 3 = c ^ 3 * x ^ 3 := by
    have hcomm : Commute c x := (hcc x).symm
    exact hcomm.mul_pow 3
  have h3 : c ^ 3 = 1 := by
    rw [h2, hx, mul_one] at h1
    exact h1
  have h4 : c = 1 := by
    have : c ^ 3 = c := by
      calc c ^ 3 = c * (c * c) := pow_three c
        _ = c := by rw [hc2, mul_one]
    rw [← this]
    exact h3
  calc u * x = (u * x * u⁻¹ * x⁻¹) * (x * u) := by group
    _ = x * u := by rw [← hcdef, h4, one_mul]

theorem exists_lift_pow_three (hz : R.KerData z) {σ : Perm (Fin n)} (hσ : σ ^ 3 = 1)
    (hs : Perm.sign σ = 1) : ∃ x : H, R.ρ x = σ ∧ x ^ 3 = 1 := by
  obtain ⟨y, hy⟩ := R.lift_even hs
  have hy3 : R.ρ (y ^ 3) = 1 := by rw [map_pow, hy, hσ]
  rcases hz.ker _ hy3 with h | h
  · exact ⟨y, hy, h⟩
  · refine ⟨y * z, ?_, ?_⟩
    · rw [map_mul, hy, hz.ρ_z, mul_one]
    · have hcomm : Commute y z := (hz.central y)
      rw [hcomm.mul_pow, h]
      have hz3 : z ^ 3 = z := by
        calc z ^ 3 = z * (z * z) := pow_three z
          _ = z := by rw [hz.sq, mul_one]
      rw [hz3, hz.sq]

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
