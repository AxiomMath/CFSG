module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24

open CFSG.ClassicalInvolution.Asc77

section Nf

variable {Y : Type} [Group Y] {x₁ x₂ x₃ : Y}

@[expose] def nf (x₁ x₂ x₃ : Y) (i j k : ℤ) : Y := x₁ ^ i * x₂ ^ j * x₃ ^ k

theorem nf_mul (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃)
    (i j k i' j' k' : ℤ) :
    nf x₁ x₂ x₃ i j k * nf x₁ x₂ x₃ i' j' k' = nf x₁ x₂ x₃ (i + i') (j + j') (k + k') := by
  have hc12 : ∀ a b : ℤ, x₁ ^ a * x₂ ^ b = x₂ ^ b * x₁ ^ a := fun a b => (c12.zpow_zpow a b).eq
  have hc13 : ∀ a b : ℤ, x₁ ^ a * x₃ ^ b = x₃ ^ b * x₁ ^ a := fun a b => (c13.zpow_zpow a b).eq
  have hc23 : ∀ a b : ℤ, x₂ ^ a * x₃ ^ b = x₃ ^ b * x₂ ^ a := fun a b => (c23.zpow_zpow a b).eq
  unfold nf
  calc x₁ ^ i * x₂ ^ j * x₃ ^ k * (x₁ ^ i' * x₂ ^ j' * x₃ ^ k')
      = x₁ ^ i * x₂ ^ j * (x₃ ^ k * x₁ ^ i') * x₂ ^ j' * x₃ ^ k' := by group
    _ = x₁ ^ i * x₂ ^ j * (x₁ ^ i' * x₃ ^ k) * x₂ ^ j' * x₃ ^ k' := by rw [← hc13 i' k]
    _ = x₁ ^ i * (x₂ ^ j * x₁ ^ i') * x₃ ^ k * x₂ ^ j' * x₃ ^ k' := by group
    _ = x₁ ^ i * (x₁ ^ i' * x₂ ^ j) * x₃ ^ k * x₂ ^ j' * x₃ ^ k' := by rw [← hc12 i' j]
    _ = x₁ ^ i * x₁ ^ i' * x₂ ^ j * (x₃ ^ k * x₂ ^ j') * x₃ ^ k' := by group
    _ = x₁ ^ i * x₁ ^ i' * x₂ ^ j * (x₂ ^ j' * x₃ ^ k) * x₃ ^ k' := by rw [← hc23 j' k]
    _ = x₁ ^ (i + i') * x₂ ^ (j + j') * x₃ ^ (k + k') := by
      rw [zpow_add, zpow_add, zpow_add]; group

theorem nf_x₁ (i : ℤ) : x₁ ^ i = nf x₁ x₂ x₃ i 0 0 := by simp [nf]

theorem nf_x₃ (k : ℤ) : x₃ ^ k = nf x₁ x₂ x₃ 0 0 k := by simp [nf]

end Nf

section Facts

variable {Y : Type} [Group Y] {x₁ x₂ x₃ r r' s t j : Y} {m m' : ℕ}

theorem vertex_r (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃)
    (r₁ : r * x₁ * r⁻¹ = x₁⁻¹) (r₂ : r * x₂ * r⁻¹ = x₂) (r₃ : r * x₃ * r⁻¹ = x₃ * x₁)
    (hm : (m : ℤ) = 2 * m') (z₁ : x₁ ^ (2 * m) = t) :
    r * nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * r⁻¹ = nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * t := by
  have h : r * nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * r⁻¹ = nf x₁ x₂ x₃ ((m : ℤ) - -(m' : ℤ)) m' m :=
    A3Mod.conj_nf_r c12 c13 r₁ r₂ r₃ (-(m' : ℤ)) m' m
  have ht : t = nf x₁ x₂ x₃ ((2 * m : ℕ) : ℤ) 0 0 := by
    rw [← z₁, ← nf_x₁ (x₂ := x₂) (x₃ := x₃), zpow_natCast]
  rw [h, ht, nf_mul c12 c13 c23]
  congr 1
  push_cast
  omega

theorem vertex_s (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃)
    (s₁ : s * x₁ * s⁻¹ = x₁ * x₃) (s₂ : s * x₂ * s⁻¹ = x₂ * x₃) (s₃ : s * x₃ * s⁻¹ = x₃⁻¹)
    (hm : (m : ℤ) = 2 * m') (z₃ : x₃ ^ (2 * m) = j) (o₃ : x₃ ^ (4 * m) = 1) :
    s * nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * s⁻¹ = nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * j := by
  have h : s * nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * s⁻¹ =
      nf x₁ x₂ x₃ (-(m' : ℤ)) m' (-(m' : ℤ) + m' - m) :=
    A3Mod.conj_nf_s c13 c23 s₁ s₂ s₃ (-(m' : ℤ)) m' m
  have hj : j = nf x₁ x₂ x₃ 0 0 ((2 * m : ℕ) : ℤ) := by
    rw [← z₃, ← nf_x₃ (x₁ := x₁) (x₂ := x₂), zpow_natCast]
  have h4 : x₃ ^ ((4 * m : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact o₃
  rw [h, hj, nf_mul c12 c13 c23]
  unfold nf
  have e : x₃ ^ ((m : ℤ) + ((2 * m : ℕ) : ℤ)) = x₃ ^ (-(m' : ℤ) + m' - m) := by
    have : (m : ℤ) + ((2 * m : ℕ) : ℤ) = (-(m' : ℤ) + m' - m) + ((4 * m : ℕ) : ℤ) := by
      push_cast; omega
    rw [this, zpow_add, h4, mul_one]
  rw [show (-(m' : ℤ)) + 0 = -(m' : ℤ) by ring, show (m' : ℤ) + 0 = m' by ring, e]

theorem vertex_r' (c23 : Commute x₂ x₃)
    (t₁ : r' * x₁ * r'⁻¹ = x₁) (t₂ : r' * x₂ * r'⁻¹ = x₂⁻¹) (t₃ : r' * x₃ * r'⁻¹ = x₃ * x₂)
    (hm : (m : ℤ) = 2 * m') :
    r' * nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * r'⁻¹ = nf x₁ x₂ x₃ (-(m' : ℤ)) m' m := by
  have h : r' * nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * r'⁻¹ =
      nf x₁ x₂ x₃ (-(m' : ℤ)) ((m : ℤ) - m') m :=
    A3Mod.conj_nf_t c23 t₁ t₂ t₃ (-(m' : ℤ)) m' m
  rw [h]
  congr 1
  omega

theorem vertex_sq (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃)
    (hm : (m : ℤ) = 2 * m') (z₃ : x₃ ^ (2 * m) = j) (hj : j = x₁ ^ m * (x₂ ^ m)⁻¹)
    (hj2 : j * j = 1) :
    nf x₁ x₂ x₃ (-(m' : ℤ)) m' m * nf x₁ x₂ x₃ (-(m' : ℤ)) m' m = 1 := by
  rw [nf_mul c12 c13 c23]
  unfold nf
  have e1 : x₁ ^ (-(m' : ℤ) + -(m' : ℤ)) = (x₁ ^ m)⁻¹ := by
    rw [show -(m' : ℤ) + -(m' : ℤ) = -(m : ℤ) by omega, zpow_neg, zpow_natCast]
  have e2 : x₂ ^ ((m' : ℤ) + m') = x₂ ^ m := by
    rw [show (m' : ℤ) + m' = (m : ℤ) by omega, zpow_natCast]
  have e3 : x₃ ^ ((m : ℤ) + m) = j := by
    rw [show (m : ℤ) + m = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, z₃]
  rw [e1, e2, e3]
  have hc : (x₁ ^ m)⁻¹ * x₂ ^ m = x₂ ^ m * (x₁ ^ m)⁻¹ := ((c12.pow_pow m m).inv_left).eq
  have hji : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj2
  have h1 : x₂ ^ m * (x₁ ^ m)⁻¹ = j⁻¹ := by rw [hj]; group
  rw [hc, h1, hji, hj2]

end Facts

section Frame

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W K K' : Subgroup Y} {t : Y}

@[expose] def vertex (D : Perp23.Two.TwoFrame Ω W K K' t) : Y :=
  nf D.x₁ D.x₂ D.x₃ (-((D.m / 2 : ℕ) : ℤ)) ((D.m / 2 : ℕ) : ℤ) (D.m : ℤ)

variable (D : Perp23.Two.TwoFrame Ω W K K' t)
  (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hm : Even D.m)

include hc hm

private theorem hm2 : (D.m : ℤ) = 2 * ((D.m / 2 : ℕ) : ℤ) := by
  obtain ⟨k, hk⟩ := hm
  omega

theorem vertex_r_eq :
    D.F.ρ.r * vertex D * D.F.ρ.r⁻¹ = vertex D * t :=
  vertex_r (hc _ D.x₁_mem_W _ D.x₂_mem_W) (hc _ D.x₁_mem_W _ D.x₃_mem_W)
    (hc _ D.x₂_mem_W _ D.x₃_mem_W) D.r₁ D.r₂ D.r₃ (hm2 D hc hm) D.z₁

theorem vertex_s_eq :
    D.F.ρ₃.r * vertex D * D.F.ρ₃.r⁻¹ = vertex D * D.F.j :=
  vertex_s (hc _ D.x₁_mem_W _ D.x₂_mem_W) (hc _ D.x₁_mem_W _ D.x₃_mem_W)
    (hc _ D.x₂_mem_W _ D.x₃_mem_W) D.s₁ D.s₂ D.s₃ (hm2 D hc hm) D.z₃
    (by rw [← D.o₃]; exact pow_orderOf_eq_one _)

theorem vertex_r'_eq :
    D.F.ρ'.r * vertex D * D.F.ρ'.r⁻¹ = vertex D :=
  vertex_r' (hc _ D.x₂_mem_W _ D.x₃_mem_W) D.t₁ D.t₂ D.t₃ (hm2 D hc hm)

theorem vertex_sq_eq (hju : D.F.j = D.b * D.b'⁻¹) : vertex D * vertex D = 1 :=
  vertex_sq (hc _ D.x₁_mem_W _ D.x₂_mem_W) (hc _ D.x₁_mem_W _ D.x₃_mem_W)
    (hc _ D.x₂_mem_W _ D.x₃_mem_W) (hm2 D hc hm) D.z₃ hju D.j_sq

theorem vertex_mem_W : vertex D ∈ W := by
  unfold vertex nf
  exact W.mul_mem (W.mul_mem (W.zpow_mem D.x₁_mem_W _) (W.zpow_mem D.x₂_mem_W _))
    (W.zpow_mem D.x₃_mem_W _)

theorem vertex_ne (hju : D.F.j = D.b * D.b'⁻¹) :
    vertex D ≠ 1 ∧ vertex D ≠ t ∧ vertex D ≠ D.F.j ∧ vertex D ≠ t * D.F.j := by
  have hz2 : t * t = 1 := (Perp23.Two.TwoFrame.hzK D).sq
  have hz1 : t ≠ 1 := (Perp23.Two.TwoFrame.hzK D).ne_one
  have hj1 : D.F.j ≠ 1 := D.F.hj.ne_one
  have hrt : D.F.ρ.r * t * D.F.ρ.r⁻¹ = t := by rw [D.r_t]; group
  have hr't : D.F.ρ'.r * t * D.F.ρ'.r⁻¹ = t := by
    have := (Perp23.Two.TwoFrame.hzK' D).commute_of_mem D.r'_mem_K'
    rw [← this]; group
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have e := vertex_r_eq D hc hm
    rw [h] at e
    simp at e
    exact hz1 e.symm
  · have e := vertex_r_eq D hc hm
    rw [h, hrt, hz2] at e
    exact hz1 e
  · have e := vertex_s_eq D hc hm
    rw [h, D.s_j, D.j_sq] at e
    exact hj1 e
  · have e := vertex_r'_eq D hc hm
    rw [h] at e
    have e2 : D.F.ρ'.r * (t * D.F.j) * D.F.ρ'.r⁻¹ = t * (D.F.j * t) := by
      calc D.F.ρ'.r * (t * D.F.j) * D.F.ρ'.r⁻¹ =
          (D.F.ρ'.r * t * D.F.ρ'.r⁻¹) * (D.F.ρ'.r * D.F.j * D.F.ρ'.r⁻¹) := by group
        _ = t * (D.F.j * t) := by rw [hr't, D.t_j hc]
    rw [e2] at e
    have e3 : D.F.j * t = D.F.j := mul_left_cancel e
    exact hz1 (mul_eq_left.mp e3)

end Frame

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
