module

public import CFSG.ClassicalInvolution.WeakCT.WeylSigns

public section

namespace CFSG.ClassicalInvolution.WeakCT

structure VData (G F : Type*) [Group G] [Field F] where
  xa : F → G
  xa' : F → G
  xb : F → G
  xc : F → G
  xd : F → G
  κ₁ : F
  κ₂ : F
  κ₃ : F
  μ₁ : F
  μ₂ : F
  μ₃ : F
  ηb : F
  ηc : F
  ηd : F
  add_a : ∀ s t, xa (s + t) = xa s * xa t
  add_a' : ∀ s t, xa' (s + t) = xa' s * xa' t
  add_b : ∀ s t, xb (s + t) = xb s * xb t
  add_c : ∀ s t, xc (s + t) = xc s * xc t
  add_d : ∀ s t, xd (s + t) = xd s * xd t
  comm_bc : ∀ s t, xb s * xc t = xc t * xb s
  comm_bd : ∀ s t, xb s * xd t = xd t * xb s
  comm_cd : ∀ s t, xc s * xd t = xd t * xc s
  conj_a_b : ∀ t v, xa t * xb v * xa (-t) = xb v * xc (κ₁ * t * v) * xd (κ₃ * t ^ 2 * v)
  conj_a_c : ∀ t v, xa t * xc v * xa (-t) = xc v * xd (κ₂ * t * v)
  conj_a_d : ∀ t v, xa t * xd v * xa (-t) = xd v
  conj_a'_b : ∀ t v, xa' t * xb v * xa' (-t) = xb v
  conj_a'_c : ∀ t v, xa' t * xc v * xa' (-t) = xc v * xb (μ₁ * t * v)
  conj_a'_d : ∀ t v, xa' t * xd v * xa' (-t) = xd v * xc (μ₂ * t * v) * xb (μ₃ * t ^ 2 * v)
  conj_n_b : ∀ v, xa 1 * xa' (-1) * xa 1 * xb v * (xa 1 * xa' (-1) * xa 1)⁻¹ = xd (ηb * v)
  conj_n_c : ∀ v, xa 1 * xa' (-1) * xa 1 * xc v * (xa 1 * xa' (-1) * xa 1)⁻¹ = xc (ηc * v)
  conj_n_d : ∀ v, xa 1 * xa' (-1) * xa 1 * xd v * (xa 1 * xa' (-1) * xa 1)⁻¹ = xb (ηd * v)
  ext : ∀ u₁ u₂ u₃ u₁' u₂' u₃', xb u₁ * xc u₂ * xd u₃ = xb u₁' * xc u₂' * xd u₃' →
    u₁ = u₁' ∧ u₂ = u₂' ∧ u₃ = u₃'
  sq_d : ηd * ηd = 1

namespace VData

variable {G F : Type*} [Group G] [Field F] (D : VData G F)

theorem xb_zero : D.xb 0 = 1 := by
  have h := D.add_b 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xc_zero : D.xc 0 = 1 := by
  have h := D.add_c 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xd_zero : D.xd 0 = 1 := by
  have h := D.add_d 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xa_zero : D.xa 0 = 1 := by
  have h := D.add_a 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xa'_zero : D.xa' 0 = 1 := by
  have h := D.add_a' 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xa_neg (t : F) : D.xa (-t) = (D.xa t)⁻¹ := by
  have h := D.add_a t (-t)
  rw [add_neg_cancel, D.xa_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem xa'_neg (t : F) : D.xa' (-t) = (D.xa' t)⁻¹ := by
  have h := D.add_a' t (-t)
  rw [add_neg_cancel, D.xa'_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

def Φ (v : F × F × F) : G := D.xb v.1 * D.xc v.2.1 * D.xd v.2.2

theorem Φ_add (u v : F × F × F) : D.Φ (u + v) = D.Φ u * D.Φ v := by
  obtain ⟨u₁, u₂, u₃⟩ := u
  obtain ⟨v₁, v₂, v₃⟩ := v
  simp only [Φ, Prod.fst_add, Prod.snd_add, D.add_b, D.add_c, D.add_d]
  have h1 : D.xd u₃ * (D.xb v₁ * D.xc v₂) = (D.xb v₁ * D.xc v₂) * D.xd u₃ := by
    rw [← mul_assoc, ← D.comm_bd v₁ u₃, mul_assoc, ← D.comm_cd v₂ u₃, ← mul_assoc]
  have h2 : D.xc u₂ * D.xb v₁ = D.xb v₁ * D.xc u₂ := (D.comm_bc v₁ u₂).symm
  calc D.xb u₁ * D.xb v₁ * (D.xc u₂ * D.xc v₂) * (D.xd u₃ * D.xd v₃)
      = D.xb u₁ * (D.xb v₁ * D.xc u₂) * D.xc v₂ * (D.xd u₃ * D.xd v₃) := by group
    _ = D.xb u₁ * (D.xc u₂ * D.xb v₁) * D.xc v₂ * (D.xd u₃ * D.xd v₃) := by rw [h2]
    _ = D.xb u₁ * D.xc u₂ * (D.xb v₁ * D.xc v₂) * D.xd u₃ * D.xd v₃ := by group
    _ = D.xb u₁ * D.xc u₂ * (D.xd u₃ * (D.xb v₁ * D.xc v₂)) * D.xd v₃ := by rw [h1]; group
    _ = _ := by group

theorem Φ_zero_left (v₂ v₃ : F) : D.Φ (0, v₂, v₃) = D.xc v₂ * D.xd v₃ := by
  simp [Φ, D.xb_zero]

theorem Φ_zero_zero (v₃ : F) : D.Φ (0, 0, v₃) = D.xd v₃ := by
  simp [Φ, D.xb_zero, D.xc_zero]

theorem Φ_inj {u v : F × F × F} (h : D.Φ u = D.Φ v) : u = v := by
  obtain ⟨h1, h2, h3⟩ := D.ext u.1 u.2.1 u.2.2 v.1 v.2.1 v.2.2 h
  exact Prod.ext h1 (Prod.ext h2 h3)

def Mf (t : F) (v : F × F × F) : F × F × F :=
  (v.1, v.2.1 + D.κ₁ * t * v.1, v.2.2 + D.κ₂ * t * v.2.1 + D.κ₃ * t ^ 2 * v.1)

def Lf (t : F) (v : F × F × F) : F × F × F :=
  (v.1 + D.μ₁ * t * v.2.1 + D.μ₃ * t ^ 2 * v.2.2, v.2.1 + D.μ₂ * t * v.2.2, v.2.2)

theorem conj_a_Φ (t : F) (v : F × F × F) : D.xa t * D.Φ v * D.xa (-t) = D.Φ (D.Mf t v) := by
  obtain ⟨v₁, v₂, v₃⟩ := v
  have e : D.xa t * D.Φ (v₁, v₂, v₃) * D.xa (-t) =
      (D.xa t * D.xb v₁ * D.xa (-t)) * (D.xa t * D.xc v₂ * D.xa (-t)) *
        (D.xa t * D.xd v₃ * D.xa (-t)) := by
    rw [D.xa_neg]
    simp only [Φ]
    group
  rw [e, D.conj_a_b, D.conj_a_c, D.conj_a_d]
  have e2 : D.xb v₁ * D.xc (D.κ₁ * t * v₁) * D.xd (D.κ₃ * t ^ 2 * v₁) *
      (D.xc v₂ * D.xd (D.κ₂ * t * v₂)) * D.xd v₃ =
      D.Φ (v₁, D.κ₁ * t * v₁, D.κ₃ * t ^ 2 * v₁) * D.Φ (0, v₂, D.κ₂ * t * v₂) *
        D.Φ (0, 0, v₃) := by
    rw [D.Φ_zero_left, D.Φ_zero_zero]
    rfl
  rw [e2, ← D.Φ_add, ← D.Φ_add]
  congr 1
  simp only [Mf, Prod.mk_add_mk, add_zero]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only
    ring
  · simp only
    ring

theorem conj_a'_Φ (t : F) (v : F × F × F) : D.xa' t * D.Φ v * D.xa' (-t) = D.Φ (D.Lf t v) := by
  obtain ⟨v₁, v₂, v₃⟩ := v
  have e : D.xa' t * D.Φ (v₁, v₂, v₃) * D.xa' (-t) =
      (D.xa' t * D.xb v₁ * D.xa' (-t)) * (D.xa' t * D.xc v₂ * D.xa' (-t)) *
        (D.xa' t * D.xd v₃ * D.xa' (-t)) := by
    rw [D.xa'_neg]
    simp only [Φ]
    group
  rw [e, D.conj_a'_b, D.conj_a'_c, D.conj_a'_d]
  have e2 : D.xb v₁ * (D.xc v₂ * D.xb (D.μ₁ * t * v₂)) *
      (D.xd v₃ * D.xc (D.μ₂ * t * v₃) * D.xb (D.μ₃ * t ^ 2 * v₃)) =
      D.Φ (v₁, 0, 0) * D.Φ (D.μ₁ * t * v₂, v₂, 0) *
        D.Φ (D.μ₃ * t ^ 2 * v₃, D.μ₂ * t * v₃, v₃) := by
    simp only [Φ, D.xc_zero, D.xd_zero, mul_one]
    have h1 : D.xc v₂ * D.xb (D.μ₁ * t * v₂) = D.xb (D.μ₁ * t * v₂) * D.xc v₂ :=
      (D.comm_bc _ _).symm
    have h2 : D.xd v₃ * D.xc (D.μ₂ * t * v₃) * D.xb (D.μ₃ * t ^ 2 * v₃) =
        D.xb (D.μ₃ * t ^ 2 * v₃) * D.xc (D.μ₂ * t * v₃) * D.xd v₃ := by
      calc D.xd v₃ * D.xc (D.μ₂ * t * v₃) * D.xb (D.μ₃ * t ^ 2 * v₃)
          = D.xc (D.μ₂ * t * v₃) * D.xd v₃ * D.xb (D.μ₃ * t ^ 2 * v₃) := by
            rw [← D.comm_cd (D.μ₂ * t * v₃) v₃]
        _ = D.xc (D.μ₂ * t * v₃) * (D.xd v₃ * D.xb (D.μ₃ * t ^ 2 * v₃)) := by group
        _ = D.xc (D.μ₂ * t * v₃) * (D.xb (D.μ₃ * t ^ 2 * v₃) * D.xd v₃) := by
            rw [← D.comm_bd (D.μ₃ * t ^ 2 * v₃) v₃]
        _ = (D.xc (D.μ₂ * t * v₃) * D.xb (D.μ₃ * t ^ 2 * v₃)) * D.xd v₃ := by group
        _ = D.xb (D.μ₃ * t ^ 2 * v₃) * D.xc (D.μ₂ * t * v₃) * D.xd v₃ := by
            rw [← D.comm_bc (D.μ₃ * t ^ 2 * v₃) (D.μ₂ * t * v₃)]
    rw [h1, h2]
  rw [e2, ← D.Φ_add, ← D.Φ_add]
  congr 1
  simp only [Lf, Prod.mk_add_mk, add_zero, zero_add]

theorem rev3 (a b c : F) : D.xd a * D.xc b * D.xb c = D.xb c * D.xc b * D.xd a := by
  calc D.xd a * D.xc b * D.xb c = D.xc b * D.xd a * D.xb c := by rw [← D.comm_cd b a]
    _ = D.xc b * (D.xd a * D.xb c) := by group
    _ = D.xc b * (D.xb c * D.xd a) := by rw [← D.comm_bd c a]
    _ = (D.xc b * D.xb c) * D.xd a := by group
    _ = D.xb c * D.xc b * D.xd a := by rw [← D.comm_bc c b]

theorem conj_n_Φ (v : F × F × F) :
    (D.xa 1 * D.xa' (-1) * D.xa 1) * D.Φ v * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹ =
      D.Φ (D.ηd * v.2.2, D.ηc * v.2.1, D.ηb * v.1) := by
  obtain ⟨v₁, v₂, v₃⟩ := v
  have e : (D.xa 1 * D.xa' (-1) * D.xa 1) * D.Φ (v₁, v₂, v₃) *
      (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹ =
      ((D.xa 1 * D.xa' (-1) * D.xa 1) * D.xb v₁ * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹) *
        ((D.xa 1 * D.xa' (-1) * D.xa 1) * D.xc v₂ * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹) *
        ((D.xa 1 * D.xa' (-1) * D.xa 1) * D.xd v₃ * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹) := by
    simp only [Φ]
    group
  rw [e, D.conj_n_b, D.conj_n_c, D.conj_n_d]
  exact D.rev3 _ _ _

theorem key (v : F × F × F) :
    D.Mf 1 (D.Lf (-1) (D.Mf 1 v)) = (D.ηd * v.2.2, D.ηc * v.2.1, D.ηb * v.1) := by
  apply D.Φ_inj
  rw [← D.conj_n_Φ v]
  have e : (D.xa 1 * D.xa' (-1) * D.xa 1) * D.Φ v * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹ =
      D.xa 1 * (D.xa' (-1) * (D.xa 1 * D.Φ v * D.xa (-1)) * D.xa' (-(-1))) * D.xa (-1) := by
    rw [D.xa_neg 1, D.xa'_neg (-1)]
    group
  rw [e, D.conj_a_Φ, D.conj_a'_Φ, D.conj_a_Φ]

theorem kappa_rel : D.κ₁ * D.κ₂ = 2 * D.κ₃ := by
  have h1 := D.conj_a_Φ (1 + 1) (1, 0, 0)
  have h2 : D.xa (1 + 1) * D.Φ (1, 0, 0) * D.xa (-(1 + 1)) =
      D.Φ (D.Mf 1 (D.Mf 1 (1, 0, 0))) := by
    rw [D.add_a, neg_add, D.add_a]
    have e : D.xa 1 * D.xa 1 * D.Φ (1, 0, 0) * (D.xa (-1) * D.xa (-1)) =
        D.xa 1 * (D.xa 1 * D.Φ (1, 0, 0) * D.xa (-1)) * D.xa (-1) := by group
    rw [e, D.conj_a_Φ, D.conj_a_Φ]
  have h3 := congrArg (fun w : F × F × F => w.2.2) (D.Φ_inj (h1.symm.trans h2))
  simp only [Mf] at h3
  linear_combination (-1 : F) * h3

theorem result : D.κ₃ = D.ηd ∧ D.κ₁ * D.κ₂ = 2 * D.ηd ∧ D.ηc = -1 ∧ D.ηb = D.ηd := by
  have E0 := D.kappa_rel
  have k1 := D.key (1, 0, 0)
  have k2 := D.key (0, 1, 0)
  have k3 := D.key (0, 0, 1)
  simp only [Mf, Lf, Prod.mk.injEq] at k1 k2 k3
  obtain ⟨a1, b1, c1⟩ := k1
  obtain ⟨a2, b2, c2⟩ := k2
  obtain ⟨a3, b3, c3⟩ := k3
  have e3 : D.μ₃ = D.ηd := by linear_combination a3
  have e6 : D.μ₂ = D.κ₁ * D.ηd := by linear_combination -b3 + D.κ₁ * a3
  have e9 : 1 - D.κ₂ * D.μ₂ + D.κ₃ * D.μ₃ = 0 := by linear_combination c3
  have hk3 : D.κ₃ * D.ηd = 1 := by
    linear_combination (-1 : F) * e9 + (-D.ηd) * E0 + (-D.κ₂) * e6 + D.κ₃ * e3
  have hk3' : D.κ₃ = D.ηd := by
    linear_combination D.ηd * hk3 + (-D.κ₃) * D.sq_d
  refine ⟨hk3', ?_, ?_, ?_⟩
  · rw [E0, hk3']
  · linear_combination D.κ₁ * a2 - b2 + (-2 : F) * hk3 + (-D.ηd) * E0 + (-D.κ₂) * e6
  · linear_combination hk3' + D.κ₂ * b1 + (D.κ₃ - D.κ₁ * D.κ₂) * a1 - c1

end VData

structure HData (G F : Type*) [Group G] [Field F] where
  xa : F → G
  xc : F → G
  xd : F → G
  xb : F → G
  xb' : F → G
  ν₁ : F
  ν₂ : F
  ρ₁ : F
  ρ₂ : F
  lam : F
  ηa : F
  ηc : F
  ηd : F
  add_a : ∀ s t, xa (s + t) = xa s * xa t
  add_c : ∀ s t, xc (s + t) = xc s * xc t
  add_d : ∀ s t, xd (s + t) = xd s * xd t
  add_b : ∀ s t, xb (s + t) = xb s * xb t
  add_b' : ∀ s t, xb' (s + t) = xb' s * xb' t
  comm_da : ∀ s t, xd s * xa t = xa t * xd s
  comm_dc : ∀ s t, xd s * xc t = xc t * xd s
  rel_ca : ∀ m n, xc m * xa n = xd (lam * m * n) * (xa n * xc m)
  conj_b_a : ∀ t v, xb t * xa v * xb (-t) = xc (ν₁ * t * v) * xd (ν₂ * t * v ^ 2) * xa v
  conj_b_c : ∀ t v, xb t * xc v * xb (-t) = xc v
  conj_b_d : ∀ t v, xb t * xd v * xb (-t) = xd v
  conj_b'_a : ∀ t v, xb' t * xa v * xb' (-t) = xa v
  conj_b'_c : ∀ t v, xb' t * xc v * xb' (-t) =
    xa (ρ₁ * t * v) * xd (ρ₂ * t * v ^ 2) * xc v
  conj_b'_d : ∀ t v, xb' t * xd v * xb' (-t) = xd v
  conj_n_a : ∀ v, xb 1 * xb' (-1) * xb 1 * xa v * (xb 1 * xb' (-1) * xb 1)⁻¹ = xc (ηa * v)
  conj_n_c : ∀ v, xb 1 * xb' (-1) * xb 1 * xc v * (xb 1 * xb' (-1) * xb 1)⁻¹ = xa (ηc * v)
  conj_n_d : ∀ v, xb 1 * xb' (-1) * xb 1 * xd v * (xb 1 * xb' (-1) * xb 1)⁻¹ = xd (ηd * v)
  ext : ∀ u₁ u₂ u₃ u₁' u₂' u₃', xa u₁ * xc u₂ * xd u₃ = xa u₁' * xc u₂' * xd u₃' →
    u₁ = u₁' ∧ u₂ = u₂' ∧ u₃ = u₃'

namespace HData

variable {G F : Type*} [Group G] [Field F] (D : HData G F)

theorem xa_zero : D.xa 0 = 1 := by
  have h := D.add_a 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xc_zero : D.xc 0 = 1 := by
  have h := D.add_c 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xd_zero : D.xd 0 = 1 := by
  have h := D.add_d 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xb_zero : D.xb 0 = 1 := by
  have h := D.add_b 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xb'_zero : D.xb' 0 = 1 := by
  have h := D.add_b' 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xb_neg (t : F) : D.xb (-t) = (D.xb t)⁻¹ := by
  have h := D.add_b t (-t)
  rw [add_neg_cancel, D.xb_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem xb'_neg (t : F) : D.xb' (-t) = (D.xb' t)⁻¹ := by
  have h := D.add_b' t (-t)
  rw [add_neg_cancel, D.xb'_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

def Ψ (v : F × F × F) : G := D.xa v.1 * D.xc v.2.1 * D.xd v.2.2

def hmul (u v : F × F × F) : F × F × F :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2 + D.lam * u.2.1 * v.1)

theorem Ψ_mul (u v : F × F × F) : D.Ψ u * D.Ψ v = D.Ψ (D.hmul u v) := by
  obtain ⟨u₁, u₂, u₃⟩ := u
  obtain ⟨v₁, v₂, v₃⟩ := v
  simp only [Ψ, hmul, D.add_a, D.add_c]
  calc D.xa u₁ * D.xc u₂ * D.xd u₃ * (D.xa v₁ * D.xc v₂ * D.xd v₃)
      = D.xa u₁ * D.xc u₂ * (D.xd u₃ * D.xa v₁) * D.xc v₂ * D.xd v₃ := by group
    _ = D.xa u₁ * D.xc u₂ * (D.xa v₁ * D.xd u₃) * D.xc v₂ * D.xd v₃ := by rw [D.comm_da u₃ v₁]
    _ = D.xa u₁ * (D.xc u₂ * D.xa v₁) * D.xd u₃ * D.xc v₂ * D.xd v₃ := by group
    _ = D.xa u₁ * (D.xd (D.lam * u₂ * v₁) * (D.xa v₁ * D.xc u₂)) * D.xd u₃ * D.xc v₂ * D.xd v₃ := by
        rw [D.rel_ca]
    _ = D.xa u₁ * (D.xd (D.lam * u₂ * v₁) * D.xa v₁) * D.xc u₂ * D.xd u₃ * D.xc v₂ * D.xd v₃ := by
        group
    _ = D.xa u₁ * (D.xa v₁ * D.xd (D.lam * u₂ * v₁)) * D.xc u₂ * D.xd u₃ * D.xc v₂ * D.xd v₃ := by
        rw [D.comm_da]
    _ = D.xa u₁ * D.xa v₁ * (D.xd (D.lam * u₂ * v₁) * D.xc u₂) * D.xd u₃ * D.xc v₂ * D.xd v₃ := by
        group
    _ = D.xa u₁ * D.xa v₁ * (D.xc u₂ * D.xd (D.lam * u₂ * v₁)) * D.xd u₃ * D.xc v₂ * D.xd v₃ := by
        rw [D.comm_dc]
    _ = D.xa u₁ * D.xa v₁ * D.xc u₂ * (D.xd (D.lam * u₂ * v₁) * D.xd u₃ * D.xc v₂) * D.xd v₃ := by
        group
    _ = D.xa u₁ * D.xa v₁ * D.xc u₂ * (D.xd (D.lam * u₂ * v₁ + u₃) * D.xc v₂) * D.xd v₃ := by
        rw [D.add_d]
    _ = D.xa u₁ * D.xa v₁ * D.xc u₂ * (D.xc v₂ * D.xd (D.lam * u₂ * v₁ + u₃)) * D.xd v₃ := by
        rw [D.comm_dc]
    _ = D.xa u₁ * D.xa v₁ * (D.xc u₂ * D.xc v₂) * (D.xd (D.lam * u₂ * v₁ + u₃) * D.xd v₃) := by
        group
    _ = _ := by
        rw [← D.add_d, show D.lam * u₂ * v₁ + u₃ + v₃ = u₃ + v₃ + D.lam * u₂ * v₁ by ring]

theorem Ψ_xa (v : F) : D.Ψ (v, 0, 0) = D.xa v := by
  simp [Ψ, D.xc_zero, D.xd_zero]

theorem Ψ_xc (v : F) : D.Ψ (0, v, 0) = D.xc v := by
  simp [Ψ, D.xa_zero, D.xd_zero]

theorem Ψ_xd (v : F) : D.Ψ (0, 0, v) = D.xd v := by
  simp [Ψ, D.xa_zero, D.xc_zero]

theorem Ψ_xcd (m m' : F) : D.Ψ (0, m, m') = D.xc m * D.xd m' := by
  simp [Ψ, D.xa_zero]

theorem Ψ_xad (p q : F) : D.Ψ (p, 0, q) = D.xa p * D.xd q := by
  simp [Ψ, D.xc_zero]

theorem Ψ_inj {u v : F × F × F} (h : D.Ψ u = D.Ψ v) : u = v := by
  obtain ⟨h1, h2, h3⟩ := D.ext u.1 u.2.1 u.2.2 v.1 v.2.1 v.2.2 h
  exact Prod.ext h1 (Prod.ext h2 h3)

def Uf (t : F) (v : F × F × F) : F × F × F :=
  (v.1, v.2.1 + D.ν₁ * t * v.1, v.2.2 + D.ν₂ * t * v.1 ^ 2 + D.lam * (D.ν₁ * t * v.1) * v.1)

def Lf (t : F) (v : F × F × F) : F × F × F :=
  (v.1 + D.ρ₁ * t * v.2.1, v.2.1, v.2.2 + D.ρ₂ * t * v.2.1 ^ 2)

def Nf (v : F × F × F) : F × F × F :=
  (D.ηc * v.2.1, D.ηa * v.1, D.lam * (D.ηa * v.1) * (D.ηc * v.2.1) + D.ηd * v.2.2)

theorem conj_b_Ψ (t : F) (v : F × F × F) : D.xb t * D.Ψ v * D.xb (-t) = D.Ψ (D.Uf t v) := by
  obtain ⟨v₁, v₂, v₃⟩ := v
  have e : D.xb t * D.Ψ (v₁, v₂, v₃) * D.xb (-t) =
      (D.xb t * D.xa v₁ * D.xb (-t)) * (D.xb t * D.xc v₂ * D.xb (-t)) *
        (D.xb t * D.xd v₃ * D.xb (-t)) := by
    rw [D.xb_neg]
    simp only [Ψ]
    group
  rw [e, D.conj_b_a, D.conj_b_c, D.conj_b_d]
  have e2 : D.xc (D.ν₁ * t * v₁) * D.xd (D.ν₂ * t * v₁ ^ 2) * D.xa v₁ * D.xc v₂ * D.xd v₃ =
      D.Ψ (0, D.ν₁ * t * v₁, D.ν₂ * t * v₁ ^ 2) * D.Ψ (v₁, 0, 0) * D.Ψ (0, v₂, 0) *
        D.Ψ (0, 0, v₃) := by
    rw [D.Ψ_xcd, D.Ψ_xa, D.Ψ_xc, D.Ψ_xd]
  rw [e2, D.Ψ_mul, D.Ψ_mul, D.Ψ_mul]
  congr 1
  simp only [hmul, Uf]
  refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))

theorem conj_b'_Ψ (t : F) (v : F × F × F) : D.xb' t * D.Ψ v * D.xb' (-t) = D.Ψ (D.Lf t v) := by
  obtain ⟨v₁, v₂, v₃⟩ := v
  have e : D.xb' t * D.Ψ (v₁, v₂, v₃) * D.xb' (-t) =
      (D.xb' t * D.xa v₁ * D.xb' (-t)) * (D.xb' t * D.xc v₂ * D.xb' (-t)) *
        (D.xb' t * D.xd v₃ * D.xb' (-t)) := by
    rw [D.xb'_neg]
    simp only [Ψ]
    group
  rw [e, D.conj_b'_a, D.conj_b'_c, D.conj_b'_d]
  have e2 : D.xa v₁ * (D.xa (D.ρ₁ * t * v₂) * D.xd (D.ρ₂ * t * v₂ ^ 2) * D.xc v₂) * D.xd v₃ =
      D.Ψ (v₁, 0, 0) * D.Ψ (D.ρ₁ * t * v₂, 0, D.ρ₂ * t * v₂ ^ 2) * D.Ψ (0, v₂, 0) *
        D.Ψ (0, 0, v₃) := by
    rw [D.Ψ_xad (D.ρ₁ * t * v₂) (D.ρ₂ * t * v₂ ^ 2), D.Ψ_xa, D.Ψ_xc, D.Ψ_xd]
    group
  rw [e2, D.Ψ_mul, D.Ψ_mul, D.Ψ_mul]
  congr 1
  simp only [hmul, Lf]
  refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))

theorem conj_n_Ψ (v : F × F × F) :
    (D.xb 1 * D.xb' (-1) * D.xb 1) * D.Ψ v * (D.xb 1 * D.xb' (-1) * D.xb 1)⁻¹ = D.Ψ (D.Nf v) := by
  obtain ⟨v₁, v₂, v₃⟩ := v
  have e : (D.xb 1 * D.xb' (-1) * D.xb 1) * D.Ψ (v₁, v₂, v₃) *
      (D.xb 1 * D.xb' (-1) * D.xb 1)⁻¹ =
      ((D.xb 1 * D.xb' (-1) * D.xb 1) * D.xa v₁ * (D.xb 1 * D.xb' (-1) * D.xb 1)⁻¹) *
        ((D.xb 1 * D.xb' (-1) * D.xb 1) * D.xc v₂ * (D.xb 1 * D.xb' (-1) * D.xb 1)⁻¹) *
        ((D.xb 1 * D.xb' (-1) * D.xb 1) * D.xd v₃ * (D.xb 1 * D.xb' (-1) * D.xb 1)⁻¹) := by
    simp only [Ψ]
    group
  rw [e, D.conj_n_a, D.conj_n_c, D.conj_n_d]
  have e2 : D.xc (D.ηa * v₁) * D.xa (D.ηc * v₂) * D.xd (D.ηd * v₃) =
      D.Ψ (0, D.ηa * v₁, 0) * D.Ψ (D.ηc * v₂, 0, 0) * D.Ψ (0, 0, D.ηd * v₃) := by
    rw [D.Ψ_xc, D.Ψ_xa, D.Ψ_xd]
  rw [e2, D.Ψ_mul, D.Ψ_mul]
  congr 1
  simp only [hmul, Nf]
  refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))

theorem key (v : F × F × F) : D.Uf 1 (D.Lf (-1) (D.Uf 1 v)) = D.Nf v := by
  apply D.Ψ_inj
  rw [← D.conj_n_Ψ v]
  have e : (D.xb 1 * D.xb' (-1) * D.xb 1) * D.Ψ v * (D.xb 1 * D.xb' (-1) * D.xb 1)⁻¹ =
      D.xb 1 * (D.xb' (-1) * (D.xb 1 * D.Ψ v * D.xb (-1)) * D.xb' (-(-1))) * D.xb (-1) := by
    rw [D.xb_neg 1, D.xb'_neg (-1)]
    group
  rw [e, D.conj_b_Ψ, D.conj_b'_Ψ, D.conj_b_Ψ]

theorem result : D.ν₁ = D.ηa ∧ D.ρ₁ = -D.ηc ∧ D.ρ₁ * D.ν₁ = 1 := by
  have k1 := D.key (1, 0, 0)
  have k2 := D.key (0, 1, 0)
  simp only [Uf, Lf, Nf, Prod.mk.injEq] at k1 k2
  obtain ⟨a1, b1, -⟩ := k1
  obtain ⟨a2, b2, -⟩ := k2
  have h1 : D.ρ₁ * D.ν₁ = 1 := by linear_combination -a1
  refine ⟨?_, ?_, h1⟩
  · linear_combination b1 + D.ν₁ * h1
  · linear_combination -a2

end HData

end CFSG.ClassicalInvolution.WeakCT
