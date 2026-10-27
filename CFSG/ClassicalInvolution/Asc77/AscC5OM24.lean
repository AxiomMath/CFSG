module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

section GL2

abbrev scl : Fˣ →* GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2)

abbrev glm (σ : F ≃+* F) : GL (Fin 2) F →* GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.map (σ : F →+* F)

theorem scl_commute (u : Fˣ) (g : GL (Fin 2) F) : Commute (scl u) g := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _

theorem glm_scl_mul (σ : F ≃+* F) (u : Fˣ) (g : GL (Fin 2) F) :
    glm σ (scl u * g) = scl (Units.map (σ : F →* F) u) * glm σ g := by
  rw [map_mul, glm, Matrix.GeneralLinearGroup.map_scalar]
  rfl

theorem glm_glm_comm [Finite F] (σ τ : F ≃+* F) (g : GL (Fin 2) F) :
    glm σ (glm τ g) = glm τ (glm σ g) := by
  have h := CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, RingHom.coe_coe]
  exact RingEquiv.congr_fun h (g i j)

theorem central_comm4 {G : Type*} [Group G] {c₁ c₂ c₃ c₄ : G} (h₂ : ∀ x, Commute c₂ x)
    (h₃ : ∀ x, Commute c₃ x) (h₄ : ∀ x, Commute c₄ x) (a b c e : G) :
    c₁ * a * (c₂ * b) * (c₃ * c)⁻¹ * (c₄ * e)⁻¹ =
      c₁ * c₂ * c₃⁻¹ * c₄⁻¹ * (a * b * c⁻¹ * e⁻¹) := by
  have e2 : a * c₂ = c₂ * a := ((h₂ a).eq).symm
  have e3 : a * b * c⁻¹ * c₃⁻¹ = c₃⁻¹ * (a * b * c⁻¹) :=
    (((h₃ (a * b * c⁻¹)).inv_left).eq).symm
  have e4 : a * b * c⁻¹ * e⁻¹ * c₄⁻¹ = c₄⁻¹ * (a * b * c⁻¹ * e⁻¹) :=
    (((h₄ (a * b * c⁻¹ * e⁻¹)).inv_left).eq).symm
  calc c₁ * a * (c₂ * b) * (c₃ * c)⁻¹ * (c₄ * e)⁻¹ =
      c₁ * (a * c₂) * b * c⁻¹ * c₃⁻¹ * e⁻¹ * c₄⁻¹ := by group
    _ = c₁ * c₂ * (a * b * c⁻¹ * c₃⁻¹) * e⁻¹ * c₄⁻¹ := by rw [e2]; group
    _ = c₁ * c₂ * c₃⁻¹ * (a * b * c⁻¹ * e⁻¹ * c₄⁻¹) := by rw [e3]; group
    _ = c₁ * c₂ * c₃⁻¹ * c₄⁻¹ * (a * b * c⁻¹ * e⁻¹) := by rw [e4]; group

theorem central_comm3 {G : Type*} [Group G] {c₁ c₂ c₃ : G} (h₂ : ∀ x, Commute c₂ x)
    (h₃ : ∀ x, Commute c₃ x) (a b c e : G) :
    c₁ * a * (c₂ * b) * (c₃ * c)⁻¹ * e⁻¹ = c₁ * c₂ * c₃⁻¹ * (a * b * c⁻¹ * e⁻¹) := by
  have h := central_comm4 (c₁ := c₁) h₂ h₃ (fun x => Commute.one_left x) a b c e
  rwa [one_mul, inv_one, mul_one] at h

theorem mul_central_mul {G : Type*} [Group G] {c : G} (hc : ∀ x, Commute c x) (x y z : G) :
    x * (y * c) * z = c * (x * y * z) := by
  calc x * (y * c) * z = x * y * (c * z) := by group
    _ = x * y * (z * c) := by rw [(hc z).eq]
    _ = x * y * z * c := by group
    _ = c * (x * y * z) := ((hc _).eq).symm

theorem fix_transport [Finite F] (d g n : GL (Fin 2) F) (σ τ : F ≃+* F) (ℓ κ : Fˣ) :
    scl ℓ * (d * g * (glm σ d)⁻¹) * glm σ (scl κ * (d * n * (glm τ d)⁻¹)) *
        (glm τ (scl ℓ * (d * g * (glm σ d)⁻¹)))⁻¹ * (scl κ * (d * n * (glm τ d)⁻¹))⁻¹ =
      scl (ℓ * Units.map (σ : F →* F) κ * (Units.map (τ : F →* F) ℓ)⁻¹ * κ⁻¹) *
        (d * (g * glm σ n * (glm τ g)⁻¹ * n⁻¹) * d⁻¹) := by
  rw [glm_scl_mul, glm_scl_mul, central_comm4 (fun x => scl_commute _ x)
    (fun x => scl_commute _ x) (fun x => scl_commute _ x)]
  have hs : scl ℓ * scl (Units.map (σ : F →* F) κ) * (scl (Units.map (τ : F →* F) ℓ))⁻¹ *
      (scl κ)⁻¹ = scl (ℓ * Units.map (σ : F →* F) κ * (Units.map (τ : F →* F) ℓ)⁻¹ * κ⁻¹) := by
    simp only [map_mul, map_inv]
  have hp : d * g * (glm σ d)⁻¹ * glm σ (d * n * (glm τ d)⁻¹) *
      (glm τ (d * g * (glm σ d)⁻¹))⁻¹ * (d * n * (glm τ d)⁻¹)⁻¹ =
      d * (g * glm σ n * (glm τ g)⁻¹ * n⁻¹) * d⁻¹ := by
    simp only [map_mul, map_inv]
    rw [glm_glm_comm τ σ d]
    group
  rw [hs, hp]

theorem swap_transport [Finite F] (d p n : GL (Fin 2) F) (π τ : F ≃+* F) (lam κ : Fˣ) :
    scl lam * (d⁻¹ * p * (glm π d)⁻¹) * glm π (scl κ * (d * n * (glm τ d)⁻¹)) *
        (glm τ (scl lam * (d⁻¹ * p * (glm π d)⁻¹)))⁻¹ * n⁻¹ =
      scl (lam * Units.map (π : F →* F) κ * (Units.map (τ : F →* F) lam)⁻¹ * κ) *
        (d⁻¹ * (p * glm π n * (glm τ p)⁻¹ * (scl κ * (d * n * (glm τ d)⁻¹))⁻¹) * d) := by
  rw [glm_scl_mul, glm_scl_mul, central_comm3 (fun x => scl_commute _ x)
    (fun x => scl_commute _ x)]
  have hR : d⁻¹ * (p * glm π n * (glm τ p)⁻¹ * (scl κ * (d * n * (glm τ d)⁻¹))⁻¹) * d =
      (scl κ)⁻¹ * (d⁻¹ * (p * glm π n * (glm τ p)⁻¹ * (d * n * (glm τ d)⁻¹)⁻¹) * d) := by
    rw [mul_inv_rev, ← mul_assoc (p * glm π n * (glm τ p)⁻¹)]
    exact mul_central_mul (fun x => (scl_commute κ x).inv_left) _ _ _
  have hs : scl lam * scl (Units.map (π : F →* F) κ) * (scl (Units.map (τ : F →* F) lam))⁻¹ =
      scl (lam * Units.map (π : F →* F) κ * (Units.map (τ : F →* F) lam)⁻¹ * κ) * (scl κ)⁻¹ := by
    simp only [map_mul, map_inv]
    group
  have hp : d⁻¹ * p * (glm π d)⁻¹ * glm π (d * n * (glm τ d)⁻¹) *
      (glm τ (d⁻¹ * p * (glm π d)⁻¹))⁻¹ * n⁻¹ =
      d⁻¹ * (p * glm π n * (glm τ p)⁻¹ * (d * n * (glm τ d)⁻¹)⁻¹) * d := by
    simp only [map_mul, map_inv]
    rw [glm_glm_comm τ π d]
    group
  rw [hR, hs, hp, mul_assoc]

end GL2

section Unique

theorem semilinear_unique (A B : GL (Fin 2) F) (α β : F ≃+* F)
    (h : ∀ b : SL(2, F), A * glm α (Matrix.SpecialLinearGroup.toGL b) * A⁻¹ =
      B * glm β (Matrix.SpecialLinearGroup.toGL b) * B⁻¹) :
    α = β ∧ ∃ ℓ : Fˣ, B = scl ℓ * A := by
  set H := B⁻¹ * A with hH
  have hHb : ∀ b : SL(2, F), H * glm α (Matrix.SpecialLinearGroup.toGL b) =
      glm β (Matrix.SpecialLinearGroup.toGL b) * H := fun b => by
    have e := h b
    calc H * glm α (Matrix.SpecialLinearGroup.toGL b) =
        B⁻¹ * (A * glm α (Matrix.SpecialLinearGroup.toGL b) * A⁻¹) * A := by rw [hH]; group
      _ = B⁻¹ * (B * glm β (Matrix.SpecialLinearGroup.toGL b) * B⁻¹) * A := by rw [e]
      _ = glm β (Matrix.SpecialLinearGroup.toGL b) * H := by rw [hH]; group
  let E : Fin 2 → F → SL(2, F) := fun i t =>
    ⟨if i = 0 then !![1, t; 0, 1] else !![1, 0; t, 1], by split_ifs <;> simp [Matrix.det_fin_two]⟩
  have hE : ∀ (σ : F ≃+* F) i t, ((glm σ (Matrix.SpecialLinearGroup.toGL (E i t)) :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = if i = 0 then !![1, σ t; 0, 1]
      else !![1, 0; σ t, 1] := by
    intro σ i t
    change (if i = 0 then !![1, t; 0, 1] else !![1, 0; t, 1]).map σ = _
    split_ifs <;> ext r c <;> fin_cases r <;> fin_cases c <;> simp
  have key : ∀ (i : Fin 2) (t : F), (H : Matrix (Fin 2) (Fin 2) F) * (if i = 0 then !![1, α t; 0, 1]
      else !![1, 0; α t, 1]) = (if i = 0 then !![1, β t; 0, 1] else !![1, 0; β t, 1]) *
      (H : Matrix (Fin 2) (Fin 2) F) := fun i t => by
    have e := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hHb (E i t))
    simp only [Units.val_mul] at e
    rwa [hE α, hE β] at e
  set Hm := (H : Matrix (Fin 2) (Fin 2) F) with hHm
  have k01 := key 0 1
  have k11 := key 1 1
  simp only [ite_true, map_one, one_ne_zero, ite_false] at k01 k11
  have a1 := congrFun (congrFun k01 0) 0
  have a2 := congrFun (congrFun k01 0) 1
  have a3 := congrFun (congrFun k11 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 a3
  have hH1 : Hm = Hm 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a1, a3]
    linear_combination -a2
  have hne : Hm 0 0 ≠ 0 := by
    intro h0
    have hd : Hm.det ≠ 0 := (Matrix.isUnits_det_units H).ne_zero
    rw [hH1, h0, zero_smul, Matrix.det_zero] at hd
    exact hd rfl
  have hαβ : α = β := by
    ext t
    have k := key 0 t
    simp only [ite_true] at k
    rw [hH1] at k
    have k' := congrFun (congrFun k 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at k'
    have k'' : Hm 0 0 * α t = Hm 0 0 * β t := by linear_combination k'
    exact mul_left_cancel₀ hne k''.symm |>.symm
  refine ⟨hαβ, (Units.mk0 _ hne)⁻¹, ?_⟩
  have hHs : H = scl (Units.mk0 _ hne) := by
    apply Units.ext
    change Hm = Matrix.scalar (Fin 2) (Hm 0 0)
    conv_lhs => rw [hH1]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hB : B = A * H⁻¹ := by rw [hH]; group
  rw [hB, hHs, map_inv, (scl_commute _ _).inv_left.eq]

end Unique

end CFSG.ClassicalInvolution.Asc77.C5O.M
