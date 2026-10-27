module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinT

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.HeldLang
open scoped commutatorElement

theorem l154_false_of_displacement {F : Type} [Field F] {I : Type} [Fintype I] [DecidableEq I] {G : Type*} [Group G]
    (ι : G →* GL I F) (hperf : commutator G = ⊤) (σ : F ≃+* F) (B Q : GL I F)
    (Sc : GL I F → Prop) (hScS : ∀ v v', Sc v → Sc v' → v * v' = v' * v)
    (hScκ : ∀ v, Sc v → ∀ g : G, v * (Q * ι g * Q⁻¹) = (Q * ι g * Q⁻¹) * v)
    (hw : ∀ g : G, Sc ((B * glMap σ (ι g) * B⁻¹) * (Q * ι g * Q⁻¹)⁻¹))
    (N : Matrix I I F) (hN : N ≠ 0) (C₀ : Set F) (h1 : (1 : F) ∈ C₀) {c₁ : F}
    (hc₁ : c₁ ∈ C₀) (hσc : σ c₁ ≠ c₁)
    (hT : ∀ c ∈ C₀, ∃ t : G, ((ι t : GL I F) : Matrix I I F) = 1 + c • N) : False := by
  classical
  let γ₀ : G →* GL I F := ((MulAut.conj B).toMonoidHom.comp (glMap σ)).comp ι
  let κ₀ : G →* GL I F := (MulAut.conj Q).toMonoidHom.comp ι
  have hγ₀ : ∀ g : G, γ₀ g = B * glMap σ (ι g) * B⁻¹ := fun g => rfl
  have hκ₀ : ∀ g : G, κ₀ g = Q * ι g * Q⁻¹ := fun g => rfl
  have hγκ : ∀ g : G, γ₀ g = κ₀ g :=
    hom_of_displacement hperf γ₀ κ₀ Sc hScS (fun v hv g => by rw [hκ₀]; exact hScκ v hv g)
      (fun g => by rw [hγ₀, hκ₀]; exact hw g)
  have hBB : (B : Matrix I I F) * ((B⁻¹ : GL I F) : Matrix I I F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ : (Q : Matrix I I F) * ((Q⁻¹ : GL I F) : Matrix I I F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ' : ((Q⁻¹ : GL I F) : Matrix I I F) * (Q : Matrix I I F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set X : Matrix I I F := (B : Matrix I I F) * N.map σ *
    ((B⁻¹ : GL I F) : Matrix I I F) with hX
  set Y : Matrix I I F := (Q : Matrix I I F) * N *
    ((Q⁻¹ : GL I F) : Matrix I I F) with hY
  have hmat : ∀ c ∈ C₀, σ c • X = c • Y := by
    intro c hc
    obtain ⟨t, hιt⟩ := hT c hc
    have h1 := hγκ t
    have h2 : ((B * glMap σ (ι t) * B⁻¹ : GL I F) : Matrix I I F) =
        ((Q * ι t * Q⁻¹ : GL I F) : Matrix I I F) := by
      have := congrArg (fun g : GL I F => (g : Matrix I I F)) h1
      exact this
    have hγt : ((B * glMap σ (ι t) * B⁻¹ : GL I F) : Matrix I I F) = 1 + σ c • X := by
      have e1 : ((glMap σ (ι t) : GL I F) : Matrix I I F) = 1 + σ c • N.map σ := by
        rw [coe_glMap, hιt]
        ext i j
        simp [Matrix.one_apply, apply_ite σ]
      rw [Units.val_mul, Units.val_mul, e1, hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBB,
        Matrix.mul_smul, Matrix.smul_mul]
    have hκt : ((Q * ι t * Q⁻¹ : GL I F) : Matrix I I F) = 1 + c • Y := by
      rw [Units.val_mul, Units.val_mul, hιt, hY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQQ,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [hγt, hκt] at h2
    exact add_left_cancel h2
  have hXY : X = Y := by
    have := hmat 1 h1
    rwa [map_one, one_smul, one_smul] at this
  have hY0 : Y ≠ 0 := by
    intro h0
    apply hN
    have : ((Q⁻¹ : GL I F) : Matrix I I F) * Y * (Q : Matrix I I F) = N := by
      have e : ((Q⁻¹ : GL I F) : Matrix I I F) * ((Q : Matrix I I F) * N *
          ((Q⁻¹ : GL I F) : Matrix I I F)) * (Q : Matrix I I F) =
          (((Q⁻¹ : GL I F) : Matrix I I F) * (Q : Matrix I I F)) * N *
          (((Q⁻¹ : GL I F) : Matrix I I F) * (Q : Matrix I I F)) := by
        simp only [Matrix.mul_assoc]
      rw [hY, e, hQQ', Matrix.one_mul, Matrix.mul_one]
    rw [← this, h0, Matrix.mul_zero, Matrix.zero_mul]
  have h3 := hmat c₁ hc₁
  rw [hXY] at h3
  have h4 : (σ c₁ - c₁) • Y = 0 := by rw [sub_smul, h3, sub_self]
  rcases smul_eq_zero.1 h4 with h5 | h5
  · exact hσc (sub_eq_zero.1 h5)
  · exact hY0 h5

theorem l154_no_inner_of_line {F D : Type} [Field F] [Field D] {I : Type} [Fintype I] [DecidableEq I] {n₁ : ℕ}
    (ι : GL (Fin n₁) D →* GL I F) {M : Subgroup (GL (Fin n₁) D)} (hperf : commutator ↥M = ⊤)
    (σ : F ≃+* F) (B : GL I F) (P : GL (Fin n₁) D)
    (N : Matrix I I F) (hN : N ≠ 0) (C₀ : Set F) (h1 : (1 : F) ∈ C₀) {c₁ : F}
    (hc₁ : c₁ ∈ C₀) (hσc : σ c₁ ≠ c₁)
    (hT : ∀ c ∈ C₀, ∃ t ∈ M, ((ι t : GL I F) : Matrix I I F) = 1 + c • N)
    (h : ∀ m ∈ M, ∃ (z : Fˣ) (z' : Dˣ),
      Matrix.GeneralLinearGroup.scalar I z * (B * glMap σ (ι m) * B⁻¹) =
        ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z' * (P * m * P⁻¹))) : False := by
  classical
  set Q : GL I F := ι P with hQdef
  let Sc : GL I F → Prop := fun v =>
    ∃ (z : Fˣ) (z' : Dˣ), v = Matrix.GeneralLinearGroup.scalar I z *
      ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z')
  have hScg : ∀ v, Sc v → ∀ g : GL (Fin n₁) D, v * ι g = ι g * v := by
    rintro v ⟨z, z', rfl⟩ g
    have h1 := scalar_mul_comm z (ι g)
    have h2 : ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') * ι g =
        ι g * ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') := by
      rw [← map_mul, ← map_mul, scalar_mul_comm z' g]
    calc Matrix.GeneralLinearGroup.scalar I z * ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') * ι g
        = Matrix.GeneralLinearGroup.scalar I z * (ι g *
            ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z')) := by rw [mul_assoc, h2]
      _ = (Matrix.GeneralLinearGroup.scalar I z * ι g) *
            ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') := by rw [mul_assoc]
      _ = ι g * Matrix.GeneralLinearGroup.scalar I z *
            ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') := by rw [h1]
      _ = ι g * (Matrix.GeneralLinearGroup.scalar I z *
            ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z')) := by rw [mul_assoc]
  have hScS : ∀ v v', Sc v → Sc v' → v * v' = v' * v := by
    intro v v' hv hv'
    obtain ⟨z, z', rfl⟩ := hv'
    have h1 := hScg v hv (Matrix.GeneralLinearGroup.scalar (Fin n₁) z')
    have h2 := scalar_mul_comm z v
    calc v * (Matrix.GeneralLinearGroup.scalar I z *
          ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z'))
        = (v * Matrix.GeneralLinearGroup.scalar I z) *
          ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') := by rw [mul_assoc]
      _ = (Matrix.GeneralLinearGroup.scalar I z * v) *
          ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') := by rw [← h2]
      _ = Matrix.GeneralLinearGroup.scalar I z * (v *
          ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z')) := by rw [mul_assoc]
      _ = Matrix.GeneralLinearGroup.scalar I z * (
          ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') * v) := by rw [h1]
      _ = (Matrix.GeneralLinearGroup.scalar I z *
          ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z')) * v := by rw [mul_assoc]
  refine l154_false_of_displacement (ι.comp M.subtype) hperf σ B Q Sc hScS ?_ ?_ N hN C₀ h1 hc₁ hσc
    (fun c hc => by
      obtain ⟨t, ht, hιt⟩ := hT c hc
      exact ⟨⟨t, ht⟩, hιt⟩)
  · intro v hv g
    have : Q * (ι.comp M.subtype) g * Q⁻¹ = ι (P * (g : GL (Fin n₁) D) * P⁻¹) := by
      show ι P * ι (g : GL (Fin n₁) D) * (ι P)⁻¹ = _
      rw [map_mul, map_mul, map_inv]
    rw [this]
    exact hScg v hv _
  · intro g
    obtain ⟨z, z', hzz⟩ := h (g : GL (Fin n₁) D) g.2
    refine ⟨z⁻¹, z', ?_⟩
    have h1 : B * glMap σ ((ι.comp M.subtype) g) * B⁻¹ = (Matrix.GeneralLinearGroup.scalar I z)⁻¹ *
        (ι (Matrix.GeneralLinearGroup.scalar (Fin n₁) z') * (Q * (ι.comp M.subtype) g * Q⁻¹)) := by
      rw [eq_inv_mul_iff_mul_eq]
      have : ι (P * (g : GL (Fin n₁) D) * P⁻¹) = Q * (ι.comp M.subtype) g * Q⁻¹ := by
        show _ = ι P * ι (g : GL (Fin n₁) D) * (ι P)⁻¹
        rw [map_mul, map_mul, map_inv]
      rw [← this, ← map_mul]
      exact hzz
    rw [h1, map_inv]
    group

end CFSG.LocalAnalysis.GLTheoremA.K155X
