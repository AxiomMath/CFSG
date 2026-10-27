module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open Matrix CFSG.Open

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

abbrev Eset (d : Fin 6 → F) (l₀ : F) : Finset (Fin 6) := Finset.univ.filter fun k => d k = l₀

abbrev emb (d : Fin 6 → F) (l₀ : F) : Fin (Eset d l₀).card ↪o Fin 6 :=
  (Eset d l₀).orderEmbOfFin rfl

@[expose] def Sm (d : Fin 6 → F) (l₀ : F) : Matrix (Fin 6) (Fin (Eset d l₀).card) F :=
  fun k i => if k = emb d l₀ i then 1 else 0

theorem mem_range_emb_iff (d : Fin 6 → F) (l₀ : F) (k : Fin 6) :
    k ∈ Set.range (emb d l₀) ↔ d k = l₀ := by
  rw [emb, Finset.range_orderEmbOfFin]
  simp

theorem sum_emb_ite (d : Fin 6 → F) (l₀ : F) (k : Fin 6) :
    ∑ i, (if k = emb d l₀ i then (1 : F) else 0) = if d k = l₀ then 1 else 0 := by
  by_cases hk : d k = l₀
  · rw [if_pos hk]
    obtain ⟨i0, hi0⟩ : k ∈ Set.range (emb d l₀) := (mem_range_emb_iff d l₀ k).2 hk
    simp only [← hi0]
    simp [(emb d l₀).injective.eq_iff, Finset.sum_ite_eq']
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hk ((mem_range_emb_iff d l₀ k).1 ⟨i, h.symm⟩)

theorem Sm_transpose_mul_Sm (d : Fin 6 → F) (l₀ : F) : (Sm d l₀)ᵀ * Sm d l₀ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Sm, Matrix.transpose_apply]
  simp only [ite_mul, Matrix.one_mul, zero_mul, mul_ite, Matrix.mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem Sm_mul_transpose_eq (d : Fin 6 → F) (l₀ : F) :
    Sm d l₀ * (Sm d l₀)ᵀ = eigP d l₀ := by
  ext k k'
  rw [Matrix.mul_apply, eigP, Matrix.diagonal_apply]
  simp only [Sm, Matrix.transpose_apply]
  have hterm : ∀ i : Fin (Eset d l₀).card,
      (if k = emb d l₀ i then (1 : F) else 0) * (if k' = emb d l₀ i then (1 : F) else 0) =
        (if k = k' then 1 else 0) * (if k = emb d l₀ i then (1 : F) else 0) := by
    intro i
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, sum_emb_ite]
  by_cases hkk : k = k'
  · subst hkk; simp
  · simp [hkk]

theorem eigP_mul_Sm (d : Fin 6 → F) (l₀ : F) : eigP d l₀ * Sm d l₀ = Sm d l₀ := by
  rw [← Sm_mul_transpose_eq, Matrix.mul_assoc, Sm_transpose_mul_Sm, Matrix.mul_one]

theorem Smt_mul_eigP (d : Fin 6 → F) (l₀ : F) : (Sm d l₀)ᵀ * eigP d l₀ = (Sm d l₀)ᵀ := by
  have h := congrArg Matrix.transpose (eigP_mul_Sm d l₀)
  rw [Matrix.transpose_mul, eigP_transpose] at h
  exact h

theorem rhoU_inv₁ {d : Fin 6 → F} {l₀ : F} {g : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ = eigP d l₀ * g) :
    (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ *
      ((Sm d l₀)ᵀ * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀) = 1 := by
  calc (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ *
        ((Sm d l₀)ᵀ * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀)
      = (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * (Sm d l₀ * (Sm d l₀)ᵀ) *
          ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by
        simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ *
          ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by
        rw [Sm_mul_transpose_eq]
    _ = (Sm d l₀)ᵀ * ((g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀) *
          ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by
        simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * (eigP d l₀ * (g : Matrix (Fin 6) (Fin 6) F)) *
          ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by
        rw [hg]
    _ = (Sm d l₀)ᵀ * eigP d l₀ * ((g : Matrix (Fin 6) (Fin 6) F) *
          ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) * Sm d l₀ := by
        simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * eigP d l₀ * Sm d l₀ := by
        rw [Units.mul_inv, Matrix.mul_one]
    _ = (Sm d l₀)ᵀ * Sm d l₀ := by rw [Smt_mul_eigP]
    _ = 1 := Sm_transpose_mul_Sm d l₀

theorem rhoU_inv₂ {d : Fin 6 → F} {l₀ : F} {g : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ = eigP d l₀ * g) :
    (Sm d l₀)ᵀ * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ *
      ((Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀) = 1 := by
  have hgi : ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ * (g : Matrix (Fin 6) (Fin 6) F)
      = eigP d l₀ := by
    calc ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ * (g : Matrix (Fin 6) (Fin 6) F)
        = ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (eigP d l₀ * (g : Matrix (Fin 6) (Fin 6) F)) :=
          Matrix.mul_assoc _ _ _
      _ = ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * ((g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀) := by
          rw [← hg]
      _ = eigP d l₀ := Units.inv_mul_cancel_left _ _
  calc (Sm d l₀)ᵀ * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ *
        ((Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀)
      = (Sm d l₀)ᵀ * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (Sm d l₀ * (Sm d l₀)ᵀ) *
          (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ *
          (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by rw [Sm_mul_transpose_eq]
    _ = (Sm d l₀)ᵀ * (((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ *
          (g : Matrix (Fin 6) (Fin 6) F)) * Sm d l₀ := by simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * eigP d l₀ * Sm d l₀ := by rw [hgi]
    _ = (Sm d l₀)ᵀ * Sm d l₀ := by rw [Smt_mul_eigP]
    _ = 1 := Sm_transpose_mul_Sm d l₀

@[expose] def rhoU (d : Fin 6 → F) (l₀ : F) (g : GL (Fin 6) F) :
    GL (Fin (Eset d l₀).card) F :=
  if hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ = eigP d l₀ * g then
    Units.mk ((Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀)
      ((Sm d l₀)ᵀ * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * Sm d l₀)
      (rhoU_inv₁ hg) (rhoU_inv₂ hg)
  else 1

theorem rhoU_val {d : Fin 6 → F} {l₀ : F} {g : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ = eigP d l₀ * g) :
    ((rhoU d l₀ g : GL (Fin (Eset d l₀).card) F) : Matrix _ _ F) =
      (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by
  unfold rhoU
  rw [dif_pos hg]

theorem comm_proj {d : Fin 6 → F} {l₀ : F} {g : Matrix (Fin 6) (Fin 6) F}
    (hg : g * eigP d l₀ = eigP d l₀ * g) : eigP d l₀ * g * eigP d l₀ = g * eigP d l₀ := by
  calc eigP d l₀ * g * eigP d l₀ = eigP d l₀ * (g * eigP d l₀) := Matrix.mul_assoc _ _ _
    _ = eigP d l₀ * (eigP d l₀ * g) := by rw [hg]
    _ = (eigP d l₀ * eigP d l₀) * g := (Matrix.mul_assoc _ _ _).symm
    _ = eigP d l₀ * g := by rw [eigP_mul_same]
    _ = g * eigP d l₀ := hg.symm

theorem rhoU_mul {d : Fin 6 → F} {l₀ : F} {g k : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ = eigP d l₀ * g)
    (hk : (k : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ = eigP d l₀ * k) :
    rhoU d l₀ (g * k) = rhoU d l₀ g * rhoU d l₀ k := by
  have hgk := commute_mul_of hg hk
  apply Units.ext
  rw [rhoU_val hgk, Units.val_mul, Units.val_mul, rhoU_val hg, rhoU_val hk]
  calc (Sm d l₀)ᵀ * ((g : Matrix (Fin 6) (Fin 6) F) * (k : Matrix (Fin 6) (Fin 6) F)) * Sm d l₀
      = (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * (k : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by
        simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * (k : Matrix (Fin 6) (Fin 6) F) *
          (eigP d l₀ * Sm d l₀) := by rw [eigP_mul_Sm]
    _ = (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * ((k : Matrix (Fin 6) (Fin 6) F) * eigP d l₀) *
          Sm d l₀ := by simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * (eigP d l₀ * (k : Matrix (Fin 6) (Fin 6) F)) *
          Sm d l₀ := by rw [hk]
    _ = (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ * (k : Matrix (Fin 6) (Fin 6) F) *
          Sm d l₀ := by simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * (Sm d l₀ * (Sm d l₀)ᵀ) *
          (k : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by rw [Sm_mul_transpose_eq]
    _ = ((Sm d l₀)ᵀ * (g : Matrix (Fin 6) (Fin 6) F) * Sm d l₀) *
          ((Sm d l₀)ᵀ * (k : Matrix (Fin 6) (Fin 6) F) * Sm d l₀) := by simp only [Matrix.mul_assoc]

@[expose] def rhoHom (d : Fin 6 → F) (l₀ : F) : ↥(Ug d l₀) →* GL (Fin (Eset d l₀).card) F where
  toFun h := rhoU d l₀ h.1.1
  map_one' := by
    have h1 : ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ =
        eigP d l₀ * ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
      rw [Units.val_one, Matrix.one_mul, Matrix.mul_one]
    show rhoU d l₀ 1 = 1
    apply Units.ext
    rw [rhoU_val h1, Units.val_one, Units.val_one, Matrix.mul_one, Sm_transpose_mul_Sm]
  map_mul' := fun h k => by
    show rhoU d l₀ (h.1.1 * k.1.1) = rhoU d l₀ h.1.1 * rhoU d l₀ k.1.1
    exact rhoU_mul (h.2.1 l₀) (k.2.1 l₀)

theorem rhoHom_injective (d : Fin 6 → F) (l₀ : F) : Function.Injective (rhoHom d l₀) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have hg := h.2.1 l₀
  have hh' : rhoU d l₀ h.1.1 = 1 := hh
  have hv := congrArg Units.val hh'
  rw [rhoU_val hg, Units.val_one] at hv
  have hgP : (h.1.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ = eigP d l₀ := by
    calc (h.1.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l₀
        = eigP d l₀ * (h.1.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ := (comm_proj hg).symm
      _ = (Sm d l₀ * (Sm d l₀)ᵀ) * (h.1.1 : Matrix (Fin 6) (Fin 6) F) * (Sm d l₀ * (Sm d l₀)ᵀ) := by
          rw [Sm_mul_transpose_eq]
      _ = Sm d l₀ * ((Sm d l₀)ᵀ * (h.1.1 : Matrix (Fin 6) (Fin 6) F) * Sm d l₀) * (Sm d l₀)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Sm d l₀ * (Sm d l₀)ᵀ := by rw [hv, Matrix.mul_one]
      _ = eigP d l₀ := Sm_mul_transpose_eq d l₀
  have hQ := h.2.2
  have hmat : (h.1.1 : Matrix (Fin 6) (Fin 6) F) = 1 := by
    calc (h.1.1 : Matrix (Fin 6) (Fin 6) F)
        = (h.1.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ +
            (h.1.1 : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l₀) := by
          rw [← mul_add, add_sub_cancel, Matrix.mul_one]
      _ = eigP d l₀ + (1 - eigP d l₀) := by rw [hgP, hQ]
      _ = 1 := add_sub_cancel _ _
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show (h.1.1 : Matrix (Fin 6) (Fin 6) F) = 1
  exact hmat

theorem card_Ug_dvd_GL (d : Fin 6 → F) (l₀ : F) :
    Nat.card ↥(Ug d l₀) ∣ Nat.card (GL (Fin (Eset d l₀).card) F) :=
  Subgroup.card_dvd_of_injective (rhoHom d l₀) (rhoHom_injective d l₀)

theorem not_dvd41_card_GL {a : ℕ} (hF : Nat.card F = 16) (ha : a ≤ 4) :
    ¬ 41 ∣ Nat.card (GL (Fin a) F) := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  haveI : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_GL_field, hq]
  interval_cases a <;> norm_num [Fin.prod_univ_succ]

end CFSG.LocalAnalysis.GLTheoremA.SFM12
