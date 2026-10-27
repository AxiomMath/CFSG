module

public import CFSG.LargeExtraspecial.GLRCentNormal
public import Mathlib.GroupTheory.Nilpotent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Module

variable {F : Type*} [Field F] {k m : ℕ}

@[expose] def nilBlockMap (A D : (Fin k → F) →ₗ[F] (Fin k → F))
    (K : (Fin m → F) →ₗ[F] (Fin m → F)) (B : (Fin m → F) →ₗ[F] (Fin k → F))
    (C : (Fin k → F) →ₗ[F] (Fin m → F)) :
    NilModel F k m →ₗ[F] NilModel F k m :=
  (A ∘ₗ LinearMap.fst F (Fin k → F) ((Fin m → F) × (Fin k → F))).prod
    ((C ∘ₗ LinearMap.fst F (Fin k → F) ((Fin m → F) × (Fin k → F)) +
        K ∘ₗ LinearMap.fst F (Fin m → F) (Fin k → F) ∘ₗ
          LinearMap.snd F (Fin k → F) ((Fin m → F) × (Fin k → F))).prod
      (D ∘ₗ LinearMap.fst F (Fin k → F) ((Fin m → F) × (Fin k → F)) +
        B ∘ₗ LinearMap.fst F (Fin m → F) (Fin k → F) ∘ₗ
          LinearMap.snd F (Fin k → F) ((Fin m → F) × (Fin k → F)) +
        A ∘ₗ LinearMap.snd F (Fin m → F) (Fin k → F) ∘ₗ
          LinearMap.snd F (Fin k → F) ((Fin m → F) × (Fin k → F))))

section Block

variable (A D : (Fin k → F) →ₗ[F] (Fin k → F)) (K : (Fin m → F) →ₗ[F] (Fin m → F))
  (B : (Fin m → F) →ₗ[F] (Fin k → F)) (C : (Fin k → F) →ₗ[F] (Fin m → F))

@[simp]
theorem nilBlockMap_apply (w : NilModel F k m) :
    nilBlockMap A D K B C w = (A w.1, C w.1 + K w.2.1, D w.1 + B w.2.1 + A w.2.2) := rfl

theorem nilBlockMap_nilModelMap (w : NilModel F k m) :
    nilBlockMap A D K B C (nilModelMap F k m w) = nilModelMap F k m (nilBlockMap A D K B C w) := by
  simp

variable {A K} in
theorem nilBlockMap_injective (hA : Function.Injective A) (hK : Function.Injective K) :
    Function.Injective (nilBlockMap A D K B C) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, z, y⟩ h
  simp only [nilBlockMap_apply, Prod.mk_eq_zero] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hx : x = 0 := hA (by rw [h1, map_zero])
  subst hx
  rw [map_zero, zero_add] at h2
  have hz : z = 0 := hK (by rw [h2, map_zero])
  subst hz
  rw [map_zero, map_zero, zero_add, zero_add] at h3
  have hy : y = 0 := hA (by rw [h3, map_zero])
  subst hy
  rfl

end Block

abbrev NilModelCent (F : Type*) [Field F] (k m : ℕ) : Type _ :=
  {h : NilModel F k m ≃ₗ[F] NilModel F k m //
    ∀ w, h (nilModelMap F k m w) = nilModelMap F k m (h w)}

section Blocks

variable (h : NilModel F k m →ₗ[F] NilModel F k m)

@[expose] def nilBlkA : (Fin k → F) →ₗ[F] (Fin k → F) :=
  LinearMap.fst F (Fin k → F) ((Fin m → F) × (Fin k → F)) ∘ₗ h ∘ₗ
    LinearMap.inl F (Fin k → F) ((Fin m → F) × (Fin k → F))

@[expose] def nilBlkD : (Fin k → F) →ₗ[F] (Fin k → F) :=
  LinearMap.snd F (Fin m → F) (Fin k → F) ∘ₗ
    LinearMap.snd F (Fin k → F) ((Fin m → F) × (Fin k → F)) ∘ₗ h ∘ₗ
      LinearMap.inl F (Fin k → F) ((Fin m → F) × (Fin k → F))

@[expose] def nilBlkK : (Fin m → F) →ₗ[F] (Fin m → F) :=
  LinearMap.fst F (Fin m → F) (Fin k → F) ∘ₗ
    LinearMap.snd F (Fin k → F) ((Fin m → F) × (Fin k → F)) ∘ₗ h ∘ₗ
      LinearMap.inr F (Fin k → F) ((Fin m → F) × (Fin k → F)) ∘ₗ
        LinearMap.inl F (Fin m → F) (Fin k → F)

@[expose] def nilBlkB : (Fin m → F) →ₗ[F] (Fin k → F) :=
  LinearMap.snd F (Fin m → F) (Fin k → F) ∘ₗ
    LinearMap.snd F (Fin k → F) ((Fin m → F) × (Fin k → F)) ∘ₗ h ∘ₗ
      LinearMap.inr F (Fin k → F) ((Fin m → F) × (Fin k → F)) ∘ₗ
        LinearMap.inl F (Fin m → F) (Fin k → F)

@[expose] def nilBlkC : (Fin k → F) →ₗ[F] (Fin m → F) :=
  LinearMap.fst F (Fin m → F) (Fin k → F) ∘ₗ
    LinearMap.snd F (Fin k → F) ((Fin m → F) × (Fin k → F)) ∘ₗ h ∘ₗ
      LinearMap.inl F (Fin k → F) ((Fin m → F) × (Fin k → F))

@[simp] theorem nilBlkA_apply (x : Fin k → F) : nilBlkA h x = (h (x, 0)).1 := rfl
@[simp] theorem nilBlkD_apply (x : Fin k → F) : nilBlkD h x = (h (x, 0)).2.2 := rfl
@[simp] theorem nilBlkK_apply (z : Fin m → F) : nilBlkK h z = (h (0, z, 0)).2.1 := rfl
@[simp] theorem nilBlkB_apply (z : Fin m → F) : nilBlkB h z = (h (0, z, 0)).2.2 := rfl
@[simp] theorem nilBlkC_apply (x : Fin k → F) : nilBlkC h x = (h (x, 0)).2.1 := rfl

variable {h} (hc : ∀ w, h (nilModelMap F k m w) = nilModelMap F k m (h w))
include hc

theorem nilModel_apply_zero_zero (y : Fin k → F) : h (0, 0, y) = (0, 0, nilBlkA h y) := by
  have := hc (y, 0)
  simpa using this

theorem nilModel_apply_zero_fst (z : Fin m → F) : (h (0, z, 0)).1 = 0 := by
  have := hc (0, z, 0)
  simp only [nilModelMap_apply, Prod.mk_zero_zero, map_zero] at this
  exact (congrArg (fun w : NilModel F k m => w.2.2) this).symm

theorem eq_nilBlockMap (w : NilModel F k m) :
    h w = nilBlockMap (nilBlkA h) (nilBlkD h) (nilBlkK h) (nilBlkB h) (nilBlkC h) w := by
  obtain ⟨x, z, y⟩ := w
  have hw : ((x, z, y) : NilModel F k m) = (x, 0) + (0, z, 0) + (0, 0, y) := by simp
  rw [hw, map_add, map_add, nilModel_apply_zero_zero hc]
  ext i <;> simp [nilModel_apply_zero_fst hc]

end Blocks

section Card

variable {h : NilModel F k m ≃ₗ[F] NilModel F k m}
  (hc : ∀ w, h (nilModelMap F k m w) = nilModelMap F k m (h w))
include hc

theorem nilBlkA_injective :
    Function.Injective (nilBlkA (h : NilModel F k m →ₗ[F] NilModel F k m)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have h1 := nilModel_apply_zero_zero hc y
  rw [hy] at h1
  have h2 : ((0, 0, y) : NilModel F k m) = 0 := h.injective (by rw [map_zero]; exact h1)
  exact congrArg (fun w : NilModel F k m => w.2.2) h2

theorem nilBlkK_injective :
    Function.Injective (nilBlkK (h : NilModel F k m →ₗ[F] NilModel F k m)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have h2 : h (0, z, 0) = (0, 0, nilBlkB (h : NilModel F k m →ₗ[F] NilModel F k m) z) := by
    ext i
    · exact congrFun (nilModel_apply_zero_fst hc z) i
    · exact congrFun hz i
    · rfl
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp (nilBlkA_injective hc))
    (nilBlkB (h : NilModel F k m →ₗ[F] NilModel F k m) z)
  have h4 : h (0, 0, y) = (0, 0, nilBlkA (h : NilModel F k m →ₗ[F] NilModel F k m) y) :=
    nilModel_apply_zero_zero hc y
  have h3 : h (0, 0, y) = h (0, z, 0) := by rw [h4, hy, h2]
  exact (congrArg (fun w : NilModel F k m => w.2.1) (h.injective h3)).symm

end Card

private noncomputable def nilModelCentEquiv : NilModelCent F k m ≃
    ((Fin k → F) ≃ₗ[F] (Fin k → F)) × ((Fin m → F) ≃ₗ[F] (Fin m → F)) ×
      ((Fin k → F) →ₗ[F] (Fin k → F)) × ((Fin m → F) →ₗ[F] (Fin k → F)) ×
        ((Fin k → F) →ₗ[F] (Fin m → F)) where
  toFun h := (LinearEquiv.ofInjectiveEndo _ (nilBlkA_injective h.2),
    LinearEquiv.ofInjectiveEndo _ (nilBlkK_injective h.2),
    nilBlkD (h.1 : NilModel F k m →ₗ[F] NilModel F k m),
    nilBlkB (h.1 : NilModel F k m →ₗ[F] NilModel F k m),
    nilBlkC (h.1 : NilModel F k m →ₗ[F] NilModel F k m))
  invFun p := ⟨LinearEquiv.ofInjectiveEndo
    (nilBlockMap (p.1 : (Fin k → F) →ₗ[F] (Fin k → F)) p.2.2.1
      (p.2.1 : (Fin m → F) →ₗ[F] (Fin m → F)) p.2.2.2.1 p.2.2.2.2)
    (nilBlockMap_injective _ _ _ p.1.injective p.2.1.injective),
    fun w => nilBlockMap_nilModelMap _ _ _ _ _ w⟩
  left_inv h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    exact (eq_nilBlockMap h.2 w).symm
  right_inv p := by
    obtain ⟨A, K, D, B, C⟩ := p
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · exact LinearEquiv.ext fun x => by simp
    · exact LinearEquiv.ext fun z => by simp
    · exact LinearMap.ext fun x => by simp
    · exact LinearMap.ext fun z => by simp
    · exact LinearMap.ext fun x => by simp

theorem card_linearEquiv_fin_eq_card_GL (a : ℕ) :
    Nat.card ((Fin a → F) ≃ₗ[F] (Fin a → F)) = Nat.card (GL (Fin a) F) :=
  Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin a → F))).toEquiv.symm

theorem card_linearMap_fin_eq_pow (a b : ℕ) :
    Nat.card ((Fin a → F) →ₗ[F] (Fin b → F)) = Nat.card F ^ (a * b) := by
  rw [Nat.card_congr (LinearMap.toMatrix' (R := F) (m := Fin b) (n := Fin a)).toEquiv]
  change Nat.card (Fin b → Fin a → F) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]

theorem card_nilModelCent (F : Type*) [Field F] (k m : ℕ) :
    Nat.card (NilModelCent F k m) =
      Nat.card (GL (Fin k) F) * Nat.card (GL (Fin m) F) * Nat.card F ^ (k * k + m * k + k * m) := by
  rw [Nat.card_congr nilModelCentEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    card_linearEquiv_fin_eq_card_GL, card_linearEquiv_fin_eq_card_GL, card_linearMap_fin_eq_pow,
    card_linearMap_fin_eq_pow,
    card_linearMap_fin_eq_pow, pow_add, pow_add]
  ring

end CFSG.LargeExtraspecial.GLR
