module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDRho

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

variable {L : Type} [Field L] {n : ℕ}

theorem comm_mulVec_iff (M N : Matrix (Fin n) (Fin n) L) :
    (∀ x, M *ᵥ (N *ᵥ x) = N *ᵥ (M *ᵥ x)) ↔ M * N = N * M := by
  constructor
  · intro h
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h x
  · intro h x
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem hfm_mulVec_iff {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (M : Matrix (Fin n) (Fin n) L) :
    (∀ x y, hfm τ (M *ᵥ x) (M *ᵥ y) = hfm τ x y) ↔ adjM τ M * M = 1 := by
  constructor
  · intro h
    have h' : ∀ x y, hfm τ x ((adjM τ M * M) *ᵥ y) = hfm τ x y := by
      intro x y
      rw [← Matrix.mulVec_mulVec, ← hfm_mulVec, h]
    have hN : ∀ y, (adjM τ M * M) *ᵥ y = y := by
      intro y
      have hz : (adjM τ M * M) *ᵥ y - y = 0 := by
        apply hfm_nondeg τ
        intro z
        rw [hfm_comm_tau hτ, hfm_sub_right', h' z y, sub_self, map_zero]
      exact sub_eq_zero.mp hz
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hN y, Matrix.one_mulVec]
  · intro h x y
    rw [hfm_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem toLin_val_apply {L' : Type} [Field L'] {n' : ℕ} (g : GL (Fin n') L') (x : Fin n' → L') :
    (Matrix.GeneralLinearGroup.toLin g).val x = (g : Matrix (Fin n') (Fin n') L') *ᵥ x :=
  rfl

theorem mem_centralizer_heldGU_iff {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (s g : GL (Fin n) L) :
    g ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ Held.heldGU n L τ hτ ↔
      Matrix.GeneralLinearGroup.toLin g ∈ Glin τ (s : Matrix (Fin n) (Fin n) L) := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Held.mem_heldGU]
  simp only [Set.mem_singleton_iff, forall_eq]
  have hL : (s * g = g * s) ↔
      ((s : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) =
        (g : Matrix (Fin n) (Fin n) L) * (s : Matrix (Fin n) (Fin n) L)) := by
    simp only [Units.ext_iff, Units.val_mul]
  have hA := (comm_mulVec_iff (g : Matrix (Fin n) (Fin n) L) (s : Matrix (Fin n) (Fin n) L))
  have hB := hfm_mulVec_iff (τ := τ) hτ (g : Matrix (Fin n) (Fin n) L)
  have hC : (s * g = g * s) ↔
      (∀ x, (g : Matrix (Fin n) (Fin n) L) *ᵥ ((s : Matrix (Fin n) (Fin n) L) *ᵥ x) =
        (s : Matrix (Fin n) (Fin n) L) *ᵥ ((g : Matrix (Fin n) (Fin n) L) *ᵥ x)) :=
    hL.trans (eq_comm.trans hA.symm)
  show (s * g = g * s) ∧ _ ↔ (∀ x, (Matrix.GeneralLinearGroup.toLin g).val
      ((s : Matrix (Fin n) (Fin n) L) *ᵥ x) = (s : Matrix (Fin n) (Fin n) L) *ᵥ
        (Matrix.GeneralLinearGroup.toLin g).val x) ∧
      ∀ x y, hfm τ ((Matrix.GeneralLinearGroup.toLin g).val x)
        ((Matrix.GeneralLinearGroup.toLin g).val y) = hfm τ x y
  simp only [toLin_val_apply]
  exact and_congr hC hB.symm

noncomputable def centralizerEquivGlin {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (s : GL (Fin n) L) :
    ↥(Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ Held.heldGU n L τ hτ) ≃*
      ↥(Glin τ (s : Matrix (Fin n) (Fin n) L)) where
  toFun g := ⟨Matrix.GeneralLinearGroup.toLin g.1, (mem_centralizer_heldGU_iff hτ s g.1).mp g.2⟩
  invFun h := ⟨Matrix.GeneralLinearGroup.toLin.symm h.1, (mem_centralizer_heldGU_iff hτ s _).mpr (by
    rw [MulEquiv.apply_symm_apply]
    exact h.2)⟩
  left_inv g := Subtype.ext (Matrix.GeneralLinearGroup.toLin.symm_apply_apply g.1)
  right_inv h := Subtype.ext (Matrix.GeneralLinearGroup.toLin.apply_symm_apply h.1)
  map_mul' g h := Subtype.ext (map_mul Matrix.GeneralLinearGroup.toLin g.1 h.1)

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
