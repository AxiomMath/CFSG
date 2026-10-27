module

public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

noncomputable def componentConjPerm {B : Type} [Group B] (b : B) :
    Equiv.Perm (CFSG.LocalCores.ComponentIndex B) where
  toFun K :=
    ⟨K.1.map (MulAut.conj b).toMonoidHom,
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj b) K.2⟩
  invFun K :=
    ⟨K.1.map (MulAut.conj b⁻¹).toMonoidHom,
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj b⁻¹) K.2⟩
  left_inv K := by
    apply Subtype.ext
    show (K.1.map (MulAut.conj b).toMonoidHom).map (MulAut.conj b⁻¹).toMonoidHom = K.1
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj b⁻¹).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
        MonoidHom.id B := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  right_inv K := by
    apply Subtype.ext
    show (K.1.map (MulAut.conj b⁻¹).toMonoidHom).map (MulAut.conj b).toMonoidHom = K.1
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj b).toMonoidHom.comp (MulAut.conj b⁻¹).toMonoidHom =
        MonoidHom.id B := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]

noncomputable def componentConjAct {B : Type} [Group B] :
    B →* Equiv.Perm (CFSG.LocalCores.ComponentIndex B) where
  toFun := componentConjPerm
  map_one' := by
    apply Equiv.ext
    intro K
    apply Subtype.ext
    change K.1.map (MulAut.conj (1 : B)).toMonoidHom = K.1
    have h : (MulAut.conj (1 : B)).toMonoidHom = MonoidHom.id B := by
      ext x
      simp [MulAut.conj_apply]
    rw [h, Subgroup.map_id]
  map_mul' b₁ b₂ := by
    apply Equiv.ext
    intro K
    apply Subtype.ext
    show K.1.map (MulAut.conj (b₁ * b₂)).toMonoidHom =
      ((componentConjPerm b₁ * componentConjPerm b₂) K).1
    rw [Equiv.Perm.mul_apply]
    show K.1.map (MulAut.conj (b₁ * b₂)).toMonoidHom =
      (K.1.map (MulAut.conj b₂).toMonoidHom).map (MulAut.conj b₁).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

theorem normalizes_components_of_perfect {B : Type} [Group B] [Finite B] {Kg X : Type}
    [Group Kg] [Group X]
    (hperm : ∀ n : ℕ, n ≤ 26 → ∀ φ : X →* Equiv.Perm (Fin n), ∀ a ∈ commutator X, φ a = 1)
    (π : Kg →* X) (hπ : Function.Surjective π) (ψ : Kg →* B)
    (hker : ∀ k ∈ π.ker, ∀ K : Subgroup B, CFSG.IsComponent K → ∀ m ∈ K,
      ψ k * m * (ψ k)⁻¹ ∈ K)
    (hn : Nat.card {K : Subgroup B // CFSG.IsComponent K} ≤ 26) {Y : Subgroup Kg}
    (hY : ⁅Y, Y⁆ = Y) :
    ∀ y ∈ Y, ∀ K : Subgroup B, CFSG.IsComponent K → ∀ m ∈ K, ψ y * m * (ψ y)⁻¹ ∈ K := by
  classical
  let n : ℕ := Fintype.card (CFSG.LocalCores.ComponentIndex B)
  let e : CFSG.LocalCores.ComponentIndex B ≃ Fin n := Fintype.equivFin _
  let Θ : Kg →* Equiv.Perm (CFSG.LocalCores.ComponentIndex B) :=
    (componentConjAct (B := B)).comp ψ
  let Θ' : Kg →* Equiv.Perm (Fin n) := (Equiv.permCongrHom e).toMonoidHom.comp Θ
  have hfix_ker : ∀ k ∈ π.ker, ∀ K : Subgroup B, CFSG.IsComponent K →
      K.map (MulAut.conj (ψ k)).toMonoidHom = K := by
    intro k hk K hK
    apply le_antisymm
    · rintro x ⟨m, hm, rfl⟩
      change (MulAut.conj (ψ k)) m ∈ K
      simpa only [MulAut.conj_apply] using hker k hk K hK m hm
    · intro m hm
      have hk' : k⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker] at hk ⊢
        simp [hk]
      have hmem : (ψ k)⁻¹ * m * ψ k ∈ K := by
        have := hker k⁻¹ hk' K hK m hm
        simpa only [map_inv, inv_inv] using this
      refine Subgroup.mem_map.mpr ⟨(ψ k)⁻¹ * m * ψ k, hmem, ?_⟩
      change (MulAut.conj (ψ k)) ((ψ k)⁻¹ * m * ψ k) = m
      rw [MulAut.conj_apply]
      group
  have hΘ_ker : ∀ k ∈ π.ker, Θ k = 1 := by
    intro k hk
    apply Equiv.ext
    intro K
    apply Subtype.ext
    change (componentConjPerm (ψ k) K).1 = K.1
    exact hfix_ker k hk K K.2
  have hker_le : π.ker ≤ Θ'.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have : Θ' k = (Equiv.permCongrHom e) (Θ k) := rfl
    rw [this, hΘ_ker k hk, map_one]
  let φ : X →* Equiv.Perm (Fin n) :=
    (MonoidHom.liftOfSurjective (f := π) hπ) ⟨Θ', hker_le⟩
  have hφ : ∀ k : Kg, φ (π k) = Θ' k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply (f := π) (f_inv := Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨Θ', hker_le⟩ k
  have hn' : n ≤ 26 := by
    have h := hn
    rw [Nat.card_eq_fintype_card] at h
    exact h
  intro y hy K hK m hm
  have hmapY : Y.map π = ⁅Y.map π, Y.map π⁆ := by
    rw [← Subgroup.map_commutator (f := π) (H₁ := Y) (H₂ := Y), hY]
  have hcomm : π y ∈ commutator X := by
    have hy' : π y ∈ Y.map π := ⟨y, hy, rfl⟩
    rw [hmapY] at hy'
    exact Subgroup.commutator_mono le_top le_top hy'
  have hφ1 : φ (π y) = 1 := hperm n hn' φ (π y) hcomm
  have hΘ'y : Θ' y = 1 := by
    rw [← hφ y]
    exact hφ1
  have hΘy : Θ y = 1 := by
    have h : (Equiv.permCongrHom e) (Θ y) = 1 := by
      change Θ' y = 1
      exact hΘ'y
    exact (Equiv.permCongrHom e).map_eq_one_iff.mp h
  have hact : componentConjAct (B := B) (ψ y) = 1 := by
    simpa only [Θ, MonoidHom.comp_apply] using hΘy
  have hfix : K.map (MulAut.conj (ψ y)).toMonoidHom = K := by
    have hK' : componentConjAct (B := B) (ψ y) ⟨K, hK⟩ = ⟨K, hK⟩ := by
      rw [hact]
      rfl
    exact congrArg Subtype.val hK'
  have hmem : (MulAut.conj (ψ y)) m ∈ K := by
    rw [← hfix]
    exact Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
  simpa only [MulAut.conj_apply] using hmem

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
