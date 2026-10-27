module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

open Subgroup

variable {X : Type*} [Group X]

theorem eq_one_of_conj_mem_of_forall_isPGroup_eq_bot (hZ : Subgroup.center X = ⊥)
    {B : Subgroup X} {Q : Subgroup (MulAut X)} (hQ : IsPGroup 2 Q)
    (hQB : ∀ b ∈ B, MulAut.conj b ∈ normalizer (Q : Set (MulAut X)))
    (hR : ∀ R : Subgroup X, IsPGroup 2 R → B ≤ normalizer (R : Set X) → R = ⊥)
    {x : X} (hx : MulAut.conj x ∈ Q) : x = 1 := by
  let R : Subgroup X := Q.comap (MulAut.conj : X →* MulAut X)
  have hR2 : IsPGroup 2 R := by
    intro r
    obtain ⟨k, hk⟩ := hQ ⟨MulAut.conj (r : X), r.2⟩
    refine ⟨k, ?_⟩
    have hk' : (MulAut.conj (r : X)) ^ (2 ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    have hconj : MulAut.conj ((r : X) ^ (2 ^ k)) = 1 := by
      rw [map_pow]
      exact hk'
    refine Subtype.ext ?_
    have hcenter : (r : X) ^ (2 ^ k) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (r : X) ^ (2 ^ k) * g * ((r : X) ^ (2 ^ k))⁻¹ = g := by
        change MulAut.conj ((r : X) ^ (2 ^ k)) g = g
        rw [hconj]
        rfl
      have hyg : (r : X) ^ (2 ^ k) * g = g * (r : X) ^ (2 ^ k) := by
        calc (r : X) ^ (2 ^ k) * g
            = ((r : X) ^ (2 ^ k) * g * ((r : X) ^ (2 ^ k))⁻¹) *
                (r : X) ^ (2 ^ k) := by group
          _ = g * (r : X) ^ (2 ^ k) := by rw [hg]
      exact hyg.symm
    rwa [hZ, Subgroup.mem_bot] at hcenter
  have hforward : ∀ b ∈ B, ∀ y ∈ R, b * y * b⁻¹ ∈ R := by
    intro b hb y hy
    change MulAut.conj (b * y * b⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    have hbQ := hQB b hb
    rw [Subgroup.mem_normalizer_iff] at hbQ
    exact (hbQ (MulAut.conj y)).mp hy
  have hBnormalizer : B ≤ normalizer (R : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hforward b hb y
    · intro hy
      have h := hforward b⁻¹ (B.inv_mem hb) (b * y * b⁻¹) hy
      rwa [show b⁻¹ * (b * y * b⁻¹) * (b⁻¹)⁻¹ = y by group] at h
  have hRbot : R = ⊥ := hR R hR2 hBnormalizer
  have hxR : x ∈ R := hx
  rwa [hRbot, Subgroup.mem_bot] at hxR

theorem apply_eq_of_forall_isPGroup_eq_bot (hZ : Subgroup.center X = ⊥)
    {B : Subgroup X} {Q : Subgroup (MulAut X)} (hQ : IsPGroup 2 Q)
    (hQB : ∀ b ∈ B, MulAut.conj b ∈ normalizer (Q : Set (MulAut X)))
    (hR : ∀ R : Subgroup X, IsPGroup 2 R → B ≤ normalizer (R : Set X) → R = ⊥) :
    ∀ α ∈ Q, ∀ b ∈ B, α b = b := by
  intro α hα b hb
  have hmem : MulAut.conj (α b * b⁻¹) ∈ Q := by
    have hconj : MulAut.conj (α b * b⁻¹) =
        α * (MulAut.conj b * α⁻¹ * (MulAut.conj b)⁻¹) := by
      rw [map_mul, map_inv]
      ext x
      simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
    rw [hconj]
    have hbQ := hQB b hb
    rw [Subgroup.mem_normalizer_iff] at hbQ
    exact Q.mul_mem hα ((hbQ α⁻¹).mp (Q.inv_mem hα))
  have hx1 : α b * b⁻¹ = 1 :=
    eq_one_of_conj_mem_of_forall_isPGroup_eq_bot hZ hQ hQB hR hmem
  rwa [mul_inv_eq_one] at hx1

theorem snd_eq_one_of_mulAut_prod_fix_fst {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] [IsSimpleGroup A] (α : MulAut (A × B)) {a : A} (ha : a ≠ 1)
    (h : α (a, 1) = (a, 1)) : ∀ x : A, (α (x, 1)).2 = 1 := by
  let F : Subgroup (A × B) := (⊤ : Subgroup A).prod (⊥ : Subgroup B)
  let M : Subgroup (A × B) := F.map α.toMonoidHom
  have hFnormal : F.Normal := Subgroup.prod_normal ⊤ ⊥
  have hMnormal : M.Normal := hFnormal.map α.toMonoidHom α.surjective
  let P : Subgroup (A × B) := M ⊓ F
  have hPnormal : P.Normal := Subgroup.normal_inf_normal M F
  let P₁ : Subgroup A := P.comap (MonoidHom.inl A B)
  have hP₁normal : P₁.Normal := hPnormal.comap (MonoidHom.inl A B)
  have hmemF : (a, 1) ∈ F := by
    show (a, 1) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup B)
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, by simp⟩
  have haP : a ∈ P₁ := by
    show (a, 1) ∈ P
    refine ⟨?_, ?_⟩
    · have h1 : α (a, 1) ∈ M := Subgroup.mem_map_of_mem α.toMonoidHom hmemF
      rwa [h] at h1
    · exact hmemF
  have hP₁top : P₁ = ⊤ := by
    haveI : P₁.Normal := hP₁normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P₁ with hbot | htop
    · exfalso
      rw [hbot, Subgroup.mem_bot] at haP
      exact ha haP
    · exact htop
  have htop : ∀ x : A, (x, 1) ∈ P := by
    intro x
    have hx : x ∈ P₁ := by
      rw [hP₁top]
      exact Subgroup.mem_top x
    simpa [P₁] using hx
  have hFM : F ≤ M := by
    intro z hz
    have hz2 : z.2 = 1 := by
      simpa using (Subgroup.mem_prod.mp hz).2
    have hzP : z ∈ P := by
      have hz' : z = (z.1, 1) := by ext <;> simp [hz2]
      rw [hz']
      exact htop z.1
    exact hzP.1
  have hcard : Nat.card M = Nat.card F :=
    Subgroup.card_map_of_injective (f := α.toMonoidHom) (K := F) α.injective
  have hMF : F = M := Subgroup.eq_of_le_of_card_ge hFM (le_of_eq hcard)
  intro x
  have hmemM : α (x, 1) ∈ M :=
    Subgroup.mem_map_of_mem α.toMonoidHom (by
      show (x, 1) ∈ F
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top x, by simp⟩)
  rw [← hMF] at hmemM
  simpa using (Subgroup.mem_prod.mp hmemM).2

theorem prod_factors_of_apply_eq {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] [Finite Y₁] [Finite Y₂]
    [IsSimpleGroup Y₁] [IsSimpleGroup Y₂] (α : MulAut (Y₁ × Y₂)) {a₁ : Y₁} {a₂ : Y₂}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (h₁ : α (a₁, 1) = (a₁, 1)) (h₂ : α (1, a₂) = (1, a₂)) :
    (∀ y : Y₁, (α (y, 1)).2 = 1) ∧ ∀ y : Y₂, (α (1, y)).1 = 1 := by
  constructor
  · exact snd_eq_one_of_mulAut_prod_fix_fst α ha₁ h₁
  · let β : MulAut (Y₂ × Y₁) :=
      MulAut.congr (MulEquiv.prodComm : Y₁ × Y₂ ≃* Y₂ × Y₁) α
    have hβ : β (a₂, 1) = (a₂, 1) := by
      simp [β, MulAut.congr, h₂]
    intro y
    have hy := snd_eq_one_of_mulAut_prod_fix_fst β ha₂ hβ y
    simpa [β, MulAut.congr] using hy

end CFSG.GroupTheory

end
