module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36P

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_conj_rho_of_sup [Finite X] {J M : Subgroup X} {n : ℕ} (hn : 7 ≤ n)
    {e : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} (hJM : J ≤ M)
    (hsup : J ⊔ (pPrimeCore 2 ↥M).map M.subtype = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ)
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction e ρJ) :
    ∃ π : Perm (Fin n), ∀ (x : X) (hxJ : x ∈ normalizer (J : Set X))
      (hxM : x ∈ normalizer (M : Set X)), ρ ⟨x, hxM⟩ = π * ρJ ⟨x, hxJ⟩ * π⁻¹ := by
  classical
  obtain ⟨θJ, hθJ⟩ := exists_coreQuot_of_sup hJM hsup θ
  obtain ⟨π, hπ⟩ := exists_equiv_of_mulEquiv_alt (Fintype.card_fin n) (Fintype.card_fin n) hn
    (e.symm.trans θJ)
  have hπ' : ∀ y : ↥J ⧸ pPrimeCore 2 ↥J,
      ((θJ y : alternatingGroup (Fin n)) : Perm (Fin n)) =
        (π : Perm (Fin n)) * (e y : Perm (Fin n)) * (π : Perm (Fin n))⁻¹ := by
    intro y
    have h1 := hπ (e y)
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [h1]
    ext ω
    simp [Perm.mul_apply, Perm.inv_def]
  refine ⟨π, fun x hxJ hxM => ?_⟩
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨q, rfl⟩ := θJ.surjective a
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  have hxj : x * (j : X) * x⁻¹ ∈ J := (mem_normalizer_iff.mp hxJ j).mp j.2
  have hM := hρ ⟨x, hxM⟩ ⟨j, hJM j.2⟩
  have hJ := hρJ ⟨x, hxJ⟩ j
  have hjM : (M.normalizerMonoidHom ⟨x, hxM⟩ ⟨j, hJM j.2⟩ : ↥M) =
      ⟨x * j * x⁻¹, hJM hxj⟩ := Subtype.ext rfl
  have hjJ : (J.normalizerMonoidHom ⟨x, hxJ⟩ j : ↥J) = ⟨x * j * x⁻¹, hxj⟩ := Subtype.ext rfl
  rw [hjM] at hM
  rw [hjJ] at hJ
  have h1 := hθJ ⟨x * j * x⁻¹, hxj⟩
  have h2 := hθJ j
  change ρ ⟨x, hxM⟩ * ((θJ (j : ↥J ⧸ pPrimeCore 2 ↥J) : alternatingGroup (Fin n)) : Perm (Fin n)) *
      (ρ ⟨x, hxM⟩)⁻¹ = π * ρJ ⟨x, hxJ⟩ * π⁻¹ *
      ((θJ (j : ↥J ⧸ pPrimeCore 2 ↥J) : alternatingGroup (Fin n)) : Perm (Fin n)) *
      (π * ρJ ⟨x, hxJ⟩ * π⁻¹)⁻¹
  conv_rhs => rw [hπ' (j : ↥J ⧸ pPrimeCore 2 ↥J)]
  conv_lhs => rw [h2, ← hM, ← h1, hπ']
  rw [hJ]
  group

theorem card_support_rho_eq_rhoJ [Finite X] {J M : Subgroup X} {n : ℕ} (hn : 7 ≤ n)
    {e : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} (hJM : J ≤ M)
    (hsup : J ⊔ (pPrimeCore 2 ↥M).map M.subtype = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ)
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction e ρJ) {x : X}
    (hxJ : x ∈ normalizer (J : Set X)) (hxM : x ∈ normalizer (M : Set X)) :
    (ρ ⟨x, hxM⟩).support.card = (ρJ ⟨x, hxJ⟩).support.card := by
  obtain ⟨π, hπ⟩ := exists_conj_rho_of_sup hn hJM hsup hρ hρJ
  rw [hπ x hxJ hxM, Perm.card_support_conj]

end CFSG.ComponentClassification.SolMax
