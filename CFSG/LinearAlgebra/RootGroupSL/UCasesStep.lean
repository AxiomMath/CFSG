module

public import CFSG.LinearAlgebra.RootGroupSL.UCasesParts
import CFSG.LinearAlgebra.RootGroupSL.FpfArith

public section

namespace CFSG.LinearAlgebra.RootGroupSL.UCasesStep

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

lemma add_self_eq_zero_mod (K : Type*) [Field K] [CharP K 2]
    {A : Type*} [AddCommGroup A] [Module K A] (x : A) : x + x = 0 := by
  calc x + x = (1 : K) • x + (1 : K) • x := by rw [one_smul]
    _ = ((1 : K) + 1) • x := (add_smul _ _ _).symm
    _ = 0 := by rw [CharTwo.add_self_eq_zero (1 : K), zero_smul]

lemma neg_eq_self_mod (K : Type*) [Field K] [CharP K 2]
    {A : Type*} [AddCommGroup A] [Module K A] (x : A) : -x = x := by
  rw [← neg_one_smul K x, CharTwo.neg_eq (1 : K), one_smul]

lemma symm_one_E : (1 : E ≃ₗ[k] E).symm = 1 := inv_one

lemma symm_one_X : (1 : X ≃ₗ[k] X).symm = 1 := inv_one

lemma mulLeftEquiv_toLinearMap (s : Eˣ) :
    (mulLeftEquiv k s : E →ₗ[k] E) = LinearMap.mulLeft k (s : E) := by
  ext x
  simp [mulLeftEquiv_apply]

lemma mulLeftEquiv_symm_toLinearMap (s : Eˣ) :
    ((mulLeftEquiv k s).symm : E →ₗ[k] E) = LinearMap.mulLeft k ((s⁻¹ : Eˣ) : E) := by
  rw [show (mulLeftEquiv k s).symm = mulLeftEquiv k (s⁻¹) from rfl]
  exact mulLeftEquiv_toLinearMap (s⁻¹)

lemma det_mulLeftEquiv_eq_one (s : Eˣ) (hs : Algebra.norm k (s : E) = 1) :
    LinearEquiv.det (mulLeftEquiv k s) = 1 := by
  apply Units.ext
  simpa using (det_mulLeft_eq_norm (mulLeftEquiv k s) (s : E)
    (mulLeftEquiv_toLinearMap s)).trans hs

lemma stable_mulLeft_of_generator {ν : Eˣ}
    (hgen : ∀ L : Subfield E, (ν : E) ∈ L → L = ⊤)
    (M : AddSubgroup (X →ₗ[k] E))
    (hν : ∀ φ : X →ₗ[k] E, φ ∈ M → LinearMap.mulLeft k (ν : E) ∘ₗ φ ∈ M) :
    ∀ (s : E) (φ : X →ₗ[k] E), φ ∈ M → LinearMap.mulLeft k s ∘ₗ φ ∈ M := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  let S : Subring E :=
    { carrier := {s : E | ∀ φ : X →ₗ[k] E, φ ∈ M → LinearMap.mulLeft k s ∘ₗ φ ∈ M}
      mul_mem' := by
        intro s t hs ht φ hφ
        rw [LinearMap.mulLeft_mul, LinearMap.comp_assoc]
        exact hs _ (ht _ hφ)
      one_mem' := by
        intro φ hφ
        simpa using hφ
      add_mem' := by
        intro s t hs ht φ hφ
        have hst : LinearMap.mulLeft k (s + t) =
            LinearMap.mulLeft k s + LinearMap.mulLeft k t := by
          ext x; simp [add_mul]
        rw [hst, LinearMap.add_comp]
        exact M.add_mem (hs _ hφ) (ht _ hφ)
      zero_mem' := by
        intro φ hφ
        simpa using M.zero_mem
      neg_mem' := by
        intro s hs φ hφ
        have hneg : LinearMap.mulLeft k (-s) = -LinearMap.mulLeft k s := by
          ext x; simp
        rw [hneg, LinearMap.neg_comp]
        exact M.neg_mem (hs _ hφ) }
  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0, inv_zero]
      exact S.zero_mem
    · have hcard : s ^ (Nat.card E - 1) = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one s hs0
      have h2 : 2 ≤ Nat.card E := by
        have := Fintype.one_lt_card (α := E)
        rw [Nat.card_eq_fintype_card]
        omega
      have hpow : s ^ (Nat.card E - 2) = s⁻¹ := by
        have hmul : s * s ^ (Nat.card E - 2) = 1 := by
          rw [mul_comm, ← pow_succ,
            show Nat.card E - 2 + 1 = Nat.card E - 1 by omega, hcard]
        exact eq_inv_of_mul_eq_one_right hmul
      rw [← hpow]
      exact S.pow_mem hs (Nat.card E - 2)
  let L : Subfield E := Subring.toSubfield S hinv
  have hνL : (ν : E) ∈ L := hν
  have htop : L = ⊤ := hgen L hνL
  intro s φ hφ
  have hs : s ∈ L := by rw [htop]; trivial
  exact hs φ hφ

lemma stable_comp_mulLeft_of_generator {ν : Eˣ}
    (hgen : ∀ L : Subfield E, (ν : E) ∈ L → L = ⊤)
    (M : AddSubgroup (E →ₗ[k] X))
    (hν : ∀ χ : E →ₗ[k] X, χ ∈ M → χ ∘ₗ LinearMap.mulLeft k (ν : E) ∈ M) :
    ∀ (s : E) (χ : E →ₗ[k] X), χ ∈ M → χ ∘ₗ LinearMap.mulLeft k s ∈ M := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  let S : Subring E :=
    { carrier := {s : E | ∀ χ : E →ₗ[k] X, χ ∈ M → χ ∘ₗ LinearMap.mulLeft k s ∈ M}
      mul_mem' := by
        intro s t hs ht χ hχ
        rw [LinearMap.mulLeft_mul, ← LinearMap.comp_assoc]
        exact ht _ (hs _ hχ)
      one_mem' := by
        intro χ hχ
        simpa using hχ
      add_mem' := by
        intro s t hs ht χ hχ
        have hst : LinearMap.mulLeft k (s + t) =
            LinearMap.mulLeft k s + LinearMap.mulLeft k t := by
          ext x; simp [add_mul]
        rw [hst, LinearMap.comp_add]
        exact M.add_mem (hs _ hχ) (ht _ hχ)
      zero_mem' := by
        intro χ hχ
        simpa using M.zero_mem
      neg_mem' := by
        intro s hs χ hχ
        have hneg : LinearMap.mulLeft k (-s) = -LinearMap.mulLeft k s := by
          ext x; simp
        rw [hneg, LinearMap.comp_neg]
        exact M.neg_mem (hs _ hχ) }
  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0, inv_zero]
      exact S.zero_mem
    · have hcard : s ^ (Nat.card E - 1) = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one s hs0
      have h2 : 2 ≤ Nat.card E := by
        have := Fintype.one_lt_card (α := E)
        rw [Nat.card_eq_fintype_card]
        omega
      have hpow : s ^ (Nat.card E - 2) = s⁻¹ := by
        have hmul : s * s ^ (Nat.card E - 2) = 1 := by
          rw [mul_comm, ← pow_succ,
            show Nat.card E - 2 + 1 = Nat.card E - 1 by omega, hcard]
        exact eq_inv_of_mul_eq_one_right hmul
      rw [← hpow]
      exact S.pow_mem hs (Nat.card E - 2)
  let L : Subfield E := Subring.toSubfield S hinv
  have hνL : (ν : E) ∈ L := hν
  have htop : L = ⊤ := hgen L hνL
  intro s χ hχ
  have hs : s ∈ L := by rw [htop]; trivial
  exact hs χ hχ

section

variable [Module.Finite k E]

lemma uSL_inv (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    (uSL φ χ ψ)⁻¹ = uSL φ χ (ψ + φ ∘ₗ χ) := by
  rw [← mul_eq_one_iff_inv_eq, uSL_mul]
  have h1 : φ + φ = 0 := by ext x; exact add_self_eq_zero_mod k (φ x)
  have h2 : χ + χ = 0 := by ext x; exact add_self_eq_zero_mod k (χ x)
  have h3 : ψ + (ψ + φ ∘ₗ χ) + φ ∘ₗ χ = 0 := by
    calc ψ + (ψ + φ ∘ₗ χ) + φ ∘ₗ χ
        = (ψ + ψ) + ((φ ∘ₗ χ) + (φ ∘ₗ χ)) := by abel
      _ = 0 := by rw [add_self_eq_zero_mod k ψ, add_self_eq_zero_mod k (φ ∘ₗ χ), add_zero]
  rw [h1, h2, h3, uSL_zero]

lemma uSL_mul_phi_psi (φ : X →ₗ[k] E) (ψ : E →ₗ[k] E) :
    uSL φ 0 0 * uSL 0 0 ψ = uSL φ 0 ψ := by
  rw [uSL_mul, uSL_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp

lemma uSL_mul_chi_psi (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    uSL 0 χ 0 * uSL 0 0 ψ = uSL 0 χ ψ := by
  rw [uSL_mul, uSL_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp

lemma uSL_factor (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    uSL φ 0 0 * uSL 0 χ 0 * uSL 0 0 (ψ + φ ∘ₗ χ) = uSL φ χ ψ := by
  rw [uSL_mul, uSL_mul, uSL_inj]
  refine ⟨?_, ?_, ?_⟩
  · ext x; simp
  · ext x; simp
  · ext x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, add_zero, zero_add, map_zero,
      LinearMap.zero_apply]
    rw [add_comm (ψ x) (φ (χ x)), ← add_assoc, add_self_eq_zero_mod k, zero_add]

lemma blockSL_mulLeft_one_one_mem_normalizer (s : Eˣ)
    (hs : Algebra.norm k (s : E) = 1) :
    blockSL (mulLeftEquiv k s) 1 1 (by rw [det_mulLeftEquiv_eq_one s hs]; simp) ∈
      Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) := by
  rw [blockSL_mem_normalizer_iff]
  intro t
  refine ⟨(s : E) * t, ?_⟩
  ext x
  rw [symm_one_E]
  change (s : E) * (t * x) = ((s : E) * t) * x
  rw [mul_assoc]

lemma blockSL_one_one_mulLeft_mem_normalizer (s : Eˣ)
    (hs : Algebra.norm k (s : E) = 1) :
    blockSL 1 1 (mulLeftEquiv k s) (by rw [det_mulLeftEquiv_eq_one s hs]; simp) ∈
      Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) := by
  rw [blockSL_mem_normalizer_iff]
  intro t
  refine ⟨t * (s : E)⁻¹, ?_⟩
  ext x
  rw [mulLeftEquiv_symm_toLinearMap, Units.val_inv_eq_inv_val]
  change t * ((s : E)⁻¹ * x) = (t * (s : E)⁻¹) * x
  rw [mul_assoc]

lemma blockSL_one_g_one_mem_normalizer (g : SpecialLinearGroup k X) :
    blockSL 1 (g : X ≃ₗ[k] X) 1 (by simp) ∈
      Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) := by
  rw [blockSL_mem_normalizer_iff]
  intro t
  refine ⟨t, ?_⟩
  ext x
  rw [symm_one_E]
  change (1 : E →ₗ[k] E) ((LinearMap.mulLeft k t) x) = (LinearMap.mulLeft k t) x
  rfl

lemma blockSL_mulLeft_one_one_conj (s : Eˣ) (hs : Algebra.norm k (s : E) = 1)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    blockSL (mulLeftEquiv k s) 1 1 (by rw [det_mulLeftEquiv_eq_one s hs]; simp) * uSL φ χ ψ *
        (blockSL (mulLeftEquiv k s) 1 1 (by rw [det_mulLeftEquiv_eq_one s hs]; simp))⁻¹ =
      uSL (LinearMap.mulLeft k (s : E) ∘ₗ φ) χ (LinearMap.mulLeft k (s : E) ∘ₗ ψ) := by
  rw [blockSL_mul_uSL_mul_inv]
  simp only [symm_one_E, symm_one_X]
  rw [uSL_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> rfl

lemma blockSL_one_one_mulLeft_conj (s : Eˣ) (hs : Algebra.norm k (s : E) = 1)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    blockSL 1 1 (mulLeftEquiv k s) (by rw [det_mulLeftEquiv_eq_one s hs]; simp) * uSL φ χ ψ *
        (blockSL 1 1 (mulLeftEquiv k s) (by rw [det_mulLeftEquiv_eq_one s hs]; simp))⁻¹ =
      uSL φ (χ ∘ₗ LinearMap.mulLeft k ((s⁻¹ : Eˣ) : E))
        (ψ ∘ₗ LinearMap.mulLeft k ((s⁻¹ : Eˣ) : E)) := by
  rw [blockSL_mul_uSL_mul_inv]
  simp only [symm_one_E, symm_one_X]
  rw [uSL_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> rfl

lemma blockSL_one_g_one_conj (g : SpecialLinearGroup k X)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    blockSL 1 (g : X ≃ₗ[k] X) 1 (by simp) * uSL φ χ ψ *
        (blockSL 1 (g : X ≃ₗ[k] X) 1 (by simp))⁻¹ =
      uSL (φ ∘ₗ (g : X ≃ₗ[k] X).symm.toLinearMap) ((g : X ≃ₗ[k] X).toLinearMap ∘ₗ χ) ψ := by
  rw [blockSL_mul_uSL_mul_inv]
  simp only [symm_one_E, symm_one_X]
  rw [uSL_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> rfl

lemma commutator_mulLeft (s : Eˣ) (hs : Algebra.norm k (s : E) = 1)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    ∃ ψ' : E →ₗ[k] E,
      blockSL (mulLeftEquiv k s) 1 1 (by rw [det_mulLeftEquiv_eq_one s hs]; simp) * uSL φ χ ψ *
        (blockSL (mulLeftEquiv k s) 1 1 (by rw [det_mulLeftEquiv_eq_one s hs]; simp))⁻¹ *
        (uSL φ χ ψ)⁻¹ =
      uSL (LinearMap.mulLeft k ((s : E) + 1) ∘ₗ φ) 0 ψ' := by
  refine ⟨(LinearMap.mulLeft k (s : E) ∘ₗ ψ) + (ψ + φ ∘ₗ χ) +
    (LinearMap.mulLeft k (s : E) ∘ₗ φ) ∘ₗ χ, ?_⟩
  rw [blockSL_mulLeft_one_one_conj s hs φ χ ψ, uSL_inv, uSL_mul, uSL_inj]
  refine ⟨?_, ?_, rfl⟩
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.mulLeft_apply]
    rw [add_mul, one_mul]
  · ext x
    simp [add_self_eq_zero_mod k]

lemma commutator_one_one_mulLeft (s : Eˣ) (hs : Algebra.norm k (s : E) = 1)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    ∃ ψ' : E →ₗ[k] E,
      blockSL 1 1 (mulLeftEquiv k s) (by rw [det_mulLeftEquiv_eq_one s hs]; simp) * uSL φ χ ψ *
        (blockSL 1 1 (mulLeftEquiv k s) (by rw [det_mulLeftEquiv_eq_one s hs]; simp))⁻¹ *
        (uSL φ χ ψ)⁻¹ =
      uSL 0 (χ ∘ₗ LinearMap.mulLeft k (((s⁻¹ : Eˣ) : E) + 1)) ψ' := by
  refine ⟨(ψ ∘ₗ LinearMap.mulLeft k ((s⁻¹ : Eˣ) : E)) + (ψ + φ ∘ₗ χ) + φ ∘ₗ χ, ?_⟩
  rw [blockSL_one_one_mulLeft_conj s hs φ χ ψ, uSL_inv, uSL_mul, uSL_inj]
  refine ⟨?_, ?_, rfl⟩
  · ext x
    simp [add_self_eq_zero_mod k]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.mulLeft_apply]
    rw [add_mul, one_mul, map_add]

end

end CFSG.LinearAlgebra.RootGroupSL.UCasesStep
