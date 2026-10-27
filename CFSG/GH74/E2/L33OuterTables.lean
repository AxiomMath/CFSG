module

public import Mathlib
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.Checks
public meta import Mathlib
public meta import CFSG.GH74.KGroups.L33
public import CFSG.GH74.E2.L33OuterTablesInputs
public meta import CFSG.GH74.E2.L33OuterTablesInputs
public import Certificates.Certificate5012
public import Certificates.Certificate5120

public section

namespace CFSG.GH74.E2

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

section Checks

variable {n : ℕ}

theorem isOuterInv_iff (QP : RawSchreierDatum n) (hQP : ValidSchreier QP)
    (τ : Equiv.Perm (Fin n)) :
    isOuterInv QP τ = true ↔ τ ^ 2 = 1 ∧ τ ∉ QP.originalSubgroup := by
  have h := mem_iff_sift QP hQP τ
  simp only [isOuterInv, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', h]
  simp

theorem outerConjCheck_sound (QP QA : RawSchreierDatum n) (hQP : ValidSchreier QP)
    (hQA : ValidSchreier QA) (h : outerConjCheck QP (elemsT QA) = true) :
    ∃ τ0 ∈ QA.originalSubgroup, τ0 ^ 2 = 1 ∧ τ0 ∉ QP.originalSubgroup ∧
      ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ QP.originalSubgroup →
        ∃ σ ∈ QA.originalSubgroup, σ * τ0 * σ⁻¹ = τ := by
  obtain ⟨τ0, hτ0L, hτ0⟩ := List.any_eq_true.1 h
  rw [outerConjAt, Bool.and_eq_true] at hτ0
  obtain ⟨hτ0o, hall⟩ := hτ0
  obtain ⟨hτ02, hτ0P⟩ := (isOuterInv_iff QP hQP τ0).1 hτ0o
  refine ⟨τ0, (mem_elemsT QA hQA τ0).1 hτ0L, hτ02, hτ0P, ?_⟩
  intro τ hτ hτ2 hτP
  have h1 := List.all_eq_true.1 hall τ ((mem_elemsT QA hQA τ).2 hτ)
  rw [Bool.or_eq_true] at h1
  rcases h1 with h2 | h2
  · exfalso
    have h3 : isOuterInv QP τ = true := (isOuterInv_iff QP hQP τ).2 ⟨hτ2, hτP⟩
    rw [h3] at h2
    exact absurd h2 (by decide)
  · obtain ⟨σ, hσL, hσ⟩ := List.any_eq_true.1 h2
    exact ⟨σ, (mem_elemsT QA hQA σ).1 hσL, of_decide_eq_true hσ⟩

theorem outerCommCheck_sound (QP QA : RawSchreierDatum n) (hQP : ValidSchreier QP)
    (hQA : ValidSchreier QA) (h : outerCommCheck QP (elemsT QA) (elemsT QP) = true) :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ QP.originalSubgroup →
      ∃ a ∈ QP.originalSubgroup, ∃ b ∈ QP.originalSubgroup, a * τ = τ * a ∧ b * τ = τ * b ∧
        (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1 := by
  intro τ hτ hτ2 hτP
  have h1 := List.all_eq_true.1 h τ ((mem_elemsT QA hQA τ).2 hτ)
  rw [Bool.or_eq_true] at h1
  rcases h1 with h2 | h2
  · exfalso
    have h3 : isOuterInv QP τ = true := (isOuterInv_iff QP hQP τ).2 ⟨hτ2, hτP⟩
    rw [h3] at h2
    exact absurd h2 (by decide)
  · obtain ⟨a, haC, h3⟩ := List.any_eq_true.1 h2
    obtain ⟨b, hbC, h4⟩ := List.any_eq_true.1 h3
    rw [List.mem_filter] at haC hbC
    rw [Bool.and_eq_true] at h4
    exact ⟨a, (mem_elemsT QP hQP a).1 haC.1, b, (mem_elemsT QP hQP b).1 hbC.1,
      of_decide_eq_true haC.2, of_decide_eq_true hbC.2, of_decide_eq_true h4.1,
      of_decide_eq_true h4.2⟩

end Checks

theorem l33_outerConj_ok :
    outerConjCheck L33.QP (elemsT L33.QA) = true :=
  Certificates.certificate5012.1

theorem l33_outerComm_ok :
    outerCommCheck L33.QP (elemsT L33.QA) (elemsT L33.QP) = true :=
  Certificates.certificate5012.2

theorem l33_outer_invs_conj
    {K : Type} [Group K] (hK : ShapeL33 K) (φ ψ : MulAut K)
    (hφ : φ ^ 2 = 1) (hψ : ψ ^ 2 = 1) (hφo : ¬ ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹)
    (hψo : ¬ ∃ k : K, ∀ x : K, ψ x = k * x * k⁻¹) : ∃ α : MulAut K, α * φ * α⁻¹ = ψ := by
  obtain ⟨e⟩ := L33.equiv_of_lieModel hK
  obtain ⟨M, hP, hA⟩ := L33.autModel e
  obtain ⟨τ0, -, -, -, hall⟩ := outerConjCheck_sound L33.QP L33.QA L33.QP_ok L33.QA_ok
    l33_outerConj_ok
  have hout : ∀ χ : MulAut K, χ ^ 2 = 1 → (¬ ∃ k : K, ∀ x : K, χ x = k * x * k⁻¹) →
      (M.ι χ ∈ L33.QA.originalSubgroup ∧ M.ι χ ^ 2 = 1 ∧ M.ι χ ∉ L33.QP.originalSubgroup) := by
    intro χ h2 ho
    refine ⟨hA.le (M.ι_mem χ), ?_, fun h => ho (M.inner_of_mem χ (hP.ge h))⟩
    rw [← map_pow, h2, map_one]
  obtain ⟨hφA, hφ2, hφP⟩ := hout φ hφ hφo
  obtain ⟨hψA, hψ2, hψP⟩ := hout ψ hψ hψo
  obtain ⟨σ₁, hσ₁, h₁⟩ := hall _ hφA hφ2 hφP
  obtain ⟨σ₂, hσ₂, h₂⟩ := hall _ hψA hψ2 hψP
  have hg : σ₂ * σ₁⁻¹ ∈ M.A := hA.ge (L33.QA.originalSubgroup.mul_mem hσ₂
    (L33.QA.originalSubgroup.inv_mem hσ₁))
  refine ⟨M.Φ.symm ⟨σ₂ * σ₁⁻¹, hg⟩, M.ι_injective ?_⟩
  have e1 : M.ι (M.Φ.symm ⟨σ₂ * σ₁⁻¹, hg⟩) = σ₂ * σ₁⁻¹ := by
    show ((M.Φ (M.Φ.symm ⟨σ₂ * σ₁⁻¹, hg⟩) : M.A) : Equiv.Perm (Fin 26)) = _
    rw [MulEquiv.apply_symm_apply]
  rw [map_mul, map_mul, map_inv, e1, ← h₂, ← h₁]
  group

theorem l33_outer_inv_commutator
    {K : Type} [Group K] (hK : ShapeL33 K) (φ : MulAut K)
    (hφ : φ ^ 2 = 1) (hφo : ¬ ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹) :
    ∃ a b : K, φ a = a ∧ φ b = b ∧ (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1 := by
  obtain ⟨e⟩ := L33.equiv_of_lieModel hK
  obtain ⟨M, hP, hA⟩ := L33.autModel e
  have hφ2 : M.ι φ ^ 2 = 1 := by rw [← map_pow, hφ, map_one]
  obtain ⟨a', ha', b', hb', hca, hcb, hsq, hne⟩ := outerCommCheck_sound L33.QP L33.QA L33.QP_ok
    L33.QA_ok l33_outerComm_ok (M.ι φ) (hA.le (M.ι_mem φ)) hφ2
    (fun h => hφo (M.inner_of_mem φ (hP.ge h)))
  have hfix : ∀ (c : Equiv.Perm (Fin 26)) (hc : c ∈ M.P), c * M.ι φ = M.ι φ * c →
      φ (M.e.symm ⟨c, hc⟩) = M.e.symm ⟨c, hc⟩ := by
    intro c hc hcomm
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec]
    change M.ι φ * (M.e (M.e.symm ⟨c, hc⟩) : Equiv.Perm (Fin 26)) * (M.ι φ)⁻¹ = _
    rw [MulEquiv.apply_symm_apply]
    change M.ι φ * c * (M.ι φ)⁻¹ = c
    rw [← hcomm]
    group
  have ha'P : a' ∈ M.P := hP.ge ha'
  have hb'P : b' ∈ M.P := hP.ge hb'
  refine ⟨M.e.symm ⟨a', ha'P⟩, M.e.symm ⟨b', hb'P⟩, hfix a' ha'P hca, hfix b' hb'P hcb, ?_, ?_⟩
  · apply M.e.injective
    apply Subtype.ext
    simpa [pow_two] using hsq
  · intro h
    apply hne
    have h1 := congrArg (fun y : K => ((M.e y : M.P) : Equiv.Perm (Fin 26))) h
    simpa using h1

end CFSG.GH74.E2
