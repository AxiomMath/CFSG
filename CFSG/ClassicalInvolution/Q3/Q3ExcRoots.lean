module

public import CFSG.LieType.HighestRoot.CentChevalley
public import CFSG.LieType.Chevalley.SignStabilizerDataE6
public import CFSG.LieType.Chevalley.SignStabilizerDataE7
public import CFSG.LieType.Chevalley.SignStabilizerDataE8
public import CFSG.LieType.Chevalley.SignStabilizerDataF4

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.HighestRoot

@[expose] def UniqIsolated (τ : Tag) (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) : Prop :=
  ∀ α β : Fin τ.rank → ℤ, α ∈ kernelRoots χ → β ∈ kernelRoots χ →
    (∀ γ ∈ kernelRoots χ, γ = α ∨ γ = -α ∨ iform α γ = 0) →
    (∀ γ ∈ kernelRoots χ, γ = β ∨ γ = -β ∨ iform β γ = 0) → β = α ∨ β = -α

theorem uniqIsolated_of_isCharConj {τ : Tag} {χ χ' : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    {t : WeylGroup τ} (ht : IsCharConj χ χ' t) (h : UniqIsolated τ χ) : UniqIsolated τ χ' := by
  intro α β hα hβ hiα hiβ
  have key : ∀ {α : Fin τ.rank → ℤ}, α ∈ kernelRoots χ' →
      (∀ γ ∈ kernelRoots χ', γ = α ∨ γ = -α ∨ iform α γ = 0) →
      t⁻¹ • α ∈ kernelRoots χ ∧
        ∀ γ ∈ kernelRoots χ, γ = t⁻¹ • α ∨ γ = -(t⁻¹ • α) ∨ iform (t⁻¹ • α) γ = 0 := by
    intro α hα hiso
    refine ⟨(kernelRoots_iff_of_isCharConj ht).1 hα, fun γ hγ => ?_⟩
    have hγ' : t • γ ∈ kernelRoots χ' := by
      rw [kernelRoots_iff_of_isCharConj ht, inv_smul_smul]
      exact hγ
    rcases hiso (t • γ) hγ' with h1 | h1 | h1
    · left
      rw [← h1, inv_smul_smul]
    · right
      left
      rw [← smul_neg, ← h1, inv_smul_smul]
    · right
      right
      rw [← iform_smul t, smul_inv_smul]
      exact h1
  obtain ⟨hα1, hα2⟩ := key hα hiα
  obtain ⟨hβ1, hβ2⟩ := key hβ hiβ
  rcases h _ _ hα1 hβ1 hα2 hβ2 with e | e
  · left
    calc β = t • (t⁻¹ • β) := (smul_inv_smul t β).symm
      _ = t • (t⁻¹ • α) := by rw [e]
      _ = α := smul_inv_smul t α
  · right
    calc β = t • (t⁻¹ • β) := (smul_inv_smul t β).symm
      _ = t • (-(t⁻¹ • α)) := by rw [e]
      _ = -α := by rw [smul_neg, smul_inv_smul]

theorem uniqIsolated_of_orbitCheck {τ : Tag} {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hO : OrbitCheck τ reps entries)
    (hrep : ∀ ρ < reps.length, UniqIsolated τ (maskChar (listMask (reps.getD ρ []))))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) : UniqIsolated τ χ := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck hO χ
  exact uniqIsolated_of_isCharConj ht (hrep ρ hρ)

@[expose] def rootVecs (τ : Tag) : List (Fin τ.rank → ℤ) :=
  τ.rootCertificate.roots.map decodeVec

@[expose] def evenPairing {τ : Tag} (m : Fin τ.rank → Bool) (v : Fin τ.rank → ℤ) : Bool :=
  decide (Even (maskPairing m v))

@[expose] def isolatedIn {τ : Tag} (K : List (Fin τ.rank → ℤ)) (v : Fin τ.rank → ℤ) : Bool :=
  K.all fun w => (List.ofFn w == List.ofFn v) || (List.ofFn w == List.ofFn (-v)) ||
    decide (iform v w = 0)

@[expose] def uniqIsolatedCheck (τ : Tag) (m : Fin τ.rank → Bool) : Bool :=
  let K := (rootVecs τ).filter (evenPairing m)
  K.all fun v => !(isolatedIn K v) ||
    K.all fun w => !(isolatedIn K w) || (List.ofFn w == List.ofFn v) ||
      (List.ofFn w == List.ofFn (-v))

theorem mem_rootVecs_iff {τ : Tag} {v : Fin τ.rank → ℤ} : v ∈ rootVecs τ ↔ IsRoot τ v := by
  rw [isRoot_iff_exists_mem_roots, rootVecs, List.mem_map]

theorem uniqIsolated_of_check {τ : Tag} {m : Fin τ.rank → Bool}
    (h : uniqIsolatedCheck τ m = true) : UniqIsolated τ (maskChar m) := by
  intro α β hα hβ hiα hiβ
  set K := (rootVecs τ).filter (evenPairing m) with hK
  have hmemK : ∀ {v : Fin τ.rank → ℤ}, v ∈ kernelRoots (maskChar m) ↔ v ∈ K := by
    intro v
    rw [mem_kernelRoots_maskChar, hK, List.mem_filter, mem_rootVecs_iff]
    simp only [evenPairing, decide_eq_true_eq]
  have hiso : ∀ {v : Fin τ.rank → ℤ}, v ∈ kernelRoots (maskChar m) →
      (∀ γ ∈ kernelRoots (maskChar m), γ = v ∨ γ = -v ∨ iform v γ = 0) →
      isolatedIn K v = true := by
    intro v hv hi
    simp only [isolatedIn, List.all_eq_true, Bool.or_eq_true, ofFn_beq_eq_true_iff,
      decide_eq_true_eq]
    intro w hw
    rcases hi w (hmemK.2 hw) with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1
  simp only [uniqIsolatedCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    ofFn_beq_eq_true_iff] at h
  have h1 := h α (hmemK.1 hα)
  rcases h1 with h1 | h1
  · rw [hiso hα hiα] at h1
    exact absurd h1 (by decide)
  · have h2 := h1 β (hmemK.1 hβ)
    rcases h2 with (h2 | h2) | h2
    · rw [hiso hβ hiβ] at h2
      exact absurd h2 (by decide)
    · exact Or.inl h2
    · exact Or.inr h2

theorem uniqIsolated_F4 (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* ℤˣ) :
    UniqIsolated .F4 χ := by
  have hc : ∀ ρ < f4SignReps.length,
      uniqIsolatedCheck .F4 (listMask (f4SignReps.getD ρ [])) = true := by decide +kernel
  exact uniqIsolated_of_orbitCheck f4SignOrbit_check
    (fun ρ hρ => uniqIsolated_of_check (hc ρ hρ)) χ

theorem uniqIsolated_E6 (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* ℤˣ) :
    UniqIsolated .E6 χ := by
  have hc : ∀ ρ < e6SignReps.length,
      uniqIsolatedCheck .E6 (listMask (e6SignReps.getD ρ [])) = true := by decide +kernel
  exact uniqIsolated_of_orbitCheck e6SignOrbit_check
    (fun ρ hρ => uniqIsolated_of_check (hc ρ hρ)) χ

theorem uniqIsolated_E7 (χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* ℤˣ) :
    UniqIsolated .E7 χ := by
  have hc : ∀ ρ < e7SignReps.length,
      uniqIsolatedCheck .E7 (listMask (e7SignReps.getD ρ [])) = true := by decide +kernel
  exact uniqIsolated_of_orbitCheck e7SignOrbit_check
    (fun ρ hρ => uniqIsolated_of_check (hc ρ hρ)) χ

theorem uniqIsolated_E8 (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* ℤˣ) :
    UniqIsolated .E8 χ := by
  have hc : ∀ ρ < e8SignReps.length,
      uniqIsolatedCheck .E8 (listMask (e8SignReps.getD ρ [])) = true := by decide +kernel
  exact uniqIsolated_of_orbitCheck e8SignOrbit_check
    (fun ρ hρ => uniqIsolated_of_check (hc ρ hρ)) χ


end CFSG.ClassicalInvolution.Q3
