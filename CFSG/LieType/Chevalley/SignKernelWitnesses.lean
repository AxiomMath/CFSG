module

public import CFSG.LieType.Chevalley.SignKernelWitnessDataG2
public import CFSG.LieType.Chevalley.SignKernelWitnessDataF4
public import CFSG.LieType.Chevalley.SignKernelWitnessDataD4
public import CFSG.LieType.Chevalley.SignKernelWitnessDataE6
public import CFSG.LieType.Chevalley.SignKernelWitnessDataE7
public import CFSG.LieType.Chevalley.SignKernelWitnessDataE8
public import CFSG.LieType.Chevalley.SignStabilizerDataE8

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag}

theorem eq_or_eq_neg_of_isolated
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ)
    (hiso : ∀ γ ∈ kernelRoots χ, γ = α ∨ γ = -α ∨ iform α γ = 0) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) (h : (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) = ⟦⟨α, hα⟩⟧) :
    γ = α ∨ γ = -α := by
  have key : ∀ x y : kernelRoots χ, Relation.EqvGen (fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
      (((x : Fin τ.rank → ℤ) = α ∨ (x : Fin τ.rank → ℤ) = -α) ↔
        ((y : Fin τ.rank → ℤ) = α ∨ (y : Fin τ.rank → ℤ) = -α)) := by
    have hmeet : ∀ x : kernelRoots χ, ((x : Fin τ.rank → ℤ) = α ∨ (x : Fin τ.rank → ℤ) = -α) →
        ∀ y : kernelRoots χ, iform (x : Fin τ.rank → ℤ) y ≠ 0 →
          (y : Fin τ.rank → ℤ) = α ∨ (y : Fin τ.rank → ℤ) = -α := by
      intro x hx y hxy
      have hαy : iform α y ≠ 0 := by
        rcases hx with e | e
        · rwa [e] at hxy
        · rw [e, ← neg_one_smul ℤ α, iform_smul_left] at hxy
          intro h0
          exact hxy (by rw [h0, mul_zero])
      rcases hiso y y.2 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd h1 hαy
    intro x y hxy
    induction hxy with
    | rel x y hr =>
      rw [dotProduct_mulVec_eq_iform] at hr
      exact ⟨fun hx => hmeet x hx y hr, fun hy => hmeet y hy x (by rwa [iform_comm])⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key ⟨α, hα⟩ ⟨γ, hγ⟩ (Quotient.exact h.symm)).1 (Or.inl rfl)

theorem nonrankone_witnesses_of_certs
    {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hO : OrbitCheck τ reps entries)
    (hW : ∀ ρ < reps.length, ∀ α : Fin τ.rank → ℤ,
      α ∈ kernelRoots (maskChar (listMask (reps.getD ρ []))) →
        KernelRootWitness (maskChar (listMask (reps.getD ρ []))) α)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ)
    (hi : 2 < (componentRoots χ i).ncard) {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) :
    (∃ β ∈ componentRoots χ i, ∃ n : ℤ, Odd n ∧
      n * (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ β)) = 2 * (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ α))) ∨
    (τ = .F4 ∧ ∃ w : WeylGroup τ, w • f4Rho ∈ componentRoots χ i ∧
      w • f4Sigma ∈ componentRoots χ i ∧ α = w • (f4Rho + f4Sigma)) := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck hO χ
  obtain ⟨hαk, hαi⟩ := hα
  have hα' := (kernelRoots_iff_of_isCharConj ht).1 hαk
  have hmk : ∀ {β : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots χ), iform β α ≠ 0 →
      β ∈ componentRoots χ i := fun hβ h =>
    ⟨hβ, (mk_eq_of_iform_ne_zero (α := ⟨_, hβ⟩) (β := ⟨α, hαk⟩) h).trans hαi⟩
  have hk : ∀ {β : Fin τ.rank → ℤ},
      β ∈ kernelRoots (maskChar (listMask (reps.getD ρ []))) → t • β ∈ kernelRoots χ :=
    fun hβ => (kernelRoots_iff_of_isCharConj ht).2 (by rwa [inv_smul_smul])
  rcases hW ρ hρ _ hα' with hiso | ⟨β', hβ', n, hn, hodd⟩ | ⟨hF4, w', h1, h2, h3, h4, h5⟩
  ·
    exfalso
    have hsub : componentRoots χ i ⊆ {α, -α} := by
      rintro γ ⟨hγk, hγi⟩
      have hγ' := (kernelRoots_iff_of_isCharConj ht).1 hγk
      have hcls := (mk_eq_mk_iff_of_isCharConj ht hγk hαk).1 (hγi.trans hαi.symm)
      rcases eq_or_eq_neg_of_isolated hα' hiso hγ' hcls with e | e
      · left
        rw [← smul_inv_smul t γ, e, smul_inv_smul]
      · right
        rw [← smul_inv_smul t γ, e, smul_neg, smul_inv_smul]
        exact Set.mem_singleton _
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard ≤ 2 := by
      have := Set.ncard_insert_le α ({-α} : Set (Fin τ.rank → ℤ))
      rw [Set.ncard_singleton] at this
      exact this
    omega
  ·
    left
    have hββ : iform (t • β') (t • β') = iform β' β' := iform_smul t β' β'
    have hβα : iform (t • β') α = iform β' (t⁻¹ • α) := by
      rw [← iform_smul t β' (t⁻¹ • α), smul_inv_smul]
    have hne : iform (t • β') α ≠ 0 := by
      rw [hβα]
      intro h0
      rw [h0, mul_zero] at hodd
      have := iform_self_pos_of_isRoot hβ'.1
      have hn0 : n ≠ 0 := by
        have := Int.odd_iff.1 hn
        omega
      rcases mul_eq_zero.1 hodd with h | h
      · exact hn0 h
      · omega
    refine ⟨t • β', hmk (hk hβ') hne, n, hn, ?_⟩
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, hββ, hβα]
    exact hodd
  ·
    right
    have hα'' : α = t • (w' • f4Rho + w' • f4Sigma) := by rw [← h3, smul_inv_smul]
    refine ⟨hF4, t * w', ?_, ?_, ?_⟩
    · rw [mul_smul]
      refine hmk (hk h1) ?_
      rw [hα'', ← h3, iform_smul]
      exact h4
    · rw [mul_smul]
      refine hmk (hk h2) ?_
      rw [hα'', ← h3, iform_smul]
      exact h5
    · simp only [hα'', mul_smul, smul_add]

theorem sign_kernel_nonrankone_root_commutator_witnesses
    (τ : Tag)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ)
    (hi : 2 < (componentRoots χ i).ncard) {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) :
    (∃ β ∈ componentRoots χ i, ∃ n : ℤ, Odd n ∧
      n * (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ β)) = 2 * (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ α))) ∨
    (τ = .F4 ∧ ∃ w : WeylGroup τ, w • f4Rho ∈ componentRoots χ i ∧
      w • f4Sigma ∈ componentRoots χ i ∧ α = w • (f4Rho + f4Sigma)) := by
  cases τ
  · exact nonrankone_witnesses_of_certs g2SignOrbit_check kernelRootWitness_G2 χ i hi hα
  · exact nonrankone_witnesses_of_certs f4SignOrbit_check kernelRootWitness_F4 χ i hi hα
  · exact nonrankone_witnesses_of_certs d4SignOrbit_check kernelRootWitness_D4 χ i hi hα
  · exact nonrankone_witnesses_of_certs e6SignOrbit_check kernelRootWitness_E6 χ i hi hα
  · exact nonrankone_witnesses_of_certs e7SignOrbit_check kernelRootWitness_E7 χ i hi hα
  · exact nonrankone_witnesses_of_certs e8SignOrbit_check kernelRootWitness_E8 χ i hi hα

end CFSG.LieType.Chevalley
