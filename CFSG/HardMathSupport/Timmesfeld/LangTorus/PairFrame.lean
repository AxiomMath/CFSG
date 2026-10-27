module

public import CFSG.LieType.Chevalley.RootCommutatorCertificate
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.PairFrame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false


variable {τ : Tag}

theorem exists_pairTable_row_gen_of_tableCheck
    {τ : Tag} (hcheck : tableCheck τ = true)
    {r s : Fin τ.rank → ℤ} (hr : IsRoot τ r) (hs : IsRoot τ s)
    (hne : r ≠ s) (hne' : r ≠ -s) :
    ∃ row ∈ pairTable τ, ∃ w : WeylGroup τ,
      w • orbitCertRoot τ row.1 = r ∧ w • orbitCertRoot τ row.2.1 = s := by
  obtain ⟨x, hx, w, hw1, hw2⟩ := exists_smul_rep hr hs hne hne'
  have hBounds := lt_length_of_mem_repsOf hx
  have hTable :
      (pairTable τ).map (fun z => (z.1, z.2.1, z.2.2.2)) = (repsOf τ).map (convertRow τ) := by
    have h := hcheck
    simp only [tableCheck, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.1
  have hConv : convertRow τ x ∈ (pairTable τ).map (fun z => (z.1, z.2.1, z.2.2.2)) := by
    rw [hTable]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨row, hrow, hroweq⟩ := List.mem_map.mp hConv
  have ha := congrArg Prod.fst hroweq
  have hb := congrArg (fun t => t.2.1) hroweq
  refine ⟨row, hrow, w, ?_, ?_⟩
  · change row.1 = certWitnessPos τ x.1 at ha
    rw [ha, orbitCertRoot_certWitnessPos hBounds.1]
    exact hw1
  · change row.2.1 = certWitnessPos τ x.2.1 at hb
    rw [hb, orbitCertRoot_certWitnessPos hBounds.2]
    exact hw2

theorem exists_pairTable_row_gen {r s : Fin τ.rank → ℤ} (hr : IsRoot τ r) (hs : IsRoot τ s)
    (hne : r ≠ s) (hne' : r ≠ -s) :
    ∃ row ∈ pairTable τ, ∃ w : WeylGroup τ,
      w • orbitCertRoot τ row.1 = r ∧ w • orbitCertRoot τ row.2.1 = s :=
  exists_pairTable_row_gen_of_tableCheck (tableCheck_eq τ) hr hs hne hne'

@[expose] def PairInjective (τ : Tag) : Prop :=
  ∀ r₁ ∈ pairTable τ, ∀ r₂ ∈ pairTable τ,
    iform (orbitCertRoot τ r₁.1) (orbitCertRoot τ r₁.2.1) =
        iform (orbitCertRoot τ r₂.1) (orbitCertRoot τ r₂.2.1) →
      r₁.1 = r₂.1 ∧ r₁.2.1 = r₂.2.1

theorem exists_weyl_pair_iform_of_tableCheck
    {τ : Tag} (hcheck : tableCheck τ = true) (hinj : PairInjective τ)
    {r s r' s' : Fin τ.rank → ℤ}
    (hr : IsRoot τ r) (hs : IsRoot τ s) (hr' : IsRoot τ r') (hs' : IsRoot τ s')
    (hne : r ≠ s) (hne' : r ≠ -s) (hne2 : r' ≠ s') (hne2' : r' ≠ -s')
    (hip : iform r s = iform r' s') :
    ∃ w : WeylGroup τ, w • r = r' ∧ w • s = s' := by
  obtain ⟨row1, hrow1, w1, h1r, h1s⟩ := exists_pairTable_row_gen_of_tableCheck hcheck hr hs hne hne'
  obtain ⟨row2, hrow2, w2, h2r, h2s⟩ := exists_pairTable_row_gen_of_tableCheck hcheck hr' hs' hne2 hne2'
  have c1 := iform_smul w1 (orbitCertRoot τ row1.1) (orbitCertRoot τ row1.2.1)
  have c2 := iform_smul w2 (orbitCertRoot τ row2.1) (orbitCertRoot τ row2.2.1)
  rw [h1r, h1s] at c1
  rw [h2r, h2s] at c2
  obtain ⟨e1, e2⟩ := hinj row1 hrow1 row2 hrow2 (c1.symm.trans (hip.trans c2))
  refine ⟨w2 * w1⁻¹, ?_, ?_⟩
  · rw [mul_smul, ← h1r, inv_smul_smul, e1, h2r]
  · rw [mul_smul, ← h1s, inv_smul_smul, e2, h2s]

theorem exists_weyl_pair_iform (hinj : PairInjective τ) {r s r' s' : Fin τ.rank → ℤ}
    (hr : IsRoot τ r) (hs : IsRoot τ s) (hr' : IsRoot τ r') (hs' : IsRoot τ s')
    (hne : r ≠ s) (hne' : r ≠ -s) (hne₂ : r' ≠ s') (hne₂' : r' ≠ -s')
    (hip : iform r s = iform r' s') :
    ∃ w : WeylGroup τ, w • r = r' ∧ w • s = s' :=
  exists_weyl_pair_iform_of_tableCheck (tableCheck_eq τ) hinj
    hr hs hr' hs' hne hne' hne₂ hne₂' hip

theorem pairInjective_of_exceptional (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    PairInjective τ := by
  rcases hτ with rfl | rfl | rfl <;> unfold PairInjective <;> decide +kernel

theorem pairInjective_E6 : PairInjective .E6 :=
  pairInjective_of_exceptional (Or.inl rfl)

theorem pairInjective_E7 : PairInjective .E7 :=
  pairInjective_of_exceptional (Or.inr (Or.inl rfl))

theorem pairInjective_E8 : PairInjective .E8 :=
  pairInjective_of_exceptional (Or.inr (Or.inr rfl))

end CFSG.HardMathSupport.Timmesfeld.LangTorus.PairFrame
