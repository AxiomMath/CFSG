module

public import CFSG.ClassicalInvolution.RouteD.MultiModelShortB

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.OddCT CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Generation

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem minusRootGroup_le_iSup_short (h2 : (2 : K) ≠ 0) {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) :
    minusRootGroup n hirr γ ≤ ⨆ γ' ∈ shortSetB (n - 1), minusRootGroup n hirr γ' := by
  set T : Subgroup (spinGroup (quadMinus n K b c)) :=
    ⨆ γ' ∈ shortSetB (n - 1), minusRootGroup n hirr γ' with hT
  have hshort : ∀ (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K),
      twShortRoot n hirr i s (Multiplicative.ofAdd p) ∈ T := by
    intro i s p
    have hmem : ofStdB (n - 1) (Pi.single i (boolSign s)) ∈ shortSetB (n - 1) :=
      ⟨i, s, toStdB_ofStdB (n - 1) _⟩
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hmem
      (twShortRoot_mem_minusRootGroup n hirr i s (toStdB_ofStdB (n - 1) _) p))
  rcases mem_rootsB_iff.mp hγ with ⟨i, j, hij, s, t, h⟩ | h
  · rw [minusRootGroup_eq_long n hirr hij s t h]
    rintro _ ⟨m, rfl⟩
    have hc := commutator_twShortRoot_twShortRoot n hirr hij s t
      (![-m.toAdd / 2, 0] : Fin 2 → K) planeOne
    have e : (-polarPlane b c (![-m.toAdd / 2, 0] : Fin 2 → K) planeOne : K) = m.toAdd := by
      simp only [polarPlane, planeOne, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one,
        add_zero]
      field_simp
    rw [e, ofAdd_toAdd] at hc
    rw [← hc, commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem (hshort i s _) (hshort j t _))
      (T.inv_mem (hshort i s _))) (T.inv_mem (hshort j t _))
  · exact le_iSup₂_of_le γ h le_rfl

theorem iSup_short_eq_top_minus [Finite K] (h2 : (2 : K) ≠ 0) (hn : 4 ≤ n) :
    (⨆ γ ∈ shortSetB (n - 1), minusRootGroup n hirr γ) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← minusDatum_iSup_eq_top n hirr hn]
  exact iSup₂_le fun γ hγ => minusRootGroup_le_iSup_short hirr h2 hγ

end Generation

section Criterion

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_pOmegaMinus_five {e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus 5 p e) :
    CommFamilyConnected (ModelFund p .POmegaMinus 5 e) := by
  refine commFamilyConnected_modelFund_of_short hp2 trivial hadm (by decide) (by decide) ?_
  have hlong0 := ModelFacts.isLongestRoot_single .POmegaMinus 5 p e Fact.out trivial hadm
    ⟨0, (by decide : 0 < 5 - 1)⟩ (by show 0 + 2 < 5; omega)
  have hlong2 := ModelFacts.isLongestRoot_single .POmegaMinus 5 p e Fact.out trivial hadm
    ⟨2, (by decide : 2 < 5 - 1)⟩ (by show 2 + 2 < 5; omega)
  refine ⟨Pi.single ⟨0, (by decide : 0 < 5 - 1)⟩ 1, shortSetB (5 - 1), hlong0,
    fun γ hγ => shortSetB_mem_roots hγ,
    iSup_short_eq_top_minus (n := 5) (minusCoeffs_irr p e)
      (ModelFacts.two_ne_zero_galoisField e hp2) (by omega),
    fun γ hγ => ?_⟩
  obtain ⟨i, s, hi⟩ := hγ
  have hγeq : γ = ofStdB (5 - 1) (Pi.single i (boolSign s)) :=
    (toStdB_eq_iff (5 - 1) γ (Pi.single i (boolSign s))).mp hi
  subst hγeq
  by_cases hi2 : 2 ≤ i.val
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [form_comm]
    exact form_toRat_single_eq_zero _ ⟨0, (by decide : 0 < 5 - 1)⟩ _ (coroot_B4_zero i s hi2)
  · refine Or.inr (Or.inr (Or.inr ⟨Pi.single ⟨2, (by decide : 2 < 5 - 1)⟩ 1, hlong2, ?_, ?_⟩))
    · exact form_single_eq_zero_of_cartan _ (by
        show cartanB (5 - 1) ⟨0, (by decide : 0 < 5 - 1)⟩ ⟨2, (by decide : 2 < 5 - 1)⟩ = 0
        decide)
    · rw [form_comm]
      exact form_toRat_single_eq_zero _ ⟨2, (by decide : 2 < 5 - 1)⟩ _
        (coroot_B4_two i s (by omega))

end Criterion

end CFSG.ClassicalInvolution.RouteD
