module

public import CFSG.ClassicalInvolution.RouteD.MultiModelShort
public import CFSG.ClassicalInvolution.RouteD.MultiModelRoot

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.OddCT CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Generation

variable {n : ℕ} {K : Type} [Field K]

@[expose] def shortSetB (n : ℕ) : Set (Fin n → ℤ) :=
  {γ | ∃ (i : Fin n) (s : Bool), toStdB n γ = Pi.single i (boolSign s)}

theorem shortSetB_mem_roots {γ : Fin n → ℤ} (h : γ ∈ shortSetB n) :
    γ ∈ roots (isFiniteType_cartanB n) ∅ :=
  mem_rootsB_iff.mpr (Or.inr h)

theorem oddRootGroup_le_iSup_short (h2 : (2 : K) ≠ 0) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) :
    oddRootGroup n K γ ≤ ⨆ γ' ∈ shortSetB n, oddRootGroup n K γ' := by
  set T : Subgroup (spinGroup (quadOdd n K)) := ⨆ γ' ∈ shortSetB n, oddRootGroup n K γ' with hT
  have hshort : ∀ (i : Fin n) (s : Bool) (a : K),
      (oddFrame n K).shortRoot i s (Multiplicative.ofAdd a) ∈ T := by
    intro i s a
    have hmem : ofStdB n (Pi.single i (boolSign s)) ∈ shortSetB n :=
      ⟨i, s, toStdB_ofStdB n _⟩
    have hgr := oddRootGroup_eq_short (K := K) i s (toStdB_ofStdB n (Pi.single i (boolSign s)))
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hmem (by rw [hgr]; exact ⟨_, rfl⟩))
  rcases mem_rootsB_iff.mp hγ with ⟨i, j, hij, s, t, h⟩ | h
  · rw [oddRootGroup_eq_long hij s t h]
    rintro _ ⟨m, rfl⟩
    have hc := (oddFrame n K).commutator_shortRoot_shortRoot hij s t (-m.toAdd / 2) 1
    have e : (-2 * (-m.toAdd / 2) * 1 : K) = m.toAdd := by field_simp
    rw [e, ofAdd_toAdd] at hc
    rw [← hc, commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem (hshort i s _) (hshort j t _))
      (T.inv_mem (hshort i s _))) (T.inv_mem (hshort j t _))
  · exact le_iSup₂_of_le γ h le_rfl

theorem iSup_short_eq_top (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    (⨆ γ ∈ shortSetB n, oddRootGroup n K γ) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← oddDatum_iSup_eq_top n K h2 hn]
  exact iSup₂_le fun γ hγ => oddRootGroup_le_iSup_short h2 hγ

end Generation

section Criterion

theorem coroot_B4_zero : ∀ (i : Fin 4) (s : Bool), 2 ≤ i.val →
    coroot (cartanB 4) 0 (ofStdB 4 (Pi.single i (boolSign s))) = 0 := by
  intro i s hi
  rw [coroot_apply]
  fin_cases i <;> cases s <;> simp_all [Fin.sum_univ_four, cartanB, ofStdB, boolSign, Pi.single_apply]

theorem coroot_B4_two : ∀ (i : Fin 4) (s : Bool), i.val ≤ 1 →
    coroot (cartanB 4) 2 (ofStdB 4 (Pi.single i (boolSign s))) = 0 := by
  intro i s hi
  rw [coroot_apply]
  fin_cases i <;> cases s <;> simp_all [Fin.sum_univ_four, cartanB, ofStdB, boolSign, Pi.single_apply]

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_pOmegaOdd_four {e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaOdd 4 p e) :
    CommFamilyConnected (ModelFund p .POmegaOdd 4 e) := by
  refine commFamilyConnected_modelFund_of_short hp2 trivial hadm (by decide) (by decide) ?_
  have hlong0 := ModelFacts.isLongestRoot_single .POmegaOdd 4 p e Fact.out trivial hadm
    ⟨0, (by decide : 0 < 4)⟩ (by show 0 + 1 < 4; omega)
  have hlong2 := ModelFacts.isLongestRoot_single .POmegaOdd 4 p e Fact.out trivial hadm
    ⟨2, (by decide : 2 < 4)⟩ (by show 2 + 1 < 4; omega)
  refine ⟨Pi.single ⟨0, (by decide : 0 < 4)⟩ 1, shortSetB 4, hlong0,
    fun γ hγ => shortSetB_mem_roots hγ,
    iSup_short_eq_top (n := 4) (ModelFacts.two_ne_zero_galoisField e hp2) (by omega),
    fun γ hγ => ?_⟩
  obtain ⟨i, s, hi⟩ := hγ
  have hγeq : γ = ofStdB 4 (Pi.single i (boolSign s)) :=
    (toStdB_eq_iff 4 γ (Pi.single i (boolSign s))).mp hi
  subst hγeq
  by_cases hi2 : 2 ≤ i.val
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [form_comm]
    exact form_toRat_single_eq_zero _ ⟨0, (by decide : 0 < 4)⟩ _ (coroot_B4_zero i s hi2)
  · refine Or.inr (Or.inr (Or.inr ⟨Pi.single ⟨2, (by decide : 2 < 4)⟩ 1, hlong2, ?_, ?_⟩))
    · exact form_single_eq_zero_of_cartan _ (by
        show cartanB 4 ⟨0, (by decide : 0 < 4)⟩ ⟨2, (by decide : 2 < 4)⟩ = 0
        decide)
    · rw [form_comm]
      exact form_toRat_single_eq_zero _ ⟨2, (by decide : 2 < 4)⟩ _ (coroot_B4_two i s (by omega))

end Criterion

end CFSG.ClassicalInvolution.RouteD
