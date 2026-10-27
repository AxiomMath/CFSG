module

public import CFSG.ClassicalInvolution.RouteD.MultiModelShort
public import CFSG.ClassicalInvolution.RouteD.MultiModelRoot

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Form

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem symmetrizer_rel (i j : I) :
    symmetrizer hA i * (A i j : ℚ) = symmetrizer hA j * (A j i : ℚ) := by
  have h := form_comm hA (Pi.single i 1) (Pi.single j 1)
  rw [form_single_left, form_single_left] at h
  simpa [Pi.single_apply] using h

end Form

@[expose] def bF4 (θ δ : Fin 4 → ℤ) : ℤ :=
  4 * θ 0 * δ 0 - 2 * θ 0 * δ 1 - 2 * θ 1 * δ 0 + 4 * θ 1 * δ 1 - 2 * θ 1 * δ 2 -
    2 * θ 2 * δ 1 + 2 * θ 2 * δ 2 - θ 2 * δ 3 - θ 3 * δ 2 + 2 * θ 3 * δ 3

theorem form_F4_explicit {A : Matrix (Fin 4) (Fin 4) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAe : A = !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]) (θ δ : Fin 4 → ℤ) :
    form hA (toRat θ) (toRat δ) = symmetrizer hA 3 * ((bF4 θ δ : ℤ) : ℚ) := by
  have r01 := symmetrizer_rel hA 0 1
  have r12 := symmetrizer_rel hA 1 2
  have r23 := symmetrizer_rel hA 2 3
  subst hAe
  simp at r01 r12 r23
  rw [form_eq_sum]
  simp only [form_single_right, Fin.sum_univ_four, toRat_apply, bF4]
  simp
  rw [r01, r12, r23]
  ring

theorem form_F4_eq_zero {A : Matrix (Fin 4) (Fin 4) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAe : A = !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]) {θ δ : Fin 4 → ℤ}
    (h : bF4 θ δ = 0) : form hA (toRat θ) (toRat δ) = 0 := by
  rw [form_F4_explicit hA hAe, h]
  simp

theorem lenSq_F4 {A : Matrix (Fin 4) (Fin 4) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAe : A = !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]) (θ : Fin 4 → ℤ) :
    ModelFacts.lenSq hA θ = symmetrizer hA 3 * ((bF4 θ θ : ℤ) : ℚ) :=
  form_F4_explicit hA hAe θ θ

theorem notRoot_F4_of_false {v : Fin 4 → ℤ} (h : RootOps.isRootB .F4 v = false) :
    ¬ IsRoot .F4 v := fun hr => by
  have := RootOps.isRootB_iff.2 hr
  rw [h] at this
  exact Bool.noConfusion this

section Generation

variable {K : Type} [Field K]

theorem xPar_mem_of_commutator (h2 : (2 : K) ≠ 0) {β γ : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hγ : IsRoot .F4 γ) (hne : β ≠ γ) (hne' : β ≠ -γ) (hne'' : γ ≠ -β)
    (hsum : IsRoot .F4 (β + γ)) (h12 : ¬ IsRoot .F4 (β + 2 • γ)) (h21 : ¬ IsRoot .F4 (2 • β + γ))
    (T : Subgroup ↥(adjointGroup .F4 K))
    (hβT : ∀ c : K, xPar (rootOperatorFamily .F4) β c ∈ T)
    (hγT : ∀ c : K, xPar (rootOperatorFamily .F4) γ c ∈ T) (t : K) :
    xPar (rootOperatorFamily .F4) (β + γ) t ∈ T := by
  have hc := fun c d : K =>
    commutator_xPar (K := K) (F := rootOperatorFamily .F4) f4Data_valid noG2_F4 hβ hγ hne hne' c d
  have hC := natAbs_coeff11 (rootOperatorFamily .F4) f4Data_valid (α := ⟨β, hβ⟩) (β := ⟨γ, hγ⟩)
    hne'' hsum
  set C : ℤ := RootOperatorFamily'.coeff11 (rootOperatorFamily .F4) f4Data_valid ⟨β, hβ⟩ ⟨γ, hγ⟩
    with hCdef
  have hCK : (C : K) ≠ 0 := by
    rcases hC with h | h
    · rcases Int.natAbs_eq_iff.mp h with h1 | h1 <;> rw [h1] <;> simp
    · rcases Int.natAbs_eq_iff.mp h with h1 | h1 <;> rw [h1] <;> simpa using h2
  have := hc (t / C) 1
  rw [xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one] at this
  have e : (C : K) * (t / C) * 1 = t := by field_simp
  rw [e] at this
  rw [← this, commutatorElement_def]
  exact T.mul_mem (T.mul_mem (T.mul_mem (hβT _) (hγT _)) (T.inv_mem (hβT _))) (T.inv_mem (hγT _))

@[expose] def shortF4 : Fin 8 → Fin 4 → ℤ :=
  ![![1, 1, 1, 0], ![-1, -1, -1, 0], ![0, 1, 1, 0], ![0, -1, -1, 0], ![0, 0, 1, 0],
    ![0, 0, -1, 0], ![0, 0, 0, 1], ![0, 0, 0, -1]]

@[expose] def shortSetF4 : Set (Fin 4 → ℤ) := Set.range shortF4

theorem isRoot_shortF4 (k : Fin 8) : IsRoot .F4 (shortF4 k) :=
  RootOps.isRootB_iff.1 (by revert k; decide)

theorem isRoot_of_mem_shortSetF4 {γ : Fin 4 → ℤ} (h : γ ∈ shortSetF4) : IsRoot .F4 γ := by
  obtain ⟨k, rfl⟩ := h
  exact isRoot_shortF4 k

theorem iSup_shortSetF4_eq_top (h2 : (2 : K) ≠ 0) :
    (⨆ γ ∈ shortSetF4, (f4Datum K).rootGroup γ) = ⊤ := by
  set T : Subgroup ↥(adjointGroup .F4 K) := ⨆ γ ∈ shortSetF4, (f4Datum K).rootGroup γ with hT
  have hmem : ∀ γ ∈ shortSetF4, ∀ c : K, xPar (rootOperatorFamily .F4) γ c ∈ T := fun γ hγ c =>
    Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ
      (xPar_mem (isRoot_of_mem_shortSetF4 hγ) c))
  have hgen : ∀ γ ∈ shortSetF4, (f4Datum K).rootGroup γ ≤ T := fun γ hγ =>
    le_iSup₂_of_le γ hγ le_rfl
  have hrk : ∀ (v : Fin (Tag.rank .F4) → ℤ), IsRoot .F4 v → (∀ t : K, xPar (rootOperatorFamily .F4) v t ∈ T) →
      (f4Datum K).rootGroup v ≤ T := by
    intro v hv hT' x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hv x).mp hx
    exact hT' c
  have step : ∀ β γ : Fin (Tag.rank .F4) → ℤ, β ∈ shortSetF4 → γ ∈ shortSetF4 → β ≠ γ → β ≠ -γ → γ ≠ -β →
      IsRoot .F4 (β + γ) → ¬ IsRoot .F4 (β + 2 • γ) → ¬ IsRoot .F4 (2 • β + γ) →
      (f4Datum K).rootGroup (β + γ) ≤ T := by
    intro β γ hβ hγ hne hne' hne'' hsum h12 h21
    exact hrk _ hsum fun t => xPar_mem_of_commutator h2 (isRoot_of_mem_shortSetF4 hβ)
      (isRoot_of_mem_shortSetF4 hγ) hne hne' hne'' hsum h12 h21 T (hmem β hβ) (hmem γ hγ) t
  have m : ∀ k, shortF4 k ∈ shortSetF4 := fun k => ⟨k, rfl⟩
  have h0p : (f4Datum K).rootGroup (Pi.single (0 : Fin 4) 1) ≤ T := by
    have e : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 0 + shortF4 3 := by
      ext j; fin_cases j <;> simp [shortF4]
    exact (congrArg (f4Datum K).rootGroup e).le.trans (step _ _ (m 0) (m 3)
      (show shortF4 0 ≠ shortF4 3 by decide) (show shortF4 0 ≠ -shortF4 3 by decide)
      (show shortF4 3 ≠ -shortF4 0 by decide) (RootOps.isRootB_iff.1 (by decide))
      (notRoot_F4_of_false (by decide)) (notRoot_F4_of_false (by decide)))
  have h0n : (f4Datum K).rootGroup (-Pi.single (0 : Fin 4) 1) ≤ T := by
    have e : (-Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 1 + shortF4 2 := by
      ext j; fin_cases j <;> simp [shortF4]
    exact (congrArg (f4Datum K).rootGroup e).le.trans (step _ _ (m 1) (m 2)
      (show shortF4 1 ≠ shortF4 2 by decide) (show shortF4 1 ≠ -shortF4 2 by decide)
      (show shortF4 2 ≠ -shortF4 1 by decide) (RootOps.isRootB_iff.1 (by decide))
      (notRoot_F4_of_false (by decide)) (notRoot_F4_of_false (by decide)))
  have h1p : (f4Datum K).rootGroup (Pi.single (1 : Fin 4) 1) ≤ T := by
    have e : (Pi.single (1 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 2 + shortF4 5 := by
      ext j; fin_cases j <;> simp [shortF4]
    exact (congrArg (f4Datum K).rootGroup e).le.trans (step _ _ (m 2) (m 5)
      (show shortF4 2 ≠ shortF4 5 by decide) (show shortF4 2 ≠ -shortF4 5 by decide)
      (show shortF4 5 ≠ -shortF4 2 by decide) (RootOps.isRootB_iff.1 (by decide))
      (notRoot_F4_of_false (by decide)) (notRoot_F4_of_false (by decide)))
  have h1n : (f4Datum K).rootGroup (-Pi.single (1 : Fin 4) 1) ≤ T := by
    have e : (-Pi.single (1 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 3 + shortF4 4 := by
      ext j; fin_cases j <;> simp [shortF4]
    exact (congrArg (f4Datum K).rootGroup e).le.trans (step _ _ (m 3) (m 4)
      (show shortF4 3 ≠ shortF4 4 by decide) (show shortF4 3 ≠ -shortF4 4 by decide)
      (show shortF4 4 ≠ -shortF4 3 by decide) (RootOps.isRootB_iff.1 (by decide))
      (notRoot_F4_of_false (by decide)) (notRoot_F4_of_false (by decide)))
  have h2p : (f4Datum K).rootGroup (Pi.single (2 : Fin 4) 1) ≤ T := by
    have e : (Pi.single (2 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 4 := by
      ext j; fin_cases j <;> simp [shortF4]
    exact (congrArg (f4Datum K).rootGroup e).le.trans (hgen _ (m 4))
  have h2n : (f4Datum K).rootGroup (-Pi.single (2 : Fin 4) 1) ≤ T := by
    have e : (-Pi.single (2 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 5 := by
      ext j; fin_cases j <;> simp [shortF4]
    exact (congrArg (f4Datum K).rootGroup e).le.trans (hgen _ (m 5))
  have h3p : (f4Datum K).rootGroup (Pi.single (3 : Fin 4) 1) ≤ T := by
    have e : (Pi.single (3 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 6 := by
      ext j; fin_cases j <;> simp [shortF4]
    exact (congrArg (f4Datum K).rootGroup e).le.trans (hgen _ (m 6))
  have h3n : (f4Datum K).rootGroup (-Pi.single (3 : Fin 4) 1) ≤ T := by
    have e : (-Pi.single (3 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 7 := by
      ext j; fin_cases j <;> simp [shortF4]
    exact (congrArg (f4Datum K).rootGroup e).le.trans (hgen _ (m 7))
  have hct := f4_isCTGroupDatum K
  refine eq_top_iff.mpr ?_
  rw [← iSup_rankOne_eq_top hct]
  refine iSup_le fun i => sup_le ?_ ?_
  · fin_cases i
    · exact h0p
    · exact h1p
    · exact h2p
    · exact h3p
  · fin_cases i
    · exact h0n
    · exact h1n
    · exact h2n
    · exact h3n

end Generation

section Criterion

theorem bF4_alpha_eps : bF4 (Pi.single (0 : Fin 4) 1) ![1, 2, 2, 2] = 0 := by decide

theorem bF4_alpha_short (k : Fin 8) (hk : 4 ≤ k.val) :
    bF4 (Pi.single (0 : Fin 4) 1) (shortF4 k) = 0 := by
  revert k; decide

theorem bF4_eps_short (k : Fin 8) (hk : k.val < 4) : bF4 ![1, 2, 2, 2] (shortF4 k) = 0 := by
  revert k; decide

theorem bF4_eps_eps :
    bF4 ![1, 2, 2, 2] ![1, 2, 2, 2] = bF4 (Pi.single (0 : Fin 4) 1) (Pi.single (0 : Fin 4) 1) := by
  decide

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_F4 {e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .F4 0 p e) :
    CommFamilyConnected (ModelFund p .F4 0 e) := by
  refine commFamilyConnected_modelFund_of_short hp2 trivial hadm (by decide) (by decide) ?_
  have hlong := ModelFacts.isLongestRoot_single .F4 0 p e Fact.out trivial hadm
    ⟨0, (by decide : 0 < 4)⟩ (by show 0 < 2; omega)
  have hεroot : IsRoot .F4 (![1, 2, 2, 2] : Fin (Tag.rank .F4) → ℤ) :=
    RootOps.isRootB_iff.1 (by decide)
  have hlongε : ModelFacts.IsLongestRoot (modelUniv .F4 0 p e Fact.out).D
      (![1, 2, 2, 2] : Fin (Tag.rank .F4) → ℤ) := by
    refine ⟨mem_adjDatum_roots.2 hεroot, fun ε' hε' => ?_⟩
    have h1 := hlong.2 ε' hε'
    have e1 : ModelFacts.lenSq (modelUniv .F4 0 p e Fact.out).D.isFiniteType
        (![1, 2, 2, 2] : Fin 4 → ℤ) =
        ModelFacts.lenSq (modelUniv .F4 0 p e Fact.out).D.isFiniteType
          (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) := by
      refine (lenSq_F4 _ rfl _).trans ?_
      refine Eq.trans ?_ (lenSq_F4 _ rfl _).symm
      rw [bF4_eps_eps]
    exact h1.trans_eq e1.symm
  refine ⟨Pi.single ⟨0, (by decide : 0 < 4)⟩ 1, shortSetF4, hlong,
    fun γ hγ => mem_adjDatum_roots.2 (isRoot_of_mem_shortSetF4 hγ),
    iSup_shortSetF4_eq_top (ModelFacts.two_ne_zero_galoisField e hp2), fun γ hγ => ?_⟩
  obtain ⟨k, rfl⟩ := hγ
  by_cases hk : k.val < 4
  · exact Or.inr (Or.inr (Or.inr ⟨![1, 2, 2, 2], hlongε,
      form_F4_eq_zero _ rfl bF4_alpha_eps, form_F4_eq_zero _ rfl (bF4_eps_short k hk)⟩))
  · exact Or.inr (Or.inr (Or.inl (form_F4_eq_zero _ rfl (bF4_alpha_short k (by omega)))))

end Criterion

end CFSG.ClassicalInvolution.RouteD
