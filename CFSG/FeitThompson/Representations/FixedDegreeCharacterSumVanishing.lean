module

public import CFSG.FeitThompson.Representations.LinearCharactersSeparateElements
public import CFSG.FeitThompson.Representations.TensorAndDualCharacters
public import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {H : Type*} [Group H] {d : ℕ}

def irrDeg (H : Type*) [Group H] (d : ℕ) : Set (H → ℂ) := {χ ∈ Irr H | χ 1 = (d : ℂ)}

theorem mem_irrDeg {χ : H → ℂ} : χ ∈ irrDeg H d ↔ χ ∈ Irr H ∧ χ 1 = (d : ℂ) := Iff.rfl

theorem irrDeg_subset_Irr : irrDeg H d ⊆ Irr H := fun _ h => h.1

theorem finite_irrDeg [Finite H] : (irrDeg H d).Finite :=
  Set.Finite.subset finite_Irr irrDeg_subset_Irr

noncomputable def irrDegFinset (H : Type*) [Group H] [Finite H] (d : ℕ) : Finset (H → ℂ) :=
  (finite_irrDeg (H := H) (d := d)).toFinset

@[simp]
theorem mem_irrDegFinset [Finite H] {χ : H → ℂ} : χ ∈ irrDegFinset H d ↔ χ ∈ irrDeg H d :=
  Set.Finite.mem_toFinset _

@[simp]
theorem coe_irrDegFinset [Finite H] : (irrDegFinset H d : Set (H → ℂ)) = irrDeg H d :=
  Set.Finite.coe_toFinset _

theorem irrDegFinset_eq_filter [Finite H] [DecidableEq ℂ] :
    irrDegFinset H d = (irrFinset H).filter fun χ => χ 1 = (d : ℂ) := by
  ext χ
  simp [mem_irrDegFinset, irrDeg, mem_irrFinset]

theorem one_mem_irrDeg_one : (1 : H → ℂ) ∈ irrDeg H 1 := ⟨one_mem_Irr, by norm_num⟩

theorem one_notMem_irrDeg (hd : d ≠ 1) : (1 : H → ℂ) ∉ irrDeg H d := fun h => by
  have h2 : (1 : ℂ) = (d : ℂ) := h.2
  exact hd (by exact_mod_cast h2.symm)

def nonprincipalIrrDeg (H : Type*) [Group H] (d : ℕ) : Set (H → ℂ) := {χ ∈ irrDeg H d | χ ≠ 1}

theorem mem_nonprincipalIrrDeg {χ : H → ℂ} :
    χ ∈ nonprincipalIrrDeg H d ↔ χ ∈ Irr H ∧ χ ≠ 1 ∧ χ 1 = (d : ℂ) :=
  ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

theorem nonprincipalIrrDeg_subset_irrDeg : nonprincipalIrrDeg H d ⊆ irrDeg H d := fun _ h => h.1

theorem finite_nonprincipalIrrDeg [Finite H] : (nonprincipalIrrDeg H d).Finite :=
  finite_irrDeg.subset nonprincipalIrrDeg_subset_irrDeg

noncomputable def nonprincipalIrrDegFinset (H : Type*) [Group H] [Finite H] (d : ℕ) :
    Finset (H → ℂ) := (finite_nonprincipalIrrDeg (H := H) (d := d)).toFinset

@[simp]
theorem mem_nonprincipalIrrDegFinset [Finite H] {χ : H → ℂ} :
    χ ∈ nonprincipalIrrDegFinset H d ↔ χ ∈ nonprincipalIrrDeg H d :=
  Set.Finite.mem_toFinset _

@[simp]
theorem coe_nonprincipalIrrDegFinset [Finite H] :
    (nonprincipalIrrDegFinset H d : Set (H → ℂ)) = nonprincipalIrrDeg H d :=
  Set.Finite.coe_toFinset _

noncomputable def irrDegSum (H : Type*) [Group H] [Finite H] (d : ℕ) : H → ℂ :=
  ∑ χ ∈ irrDegFinset H d, χ

theorem irrDegSum_apply [Finite H] (h : H) :
    irrDegSum H d h = ∑ χ ∈ irrDegFinset H d, χ h := by
  rw [irrDegSum, Finset.sum_apply]

theorem irrDegSum_eq_zero_of_irrDeg_eq_empty [Finite H] (h : irrDeg H d = ∅) :
    irrDegSum H d = 0 := by
  have hf : irrDegFinset H d = ∅ := by rw [← Finset.coe_eq_empty, coe_irrDegFinset, h]
  rw [irrDegSum, hf, Finset.sum_empty]

theorem irrDegSum_mem_classFun [Finite H] : irrDegSum H d ∈ classFun H :=
  Submodule.sum_mem _ fun _ hχ => Irr_subset_classFun (mem_irrDegFinset.1 hχ).1

theorem irrDegSum_mem_virtualChars [Finite H] : irrDegSum H d ∈ virtualChars H := by
  rw [virtualChars_eq_span_Irr]
  exact Submodule.sum_mem _ fun _ hχ => Submodule.subset_span (mem_irrDegFinset.1 hχ).1

theorem mul_mem_Irr (ν : H →* ℂˣ) {χ : H → ℂ} (hχ : χ ∈ Irr H) :
    (fun x => (ν x : ℂ) * χ x) ∈ Irr H := by
  obtain ⟨V, hV, rfl⟩ := mem_Irr.1 hχ
  have h := character_mem_Irr_of_isIrreducible (Representation.twist V.ρ ν)
    (Representation.IsIrreducible.twist hV ν)
  have he : (Representation.twist V.ρ ν).character
      = fun x => (ν x : ℂ) * FDRep.character V x := by
    funext x
    rw [Representation.character_twist, fdRepCharacter_eq]
  rwa [he] at h

theorem mul_mem_irrDeg (ν : H →* ℂˣ) {χ : H → ℂ} (hχ : χ ∈ irrDeg H d) :
    (fun x => (ν x : ℂ) * χ x) ∈ irrDeg H d := by
  refine ⟨mul_mem_Irr ν hχ.1, ?_⟩
  simpa using hχ.2

theorem exists_monoidHom_apply_ne_one_of_notMem_commutator [Finite H] {h : H}
    (hh : h ∉ commutator H) : ∃ ν : H →* ℂˣ, (ν h : ℂ) ≠ 1 := by
  have : Finite (Abelianization H) := Quotient.finite _
  have h1 : Abelianization.of h ≠ 1 := fun hc =>
    hh (by rw [← Abelianization.ker_of]; exact MonoidHom.mem_ker.2 hc)
  obtain ⟨ψ, hψ⟩ := exists_monoidHom_apply_ne_one h1
  exact ⟨ψ.comp Abelianization.of, hψ⟩

theorem irrDegSum_apply_eq_zero_of_notMem_commutator [Finite H] {h : H}
    (hh : h ∉ commutator H) : irrDegSum H d h = 0 := by
  classical
  obtain ⟨ν, hν⟩ := exists_monoidHom_apply_ne_one_of_notMem_commutator hh
  set Φ : (H → ℂ) → (H → ℂ) := fun f x => (ν x : ℂ) * f x with hΦ
  have hinj : ∀ χ ∈ irrDegFinset H d, ∀ χ' ∈ irrDegFinset H d, Φ χ = Φ χ' → χ = χ' := by
    intro χ _ χ' _ he
    funext x
    exact mul_left_cancel₀ (Units.ne_zero (ν x)) (congrFun he x)
  have himage : (irrDegFinset H d).image Φ = irrDegFinset H d :=
    Finset.eq_of_subset_of_card_le
      (fun f hf => by
        obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hf
        exact mem_irrDegFinset.2 (mul_mem_irrDeg ν (mem_irrDegFinset.1 hχ)))
      (le_of_eq (Finset.card_image_of_injOn hinj).symm)
  have key : ∑ χ ∈ irrDegFinset H d, χ h
      = (ν h : ℂ) * ∑ χ ∈ irrDegFinset H d, χ h := by
    rw [Finset.mul_sum]
    calc ∑ χ ∈ irrDegFinset H d, χ h
        = ∑ f ∈ (irrDegFinset H d).image Φ, f h := by rw [himage]
      _ = ∑ χ ∈ irrDegFinset H d, Φ χ h := Finset.sum_image hinj
      _ = ∑ χ ∈ irrDegFinset H d, (ν h : ℂ) * χ h := rfl
  rw [irrDegSum_apply]
  have h2 : ((ν h : ℂ) - 1) * ∑ χ ∈ irrDegFinset H d, χ h = 0 := by linear_combination -key
  rcases mul_eq_zero.1 h2 with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) hν
  · exact h0

theorem sum_nonprincipalIrrDeg_apply_of_notMem_commutator [Finite H] {h : H}
    (hh : h ∉ commutator H) :
    ∑ χ ∈ nonprincipalIrrDegFinset H d, χ h = if d = 1 then -1 else 0 := by
  classical
  have h0 : ∑ χ ∈ irrDegFinset H d, χ h = 0 := by
    rw [← irrDegSum_apply]; exact irrDegSum_apply_eq_zero_of_notMem_commutator hh
  by_cases hd : d = 1
  · subst hd
    have hins : irrDegFinset H 1 = insert (1 : H → ℂ) (nonprincipalIrrDegFinset H 1) := by
      ext χ
      rw [mem_irrDegFinset, Finset.mem_insert, mem_nonprincipalIrrDegFinset]
      refine ⟨fun hχ => ?_, ?_⟩
      · by_cases h1 : χ = 1
        · exact Or.inl h1
        · exact Or.inr (mem_nonprincipalIrrDeg.2 ⟨hχ.1, h1, hχ.2⟩)
      · rintro (rfl | hχ)
        · exact one_mem_irrDeg_one
        · exact nonprincipalIrrDeg_subset_irrDeg hχ
    have hnot : (1 : H → ℂ) ∉ nonprincipalIrrDegFinset H 1 := fun hc =>
      (mem_nonprincipalIrrDeg.1 (mem_nonprincipalIrrDegFinset.1 hc)).2.1 rfl
    rw [hins, Finset.sum_insert hnot, Pi.one_apply] at h0
    rw [if_pos rfl]
    linear_combination h0
  · have heq : nonprincipalIrrDegFinset H d = irrDegFinset H d := by
      ext χ
      rw [mem_nonprincipalIrrDegFinset, mem_irrDegFinset]
      exact ⟨fun hχ => nonprincipalIrrDeg_subset_irrDeg hχ, fun hχ =>
        mem_nonprincipalIrrDeg.2 ⟨hχ.1, fun hc => one_notMem_irrDeg hd (hc ▸ hχ), hχ.2⟩⟩
    rw [heq, if_neg hd]
    exact h0

end CFSG.FeitThompson
