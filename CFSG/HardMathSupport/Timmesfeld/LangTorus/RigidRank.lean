module

public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


@[expose] def SimplyLacedTag (τ : Tag) : Prop := τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8

@[expose] def stringsLeOne (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k => (List.finRange τ.rank).all fun i =>
    decide (τ.stringData.up k i + τ.stringData.down k i ≤ 1) ||
      (List.ofFn (τ.rootCertificate.root k) == List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ)) ||
      (List.ofFn (τ.rootCertificate.root k) == List.ofFn (-Pi.single i 1 : Fin τ.rank → ℤ))

theorem stringsLeOne_eq_true {τ : Tag} (hτ : SimplyLacedTag τ) : stringsLeOne τ = true := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem not_isRoot_add_two_smul {τ : Tag} (hτ : SimplyLacedTag τ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {i : Fin τ.rank} (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    ¬IsRoot τ (α + (2 : ℤ) • Pi.single i 1) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  have h := stringsLeOne_eq_true hτ
  simp only [stringsLeOne, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hu : τ.stringData.up k i + τ.stringData.down k i ≤ 1 := by
    rcases h k hk i with (h | h) | h
    · exact h
    · exact absurd (List.ofFn_injective h) h₁
    · exact absurd (List.ofFn_injective h) h₂
  have hs := (StringData.isRoot_root_add_iff τ.rootCertificate_check τ.stringData_check hk i
    h₁ h₂).2
  intro hr
  have := ((hs 2).1 hr).2
  omega

theorem exists_cartan_neighbour {τ : Tag} (hτ : SimplyLacedTag τ) (j : Fin τ.rank) :
    ∃ l : Fin τ.rank, (τ.cartan l j).natAbs = 1 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> revert j <;> decide +kernel

section Ranks

variable {τ : Tag} {L : Type} [Field L]

theorem xCoeff_two_range_le (hτ : SimplyLacedTag τ) (j : Fin τ.rank) :
    Module.finrank L (LinearMap.range (xCoeff τ L j 2)) ≤ 1 := by
  have hw : (rootVec τ L (Pi.single j 1) : RootModule τ L) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot' (isRoot_single τ j)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have hle : LinearMap.range (xCoeff τ L j 2) ≤
      Submodule.span L {rootVec τ L (Pi.single j 1)} := by
    rintro _ ⟨v, rfl⟩
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => rw [map_add]; exact add_mem hv hw
    | single b c =>
      rw [← Finsupp.smul_single_one, map_smul]
      refine Submodule.smul_mem _ _ ?_
      rcases b with l | ⟨α, hα⟩
      · change xCoeff τ L j 2 (hVec τ L l) ∈ _
        rw [xCoeff_hVec]
        simp
      · rw [← rootVec_eq_single_of_isRoot' hα]
        by_cases h₁ : α = Pi.single j 1
        · subst h₁
          rw [xCoeff_rootVec_single]
          simp
        by_cases h₂ : α = -Pi.single j 1
        · subst h₂
          rw [xCoeff_rootVec_neg_single]
          simp [Submodule.mem_span_singleton_self]
        have hnr := not_isRoot_add_two_smul hτ hα h₁ h₂
        rw [xCoeff_rootVec_of_ne j 2 hα h₁ h₂,
          rootVec_eq_zero_of_not_isRoot'
            (β := α + ((2 : ℕ) : ℤ) • Pi.single j 1) (by simpa only [Nat.cast_ofNat] using hnr),
          smul_zero]
        exact zero_mem _
  calc Module.finrank L (LinearMap.range (xCoeff τ L j 2)) ≤
        Module.finrank L (Submodule.span L {rootVec τ L (Pi.single j 1)}) :=
      Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hw

theorem xCoeff_one_range_ge (hτ : SimplyLacedTag τ) (j : Fin τ.rank) :
    2 ≤ Module.finrank L (LinearMap.range (xCoeff τ L j 1)) := by
  obtain ⟨l, hl⟩ := exists_cartan_neighbour hτ j
  set w1 : RootModule τ L := Finsupp.single (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩) 1
    with hw1d
  set w2 : RootModule τ L := Finsupp.single (Sum.inl j) 1 with hw2d
  have hw1 : xCoeff τ L j 1 (hVec τ L l) = w1 := by
    rw [xCoeff_hVec]
    simp only [one_ne_zero, ↓reduceIte, hl, Nat.cast_one, one_smul]
    exact rootVec_eq_single_of_isRoot' (isRoot_single τ j)
  have hw2 : xCoeff τ L j 1 (rootVec τ L (-Pi.single j 1)) = w2 := by
    rw [xCoeff_rootVec_neg_single]
    simp only [one_ne_zero, ↓reduceIte]
    rfl
  have hli : LinearIndependent L ![w1, w2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun v : RootModule τ L => v (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩)) hst
    have h2 := congrArg (fun v : RootModule τ L => v (Sum.inl j)) hst
    simp [hw1d, hw2d] at h1 h2
    exact ⟨h1, h2⟩
  have hsub : Submodule.span L (Set.range ![w1, w2]) ≤ LinearMap.range (xCoeff τ L j 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨hVec τ L l, hw1⟩
    · exact ⟨rootVec τ L (-Pi.single j 1), hw2⟩
  have := Submodule.finrank_mono hsub
  rw [finrank_span_eq_card hli] at this
  simpa using this

end Ranks

section FinrankConj

variable {τ : Tag} {L : Type} [Field L]

theorem finrank_range_smul_le (c : L) (f : Module.End L (RootModule τ L)) :
    Module.finrank L (LinearMap.range (c • f)) ≤ Module.finrank L (LinearMap.range f) := by
  refine Submodule.finrank_mono ?_
  rintro _ ⟨v, rfl⟩
  exact ⟨c • v, by simp⟩

theorem finrank_range_smul_eq {c : L} (hc : c ≠ 0) (f : Module.End L (RootModule τ L)) :
    Module.finrank L (LinearMap.range (c • f)) = Module.finrank L (LinearMap.range f) := by
  refine le_antisymm (finrank_range_smul_le c f) ?_
  have := finrank_range_smul_le c⁻¹ (c • f)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem finrank_range_conj_le (g : ModGL τ L) (f : Module.End L (RootModule τ L)) :
    Module.finrank L (LinearMap.range ((g : Module.End L (RootModule τ L)) * f *
      ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)))) ≤
      Module.finrank L (LinearMap.range f) := by
  have h1 : LinearMap.range ((g : Module.End L (RootModule τ L)) * f *
      ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))) =
      (LinearMap.range (f * ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)))).map
        (g : Module.End L (RootModule τ L)) := by
    rw [mul_assoc]
    exact LinearMap.range_comp _ _
  rw [h1]
  refine (Submodule.finrank_map_le _ _).trans (Submodule.finrank_mono ?_)
  exact LinearMap.range_comp_le_range _ _

theorem finrank_range_conj_eq (g : ModGL τ L) (f : Module.End L (RootModule τ L)) :
    Module.finrank L (LinearMap.range ((g : Module.End L (RootModule τ L)) * f *
      ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)))) =
      Module.finrank L (LinearMap.range f) := by
  refine le_antisymm (finrank_range_conj_le g f) ?_
  have := finrank_range_conj_le g⁻¹ ((g : Module.End L (RootModule τ L)) * f *
    ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)))
  have e : ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) *
      ((g : Module.End L (RootModule τ L)) * f *
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))) *
      (((g⁻¹)⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) = f := by
    rw [inv_inv]
    calc ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) *
        ((g : Module.End L (RootModule τ L)) * f *
          ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))) * (g : Module.End L (RootModule τ L))
        = ((g⁻¹ * g : ModGL τ L) : Module.End L (RootModule τ L)) * f *
          ((g⁻¹ * g : ModGL τ L) : Module.End L (RootModule τ L)) := by
          simp only [Units.val_mul]
          noncomm_ring
      _ = f := by simp
  rwa [e] at this

end FinrankConj

end CFSG.HardMathSupport.Timmesfeld.LangTorus
