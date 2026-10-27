module

public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.ConjugacyClassSumScalar
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Aux

variable {α : Type*} [Fintype α]

theorem cfInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → α → ℂ) (h : α → ℂ) :
    cfInner (∑ i ∈ s, f i) h = ∑ i ∈ s, cfInner (f i) h := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [cfInner_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, cfInner_add_left, ih, Finset.sum_cons]

theorem cfInner_zsmul_left (n : ℤ) (f h : α → ℂ) : cfInner (n • f) h = (n : ℂ) * cfInner f h := by
  rw [← Int.cast_smul_eq_zsmul ℂ n f, cfInner_smul_left]

end Aux

variable {L : Type*} [Group L] {S : Set (L → ℂ)} {χ₀ : L → ℂ} {d : ℂ}

theorem apply_one_ne_zero_of_mem_Irr {χ : L → ℂ} (hχ : χ ∈ Irr L) : χ 1 ≠ 0 := by
  obtain ⟨V, hV, rfl⟩ := mem_Irr.1 hχ
  have := hV
  exact character_one_ne_zero V.ρ

theorem sub_mem_charSpanZero (hdeg : ∀ χ ∈ S, χ 1 = d) {χ : L → ℂ} (hχ : χ ∈ S) (hχ₀ : χ₀ ∈ S) :
    χ - χ₀ ∈ charSpanZero S := by
  refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
    (Submodule.subset_span hχ₀), ?_⟩
  simp [hdeg χ hχ, hdeg χ₀ hχ₀]

theorem span_sub_eq_charSpanZero (hSfin : S.Finite) (hS : S ⊆ Irr L) (hχ₀ : χ₀ ∈ S)
    (hdeg : ∀ χ ∈ S, χ 1 = d) :
    Submodule.span ℤ (Set.range fun χ : (S \ {χ₀} : Set (L → ℂ)) => (χ : L → ℂ) - χ₀)
      = charSpanZero S := by
  classical
  refine le_antisymm ?_ fun f hf => ?_
  · rw [Submodule.span_le]
    rintro _ ⟨χ, rfl⟩
    exact sub_mem_charSpanZero hdeg χ.2.1 hχ₀
  obtain ⟨hfspan, hf1⟩ := mem_charSpanZero.1 hf
  rw [← hSfin.coe_toFinset] at hfspan
  obtain ⟨a, -, hfa⟩ := Submodule.mem_span_finset.1 hfspan
  set T := hSfin.toFinset with hT
  have hmemT : ∀ χ : L → ℂ, χ ∈ T ↔ χ ∈ S := fun χ => hSfin.mem_toFinset
  have hd : d ≠ 0 := by
    rw [← hdeg χ₀ hχ₀]; exact apply_one_ne_zero_of_mem_Irr (hS hχ₀)
  have key : ((∑ χ ∈ T, a χ : ℤ) : ℂ) * d = 0 := by
    push_cast
    rw [Finset.sum_mul]
    calc ∑ χ ∈ T, (a χ : ℂ) * d = ∑ χ ∈ T, (a χ • χ) (1 : L) := by
          refine Finset.sum_congr rfl fun χ hχ => ?_
          simp [hdeg χ ((hmemT χ).1 hχ)]
      _ = f 1 := by rw [← hfa]; simp
      _ = 0 := hf1
  have hsum : ∑ χ ∈ T, a χ = 0 := by
    exact_mod_cast (mul_eq_zero.1 key).resolve_right hd
  have hrw : f = ∑ χ ∈ T, a χ • ((χ : L → ℂ) - χ₀) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, hfa, zero_smul, sub_zero]
  rw [hrw]
  refine Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _ ?_
  by_cases h : χ = χ₀
  · simp [h]
  · exact Submodule.subset_span ⟨⟨χ, (hmemT χ).1 hχ, h⟩, rfl⟩

theorem linearIndependent_sub_of_subset_Irr [Finite L] (hS : S ⊆ Irr L) (hχ₀ : χ₀ ∈ S) :
    LinearIndependent ℤ (fun χ : (S \ {χ₀} : Set (L → ℂ)) => (χ : L → ℂ) - χ₀) := by
  classical
  have : Fintype L := Fintype.ofFinite L
  rw [linearIndependent_iff']
  intro t g hg j hj
  have hjS : (j : L → ℂ) ∈ S := j.2.1
  have hjne : (j : L → ℂ) ≠ χ₀ := j.2.2
  have key := congrArg (fun f => cfInner f ((j : L → ℂ))) hg
  simp only [cfInner_sum_left, cfInner_zsmul_left, cfInner_sub_left, cfInner_zero_left] at key
  have h0 : cfInner χ₀ ((j : L → ℂ)) = 0 :=
    cfInner_eq_zero_of_mem_Irr (hS hχ₀) (hS hjS) (Ne.symm hjne)
  have hij : ∀ i : (S \ {χ₀} : Set (L → ℂ)),
      cfInner ((i : L → ℂ)) ((j : L → ℂ)) = if i = j then 1 else 0 := by
    intro i
    rw [cfInner_eq_ite_of_mem_Irr (hS i.2.1) (hS hjS)]
    congr 1
    simp [Subtype.ext_iff]
  simp only [h0, hij, sub_zero] at key
  rw [Finset.sum_congr rfl (fun i _ => by rw [mul_ite, mul_one, mul_zero] :
    ∀ i ∈ t, (g i : ℂ) * (if i = j then 1 else 0) = if i = j then (g i : ℂ) else 0),
    Finset.sum_ite_eq' t j (fun i => (g i : ℂ)), if_pos hj] at key
  exact_mod_cast key

noncomputable def charSpanZeroBasis [Finite L] (hSfin : S.Finite) (hS : S ⊆ Irr L)
    (hχ₀ : χ₀ ∈ S) (hdeg : ∀ χ ∈ S, χ 1 = d) :
    Module.Basis (S \ {χ₀} : Set (L → ℂ)) ℤ (charSpanZero S) :=
  (Module.Basis.span (linearIndependent_sub_of_subset_Irr hS hχ₀)).map
    (LinearEquiv.ofEq _ _ (span_sub_eq_charSpanZero hSfin hS hχ₀ hdeg))

@[simp]
theorem charSpanZeroBasis_apply [Finite L] (hSfin : S.Finite) (hS : S ⊆ Irr L) (hχ₀ : χ₀ ∈ S)
    (hdeg : ∀ χ ∈ S, χ 1 = d) (χ : (S \ {χ₀} : Set (L → ℂ))) :
    (charSpanZeroBasis hSfin hS hχ₀ hdeg χ : L → ℂ) = (χ : L → ℂ) - χ₀ := by
  simp [charSpanZeroBasis, Module.Basis.span_apply]

theorem existsUnique_finsupp_charSpanZero [Finite L] (hSfin : S.Finite) (hS : S ⊆ Irr L)
    (hχ₀ : χ₀ ∈ S) (hdeg : ∀ χ ∈ S, χ 1 = d) (f : charSpanZero S) :
    ∃! a : (S \ {χ₀} : Set (L → ℂ)) →₀ ℤ,
      Finsupp.linearCombination ℤ (fun χ : (S \ {χ₀} : Set (L → ℂ)) => (χ : L → ℂ) - χ₀) a
        = (f : L → ℂ) := by
  set b := charSpanZeroBasis hSfin hS hχ₀ hdeg with hb
  have hcoe : ∀ a : (S \ {χ₀} : Set (L → ℂ)) →₀ ℤ,
      Finsupp.linearCombination ℤ (fun χ : (S \ {χ₀} : Set (L → ℂ)) => (χ : L → ℂ) - χ₀) a
        = ((Finsupp.linearCombination ℤ b a : charSpanZero S) : L → ℂ) := by
    intro a
    simp only [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Submodule.coe_smul, hb, charSpanZeroBasis_apply]
  refine ⟨b.repr f, ?_, fun a ha => ?_⟩
  · change Finsupp.linearCombination ℤ _ (b.repr f) = (f : L → ℂ)
    rw [hcoe, Module.Basis.linearCombination_repr]
  · have h : Finsupp.linearCombination ℤ b a = f := Subtype.ext (by rw [← hcoe, ha])
    rw [← h, Module.Basis.repr_linearCombination]

theorem finrank_charSpanZero [Finite L] (hSfin : S.Finite) (hS : S ⊆ Irr L) (hχ₀ : χ₀ ∈ S)
    (hdeg : ∀ χ ∈ S, χ 1 = d) :
    Module.finrank ℤ (charSpanZero S) = S.ncard - 1 := by
  rw [Module.finrank_eq_nat_card_basis (charSpanZeroBasis hSfin hS hχ₀ hdeg),
    Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hχ₀]

end CFSG.FeitThompson
