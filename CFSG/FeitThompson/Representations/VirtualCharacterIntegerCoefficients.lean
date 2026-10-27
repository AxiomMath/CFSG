module

public import CFSG.FeitThompson.Representations.IrreducibleCharactersOrthonormalBasis
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

noncomputable section

variable {G : Type*} [Group G]

theorem mem_classFun_of_mem_span_Irr {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G)) :
    f ∈ classFun G :=
  virtualChars_le_classFun (span_Irr_le_virtualChars hf)

theorem mem_span_Irr_iff_exists_intCast_sum [Fintype (Irr G)] {f : G → ℂ} :
    f ∈ Submodule.span ℤ (Irr G) ↔
      ∃ n : Irr G → ℤ, f = ∑ χ : Irr G, (n χ : ℂ) • ((χ : Irr G) : G → ℂ) := by
  have hrange : Set.range (fun χ : Irr G => ((χ : Irr G) : G → ℂ)) = Irr G := Subtype.range_coe
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1
      (show f ∈ Submodule.span ℤ (Set.range (fun χ : Irr G => ((χ : Irr G) : G → ℂ))) by
        rw [hrange]; exact hf)
    exact ⟨c, by simpa [Int.cast_smul_eq_zsmul] using hc.symm⟩
  · rintro ⟨n, rfl⟩
    refine Submodule.sum_mem _ fun χ _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span χ.2)

variable [Fintype G]

theorem cfInner_intCast_sum_Irr_coe [Fintype (Irr G)] (n : Irr G → ℤ) (ψ : Irr G) :
    cfInner (∑ χ : Irr G, (n χ : ℂ) • ((χ : Irr G) : G → ℂ)) ((ψ : Irr G) : G → ℂ)
      = (n ψ : ℂ) := by
  classical
  rw [cfInner_sum_left]
  simp only [cfInner_smul_left, cfInner_coe_Irr, mul_ite, mul_one, mul_zero]
  simp

theorem eq_sum_cfInner_smul_of_mem_classFun [Fintype (Irr G)] {f : G → ℂ}
    (hf : f ∈ classFun G) :
    f = ∑ χ : Irr G, cfInner f ((χ : Irr G) : G → ℂ) • ((χ : Irr G) : G → ℂ) :=
  classFun.coe_eq_sum_cfInner_smul (⟨f, hf⟩ : classFun G)

theorem mem_span_Irr_iff_forall_exists_int_cfInner {f : G → ℂ} (hf : f ∈ classFun G) :
    f ∈ Submodule.span ℤ (Irr G) ↔ ∀ χ ∈ Irr G, ∃ n : ℤ, cfInner f χ = (n : ℂ) := by
  have : Fintype (Irr G) := Fintype.ofFinite _
  rw [mem_span_Irr_iff_exists_intCast_sum]
  refine ⟨fun ⟨n, hn⟩ χ hχ => ⟨n ⟨χ, hχ⟩, hn ▸ cfInner_intCast_sum_Irr_coe n ⟨χ, hχ⟩⟩,
    fun h => ?_⟩
  choose n hn using h
  refine ⟨fun χ => n χ χ.2, ?_⟩
  rw [eq_sum_cfInner_smul_of_mem_classFun hf]
  exact Finset.sum_congr rfl fun χ _ => by rw [hn χ.1 χ.2]

theorem cfInner_intCast_sum_Irr_intCast_sum_Irr [Fintype (Irr G)] (a b : Irr G → ℤ) :
    cfInner (∑ χ : Irr G, (a χ : ℂ) • ((χ : Irr G) : G → ℂ))
        (∑ χ : Irr G, (b χ : ℂ) • ((χ : Irr G) : G → ℂ))
      = ((∑ χ : Irr G, a χ * b χ : ℤ) : ℂ) := by
  classical
  rw [cfInner_sum_right]
  push_cast
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [cfInner_smul_right, cfInner_intCast_sum_Irr_coe]
  simp [mul_comm]

theorem exists_int_cfInner_of_mem_span_Irr {f h : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (hh : h ∈ Submodule.span ℤ (Irr G)) :
    ∃ m : ℤ, cfInner f h = (m : ℂ) := by
  have : Fintype (Irr G) := Fintype.ofFinite _
  obtain ⟨a, rfl⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hf
  obtain ⟨b, rfl⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hh
  exact ⟨_, cfInner_intCast_sum_Irr_intCast_sum_Irr a b⟩

theorem cfInner_self_intCast_sum_Irr [Fintype (Irr G)] (n : Irr G → ℤ) :
    cfInner (∑ χ : Irr G, (n χ : ℂ) • ((χ : Irr G) : G → ℂ))
        (∑ χ : Irr G, (n χ : ℂ) • ((χ : Irr G) : G → ℂ))
      = ((∑ χ : Irr G, n χ ^ 2 : ℤ) : ℂ) := by
  rw [cfInner_intCast_sum_Irr_intCast_sum_Irr]
  push_cast
  exact Finset.sum_congr rfl fun χ _ => by ring

theorem cfInner_self_eq_sum_sq_cfInner [Fintype (Irr G)] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) :
    cfInner f f = ∑ χ : Irr G, cfInner f ((χ : Irr G) : G → ℂ) ^ 2 := by
  obtain ⟨n, rfl⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hf
  rw [cfInner_self_intCast_sum_Irr]
  push_cast
  exact Finset.sum_congr rfl fun ψ _ => by rw [cfInner_intCast_sum_Irr_coe]

end

end CFSG.FeitThompson
