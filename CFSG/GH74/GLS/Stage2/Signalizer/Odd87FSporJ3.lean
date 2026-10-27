module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSpor
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Model
public import Certificates.Certificate5166

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Certificates.Odd87F3 Certificates.Odd87F3.J3

theorem j3_F3S :
    (∀ p ∈ [3, 5, 17, 19], F3S j3P (tp 6156 (rowAt 0).rep) p) ∧
    (∀ p ∈ [3, 5, 17, 19], F3S j3P (tp 6156 (rowAt 1).rep) p) :=
  Certificates.certificate5166

theorem sporKL_J3 :
    SporKL .J3 := by
  intro Y _ _ hY p α Xh h
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥j3P := (e : Y ≃* NativeSporadic.J3).trans j3PermEquiv
  obtain ⟨hF0, hF1⟩ := j3_F3S
  obtain ⟨-, -, -, -, hcover, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  refine false_of_F3_autModel j3_autModel e'
    [tp 6156 (rowAt 0).rep, tp 6156 (rowAt 1).rep] ?_ (ps := [3, 5, 17, 19]) ?_ ?_ ?_ h
  · intro t ht ho
    obtain ⟨r, hr, g, hg, hrt⟩ := hcover t ht ho
    obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.1 hr
    have hlen : j3Rows.length = 2 := by decide
    have hi2 : i < 2 := hlen ▸ hi
    have hreq : r = rowAt ⟨i, hi2⟩ := hir.symm
    refine ⟨tp 6156 r.rep, ?_, g, hg, hrt⟩
    rw [hreq]
    interval_cases i <;> simp
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  · intro q hq hq2 hd
    rw [card_j3P] at hd
    have := prime_mem_of_dvd (by norm_num : (50232960 : ℕ) ≠ 0)
      (by norm_num : Nat.primeFactorsList 50232960 =
        [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 17, 19]) hq hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    omega
  · intro r hr q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hF0 q hq
    · exact hF1 q hq

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
