module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Hyp

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix Finset

variable {G : Type*} [Group G]

@[expose] def Tsub (C : ECoord G) (tl : List M4) (hone : (1 : M4) ∈ tl)
    (hmul : ∀ A ∈ tl, ∀ B ∈ tl, A * B ∈ tl) (hinv : ∀ A ∈ tl, ∃ B ∈ tl, A * B = 1) :
    Subgroup G where
  carrier := {m | m ∈ normalizer (C.E : Set G) ∧ C.mat m ∈ tl}
  one_mem' := ⟨one_mem _, by rw [C.mat_one]; exact hone⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨mul_mem ha hb, by rw [C.mat_mul ha hb]; exact hmul _ ha' _ hb'⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    obtain ⟨B, hB, hAB⟩ := hinv _ ha'
    have : C.mat a⁻¹ = B := by
      calc C.mat a⁻¹ = C.mat a⁻¹ * (C.mat a * B) := by rw [hAB, mul_one]
        _ = (C.mat a⁻¹ * C.mat a) * B := by rw [mul_assoc]
        _ = B := by rw [C.mat_inv_mul ha, one_mul]
    rw [this]
    exact hB

section TsubLemmas

variable {C : ECoord G} {tl : List M4} {hone : (1 : M4) ∈ tl}
  {hmul : ∀ A ∈ tl, ∀ B ∈ tl, A * B ∈ tl} {hinv : ∀ A ∈ tl, ∃ B ∈ tl, A * B = 1}

theorem E_le_Tsub : C.E ≤ Tsub C tl hone hmul hinv := by
  intro e he
  refine ⟨le_normalizer he, ?_⟩
  have hn : e ∈ normalizer (C.E : Set G) := le_normalizer he
  have : C.mat e = 1 := (C.mat_eq_one_iff hn).2 fun e' he' => C.comm he he'
  rw [this]
  exact hone

end TsubLemmas

namespace Sect8Hyp

variable {C : ECoord G} {f n : G} {S₀ : Subgroup G} (h : Sect8Hyp C f n S₀)
include h

theorem mem_E_of_mat_eq_one {m : G} (hm : m ∈ normalizer (C.E : Set G))
    (h1 : C.mat m = 1) : m ∈ C.E := by
  have hc := (C.mat_eq_one_iff hm).1 h1
  refine h.centN m ?_ hc
  exact hc _ (pow_mem h.f_mem 2)

end Sect8Hyp

end CFSG.EvenSporadicStandard.TwoHS
