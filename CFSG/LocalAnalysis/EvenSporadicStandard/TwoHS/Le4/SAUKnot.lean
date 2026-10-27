module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUOProps
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyNorm
public import Certificates.Certificate26821
public import Certificates.Certificate26822

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Facts


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}
  {C : ECoord G}

theorem exists_UFactsOf (H : Sect7Hyps G L f s y S₀ n) (hQ : Q0Facts)
    (h : Sect8Hyp C f n S₀) :
    ∃ sl : List M4, UFactsOf sl ∧ ∀ m ∈ normalizer (C.E : Set G), C.mat m ∈ sl := by
  have hNC : NormComplete := Certificates.certificate26421
  have hCF : CandFacts := Certificates.certificate26422
  have hs2 : s ^ 2 ≠ f ^ 2 := by
    intro h2
    obtain ⟨u, hu1, -, hu3⟩ := H.u
    obtain ⟨τ, hτ, hτ'⟩ := H.four.exists_center_gen
    apply hu3
    have : u = τ := Subtype.ext (hu1.trans (h2.trans hτ'.symm))
    rw [this]
    exact hτ
  obtain ⟨n₀, hn0, hα₀, hn0t, hs2z⟩ := h.exists_n0 hQ hNC hCF H.n_t hs2
  have hfus := fun m hm => h.exists_fus hQ H.four.order H.not_conj hs2z (m := m) hm
  have hS : ∀ m ∈ normalizer (C.E : Set G), C.mat m ∈ sList (C.mat n₀) :=
    fun m hm => h.mat_mem_sList hQ hn0 hn0t hs2z hfus hm
  refine ⟨sList (C.mat n₀), ?_, hS⟩
  simp only [alphaReps, List.mem_cons, List.not_mem_nil, or_false] at hα₀
  rcases hα₀ with h1 | h1
  · rw [h1]; exact Certificates.certificate26821
  · rw [h1]; exact Certificates.certificate26822

theorem knotInLf_holds : ∀ hQ : Q0Facts, KNotInLf hQ := by
  intro hQ G _ _ L f s y S₀ n H C h T K hT w hwT hwE hwc _ _
  obtain ⟨sl, hUS, hS⟩ := exists_UFactsOf H hQ h
  have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
  have hff : f ^ 2 * f ^ 2 = 1 := by
    rw [← pow_add]; exact H.f_pow_four
  have hwn : w ∈ normalizer (C.E : Set G) := hT.sylow.mem_normalizer_E hwT
  have hmat := h.mat_neg_of_comm hUS hwn (hS w hwn) hwE hwc
  intro hw
  obtain ⟨l, hl, i, hw'⟩ := exists_mul_zpow_of_mem_sup (SAU.hcom H) hw
  have hcw : w * f = f * w := by
    rw [hw']
    exact ((show Commute l f from SAU.hcom H l hl).mul_left
      (Commute.zpow_left (Commute.refl f) i)).eq
  have h1 := h.inv_of_mat_neg hwn hmat h.f_mem
  rw [hcw] at h1
  have h2 : f = f⁻¹ := by
    calc f = f * w * w⁻¹ := by group
      _ = f⁻¹ := h1
  have h3 : f ^ 2 = 1 := by
    calc f ^ 2 = f * f := sq f
      _ = f * f⁻¹ := by rw [← h2]
      _ = 1 := by group
  have := orderOf_dvd_of_pow_eq_one h3
  rw [H.four.order] at this
  omega

end Facts

end CFSG.EvenSporadicStandard.TwoHS
