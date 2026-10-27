module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUConj
public import Certificates.Certificate26823
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUCl
public import Certificates.Certificate26820

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

section ModelZ


theorem modelZ_of_zdata (hU37 : U37Facts)
    (hZ : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G)
      (n : G), Sect7Hyps G L f s y S₀ n → ∀ C : ECoord G, Sect8Hyp C f n S₀ →
        ∃ r w ρ : G, ZData C L f y r w ρ) : ModelZ := by
  intro G _ _ L f s y S₀ n H C h
  obtain ⟨r, w₀, ρ, hz⟩ := hZ G L f s y S₀ n H C h
  obtain ⟨hr, hr3, hr1, hw₀, hw₀w₀, hcl, hrw₀, hρ3, hρt, hρn, hρr, hρw₀⟩ := hz
  have hQ : Q0Facts := Certificates.certificate26420
  have hU : UFactsQ := Certificates.certificate26820
  obtain ⟨hrt, hrn⟩ := SAU.mem_M0.1 hr
  have hB : C.mat r ∈ q0List := h.actN r hrt hrn
  have hB3 : C.mat r ^ 3 = 1 := by rw [← ECoord.mat_pow hrn, hr3, C.mat_one]
  have hB1 : C.mat r ≠ 1 := by
    intro hm
    apply hr1
    have hrE : r ∈ C.E := h.centN r hrt ((C.mat_eq_one_iff hrn).1 hm)
    have h4 : r ^ 3 * r = 1 := by rw [← pow_succ]; exact C.pow_four hrE
    rwa [hr3, one_mul] at h4
  obtain ⟨c, hcfix, hc2, hc3⟩ := hU37.three _ hB hB3 hB1
  have hf2 : f ^ 2 = C.elt tVec := h.f2_eq hQ
  obtain ⟨B7, hB7q, hB77, hB71⟩ := hU37.ex7
  obtain ⟨v, hvt, hvn, hvm⟩ := h.actN' B7 hB7q
  have hv7E : v ^ 7 ∈ C.E := by
    refine h.centN _ ((Commute.pow_left (show Commute v (f ^ 2) from hvt) 7).eq) ?_
    exact (C.mat_eq_one_iff (pow_mem hvn 7)).1 (by rw [ECoord.mat_pow hvn, hvm, hB77])
  have hv₀7 : (v ^ 8) ^ 7 = 1 := by
    have h56 : (v ^ 8) ^ 7 = ((v ^ 7) ^ 4) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
    rw [h56, C.pow_four hv7E, one_pow]
  have hv₀n : v ^ 8 ∈ normalizer (C.E : Set G) := pow_mem hvn 8
  have hv₀m : C.mat (v ^ 8) = B7 := by
    rw [ECoord.mat_pow hvn, hvm, show (8 : ℕ) = 7 + 1 from rfl, pow_succ, hB77, one_mul]
  refine ⟨r, v ^ 8, w₀, ρ, C.elt c, hr, hr3, hr1,
    SAU.mem_M0.2 ⟨(Commute.pow_left (show Commute v (f ^ 2) from hvt) 8).eq, hv₀n⟩, hv₀7, ?_,
    C.elt_mem c, ?_, ?_, ?_, hw₀, hw₀w₀, hcl, hrw₀, hρ3, hρt, hρn, hρr, hρw₀⟩
  · intro x hxE hxL hfix
    have hxH : x ∈ L ⊔ zpowers y := Subgroup.mem_sup_left hxL
    have hx1 := Sect8Hyp.mem_E1sub_of_mem_H1 h hQ H hU hxE hxH
    have hxv := ((ECoord.mem_E1sub_iff_vec hQ).1 hx1).2
    have hmat := C.vec_conj hv₀n hxE
    rw [hfix, hv₀m] at hmat
    rcases hU37.seven B7 hB7q hB77 hB71 (C.vec x) hxv hmat.symm with h0 | h0
    · left
      rw [← C.elt_vec hxE, h0, C.elt_zero]
    · right
      rw [← C.elt_vec hxE, h0, ← hf2]
  · have h1 := C.conj_elt hrn c
    rw [hcfix] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  · intro h1
    apply hc2
    apply C.elt_injective
    rw [C.elt_add, C.elt_zero]
    exact h1
  · intro h1
    apply hc3
    apply C.elt_injective
    rw [C.elt_add]
    rw [hf2] at h1
    exact h1


theorem modelZ_holds (hHN : HNCentralizerFacts) : ModelZ :=
  modelZ_of_zdata Certificates.certificate26823
    fun _ _ _ _ _ _ _ _ _ H _ h => zdata_holds hHN H h

end ModelZ

end CFSG.EvenSporadicStandard.TwoHS
