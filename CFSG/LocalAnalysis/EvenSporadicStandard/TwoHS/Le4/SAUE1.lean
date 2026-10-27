module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}
  {C : ECoord G}

namespace ECoord

theorem mem_E1sub_iff_vec (hQ : Q0Facts) {x : G} :
    x ∈ C.E1sub hQ ↔ x ∈ C.E ∧ C.vec x + C.vec x ∈ fVecs := by
  constructor
  · rintro ⟨hx, hxx⟩
    refine ⟨hx, ?_⟩
    have := ((C.mem_Fsub hQ).1 hxx).2
    rwa [C.vec_mul hx hx] at this
  · rintro ⟨hx, hv⟩
    refine ⟨hx, (C.mem_Fsub hQ).2 ⟨C.E.mul_mem hx hx, ?_⟩⟩
    rw [C.vec_mul hx hx]
    exact hv

theorem mul_self_eq_one_iff' {x : G} (hx : x ∈ C.E) : x * x = 1 ↔ C.vec x + C.vec x = 0 := by
  constructor
  · intro h
    rw [← C.vec_mul hx hx, h, C.vec_one]
  · intro h
    rw [← C.elt_vec (C.E.mul_mem hx hx), C.vec_mul hx hx, h, C.elt_zero]

end ECoord

namespace Sect8Hyp

variable {C : ECoord G} (h : Sect8Hyp C f n S₀) (hQ : Q0Facts)
include h hQ

theorem exists_sqrt {ε : G} (hε : ε ∈ C.E) (hεε : ε * ε = 1) : ∃ e ∈ C.E, e * e = ε := by
  have h1 := (C.mul_self_eq_one_iff' hε).1 hεε
  obtain ⟨w, hw⟩ := hQ.om_sq _ h1
  refine ⟨C.elt w, C.elt_mem w, ?_⟩
  rw [← C.elt_add, hw, C.elt_vec hε]

theorem E_cases {e : G} (he : e ∈ C.E) : e ∈ C.E1sub hQ ∨ f⁻¹ * e ∈ C.E1sub hQ := by
  have h4 : (e * e) * (e * e) = 1 := by
    have := C.pow_four he
    rw [show e ^ 4 = (e * e) * (e * e) by simp [pow_succ, mul_assoc]] at this
    exact this
  have hee : e * e ∈ C.E := C.E.mul_mem he he
  have h1 : (C.vec e + C.vec e) + (C.vec e + C.vec e) = 0 := by
    rw [← C.vec_mul he he, ← C.vec_mul hee hee, h4, C.vec_one]
  rcases hQ.om_f _ h1 with h2 | h2
  · left
    exact (C.mem_E1sub_iff_vec hQ).2 ⟨he, h2⟩
  · right
    obtain ⟨u', hu', hsq⟩ := hQ.sq_coset (C.vec e)
      ⟨C.vec e + C.vec e - tVec, h2, by abel⟩
    have hfi : f⁻¹ ∈ C.E := C.E.inv_mem h.f_mem
    have hmem : f⁻¹ * e ∈ C.E := C.E.mul_mem hfi he
    have hfv : C.vec f⁻¹ = -fVec := by
      have := C.vec_mul h.f_mem hfi
      rw [mul_inv_cancel, C.vec_one, h.vec_f] at this
      exact eq_neg_of_add_eq_zero_right this.symm
    refine (C.mem_E1sub_iff_vec hQ).2 ⟨hmem, ?_⟩
    have hvec : C.vec (f⁻¹ * e) = C.vec e - fVec := by
      rw [C.vec_mul hfi he, hfv]; abel
    rw [hvec, hsq]
    exact hu'

omit hQ in
theorem E_le_LF (H : Sect7Hyps G L f s y S₀ n) {e : G} (he : e ∈ C.E) :
    e ∈ L ⊔ zpowers f := SAU.hC H e (C.comm he h.f_mem)

theorem E1_le_L (H : Sect7Hyps G L f s y S₀ n) (hU : UFactsQ) {e : G}
    (he : e ∈ C.E1sub hQ) : e ∈ L := by
  obtain ⟨heE, hev⟩ := (C.mem_E1sub_iff_vec hQ).1 he
  obtain ⟨A, hA, hcomm⟩ := hU.comm
  obtain ⟨x, hxc, hxn, hxA⟩ := h.actN' A hA
  have hf2 : f ^ 2 ∈ L := H.four.sq_mem
  have hcl : ∀ w : V4, C.elt w * x * (C.elt w)⁻¹ * x⁻¹ = C.elt (w - A *ᵥ w) := by
    intro w
    have h1 : x * C.elt w * x⁻¹ = C.elt (A *ᵥ w) := by rw [C.conj_elt hxn, hxA]
    calc C.elt w * x * (C.elt w)⁻¹ * x⁻¹ = C.elt w * (x * C.elt w * x⁻¹)⁻¹ := by group
      _ = C.elt (w - A *ᵥ w) := by rw [h1, C.elt_sub]
  have hmemL : ∀ w : V4, C.elt (w - A *ᵥ w) ∈ L := by
    intro w
    rw [← hcl w]
    exact SAU.comm_mem_L H (E_le_LF h H (C.elt_mem w)) hxc
  rcases hcomm _ hev with ⟨w, hw⟩ | ⟨w, hw⟩
  · rw [← C.elt_vec heE, hw]
    exact hmemL w
  · have h1 : e = C.elt (C.vec e - tVec) * f ^ 2 := by
      rw [h.f2_eq hQ, ← C.elt_add, sub_add_cancel, C.elt_vec heE]
    rw [h1, hw]
    exact L.mul_mem (hmemL w) hf2

theorem inv_mem_E1sub {e : G} (he : e ∈ C.E) (hee : e * e = 1) : e ∈ C.E1sub hQ := by
  refine ⟨he, ?_⟩
  rw [hee]
  exact (C.Fsub hQ).one_mem

theorem mem_E1sub_of_mem_H1 (H : Sect7Hyps G L f s y S₀ n) (hU : UFactsQ) {e : G} (he : e ∈ C.E)
    (heH : e ∈ L ⊔ zpowers y) : e ∈ C.E1sub hQ := by
  rcases E_cases h hQ he with h1 | h1
  · exact h1
  · exfalso
    have hL := E1_le_L h hQ H hU h1
    apply SAU.f_not_mem_H1 H
    have : f = e * (f⁻¹ * e)⁻¹ := by group
    rw [this]
    exact (L ⊔ zpowers y).mul_mem heH ((L ⊔ zpowers y).inv_mem (Subgroup.mem_sup_left hL))

theorem conj_mem_E1sub {sl : List M4} (hU : UFactsOf sl) {m e : G}
    (hm : m ∈ normalizer (C.E : Set G)) (hms : C.mat m ∈ sl) (he : e ∈ C.E1sub hQ) :
    m * e * m⁻¹ ∈ C.E1sub hQ := by
  obtain ⟨heE, hev⟩ := (C.mem_E1sub_iff_vec hQ).1 he
  have hmE : m * e * m⁻¹ ∈ C.E := (mem_normalizer_iff.1 hm e).1 heE
  refine (C.mem_E1sub_iff_vec hQ).2 ⟨hmE, ?_⟩
  rw [C.vec_conj hm heE]
  exact hU.lam_inv _ hms _ hev

end Sect8Hyp

namespace ECoord

theorem ncard_Fsub (hQ : Q0Facts) (hnd : fVecs.Nodup) :
    ((C.Fsub hQ : Subgroup G) : Set G).ncard = fVecs.length := by
  have hset : ((C.Fsub hQ : Subgroup G) : Set G) = C.elt '' (fVecs.toFinset : Set V4) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxE, hxv⟩ := (C.mem_Fsub hQ).1 hx
      exact ⟨C.vec x, by simpa using hxv, C.elt_vec hxE⟩
    · rintro ⟨v, hv, rfl⟩
      exact (C.mem_Fsub hQ).2 ⟨C.elt_mem v, by rw [C.vec_elt]; simpa using hv⟩
  rw [hset, Set.ncard_image_of_injective _ C.elt_injective, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

end ECoord

end CFSG.EvenSporadicStandard.TwoHS
