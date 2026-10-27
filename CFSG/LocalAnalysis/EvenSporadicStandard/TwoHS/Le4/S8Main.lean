module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Syl2

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

variable {G : Type*} [Group G]

namespace ECoord

variable (C : ECoord G)

@[expose] def E1sub (hQ : Q0Facts) : Subgroup G where
  carrier := {e | e ∈ C.E ∧ e * e ∈ C.Fsub hQ}
  one_mem' := ⟨C.E.one_mem, by rw [mul_one]; exact (C.Fsub hQ).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨C.E.mul_mem ha hb, ?_⟩
    have : a * b * (a * b) = (a * a) * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [C.comm hb ha]
        _ = (a * a) * (b * b) := by group
    rw [this]
    exact (C.Fsub hQ).mul_mem ha' hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨C.E.inv_mem ha, ?_⟩
    have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by
      rw [_root_.mul_inv_rev]
    rw [this]
    exact (C.Fsub hQ).inv_mem ha'

end ECoord

structure Lemma61Out (C : ECoord G) (hQ : Q0Facts) (f : G) (S₀ T K : Subgroup G) : Prop where
  sylow : Sect7SylowData (f ^ 2) T C.E (C.Fsub hQ) K
  S₀_le : S₀ ≤ T
  T_cent : ∀ w ∈ T, w * f ^ 2 = f ^ 2 * w → w ∈ S₀
  core : ∀ x ∈ T, (∀ z ∈ T, (z * x * z⁻¹) * f ^ 2 = f ^ 2 * (z * x * z⁻¹)) → x ∈ K
  K_cent : ∀ x ∈ K, x * f = f * x → x ∈ C.E
  sq_fusion : ∀ g : G, g⁻¹ * f ^ 2 * g ∈ C.E →
    g⁻¹ * f ^ 2 * g ∈ {x : G | ∃ u ∈ C.Fsub hQ, x = f ^ 2 * u}
  sq_coset : ∀ x ∈ C.E, x * x ∈ {x : G | ∃ u ∈ C.Fsub hQ, x = f ^ 2 * u} →
    f⁻¹ * x ∈ C.E1sub hQ

theorem sect8_lemma61 [Finite G] {C : ECoord G} {f n s : G} {S₀ : Subgroup G}
    (h : Sect8Hyp C f n S₀) (hQ : Q0Facts) (hNC : NormComplete) (hCF : CandFacts)
    (hAF : AlphaFacts) (hf : orderOf f = 4) (hnt : n * f ^ 2 * n⁻¹ = s ^ 2)
    (hs2 : s ^ 2 ≠ f ^ 2) (hn : ¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹) :
    ∃ T K : Subgroup G, Lemma61Out C hQ f S₀ T K := by
  obtain ⟨n₀, hn0, hα₀, hn0t, hs2z⟩ := h.exists_n0 hQ hNC hCF hnt hs2
  have hT : TFacts (C.mat n₀) := hAF _ hα₀
  have hf2 : f ^ 2 = C.elt tVec := h.f2_eq hQ
  have hfus := fun m hm => h.exists_fus hQ hf hn hs2z (m := m) hm
  have hS : ∀ m ∈ normalizer (C.E : Set G), C.mat m ∈ sList (C.mat n₀) :=
    fun m hm => h.mat_mem_sList hQ hn0 hn0t hs2z hfus hm
  have hR : ∀ B ∈ sList (C.mat n₀), ∃ m ∈ normalizer (C.E : Set G), C.mat m = B :=
    fun B hB => h.exists_mat_of_mem_sList hn0 hQ hB
  have hSD := sylowData h hQ hT hS hR hf2
  refine ⟨Tα C hT, Kα C hT, hSD, ?_, ?_, ?_, ?_, h.sq_fusion hQ hf hn hs2z, ?_⟩
  ·
    intro x hx
    exact ⟨h.S₀_norm x hx, hT.shat_sub _ (h.actS x hx)⟩
  ·
    intro w hw hc
    have h1 : C.mat w *ᵥ tVec = tVec := by
      have : w * C.elt tVec * w⁻¹ = C.elt tVec := by
        rw [← hf2]
        calc w * f ^ 2 * w⁻¹ = (f ^ 2 * w) * w⁻¹ := by rw [hc]
          _ = f ^ 2 := by group
      rw [C.conj_elt hw.1] at this
      exact C.elt_injective this
    obtain ⟨w', hw'S, hw'⟩ := h.actS' _ (hT.stab_t _ hw.2 h1)
    have hw'n := h.S₀_norm _ hw'S
    have hmat : C.mat (w * w'⁻¹) = 1 := by
      rw [C.mat_mul hw.1 (inv_mem hw'n), ← hw', C.mat_mul_inv hw'n]
    have hE := h.mem_E_of_mat_eq_one (mul_mem hw.1 (inv_mem hw'n)) hmat
    have hww : w = (w * w'⁻¹) * w' := by group
    rw [hww]
    exact S₀.mul_mem (h.E_le hE) hw'S
  ·
    refine core_of_K_def (T := Tα C hT) (E := C.E) (F := C.Fsub hQ) (K := Kα C hT) ?_
      hSD.E_inv ?_ (T_K_def h hQ hT hS hR)
    · rw [← sq, ← pow_mul]
      have : f ^ 4 = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
      exact this
    · intro u hu
      obtain ⟨A, hA, hAt⟩ := hT.ftrans _ hu.2
      obtain ⟨z, hz, hzA⟩ := realize_T h hQ hT hS hR A hA
      refine ⟨z, hz, ?_⟩
      rw [hf2, C.conj_elt hz.1, hzA, hAt, C.elt_add, C.elt_vec hu.1]
  · exact T_K_cent h hQ hT hS hR
  ·
    intro x hx hxx
    obtain ⟨u, hu, hxu⟩ := hxx
    have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
    have hv : C.vec x + C.vec x = tVec + C.vec u := by
      rw [← C.vec_mul hx hx, hxu, C.vec_mul hf2E hu.1, h.vec_f2 hQ]
    obtain ⟨u', hu', hsq⟩ := hQ.sq_coset (C.vec x) ⟨C.vec u, hu.2, hv⟩
    have hfi : f⁻¹ ∈ C.E := C.E.inv_mem h.f_mem
    have hmem : f⁻¹ * x ∈ C.E := C.E.mul_mem hfi hx
    have hvec : C.vec (f⁻¹ * x) = C.vec x - fVec := by
      have hfv : C.vec f⁻¹ = -fVec := by
        have := C.vec_mul h.f_mem hfi
        rw [mul_inv_cancel, C.vec_one, h.vec_f] at this
        exact eq_neg_of_add_eq_zero_right this.symm
      rw [C.vec_mul hfi hx, hfv]
      abel
    refine ⟨hmem, (C.mem_Fsub hQ).2 ⟨C.E.mul_mem hmem hmem, ?_⟩⟩
    rw [C.vec_mul hmem hmem, hvec, hsq]
    exact hu'

end CFSG.EvenSporadicStandard.TwoHS
