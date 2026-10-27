module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Hyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Fusion

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

variable {G : Type*} [Group G]

namespace ECoord

variable (C : ECoord G)

@[expose] def Fsub (hQ : Q0Facts) : Subgroup G where
  carrier := {x | x ∈ C.E ∧ C.vec x ∈ fVecs}
  one_mem' := ⟨C.E.one_mem, by rw [C.vec_one]; exact hQ.f_zero⟩
  mul_mem' := by
    rintro x y ⟨hx, hxv⟩ ⟨hy, hyv⟩
    exact ⟨C.E.mul_mem hx hy, by rw [C.vec_mul hx hy]; exact hQ.f_add _ hxv _ hyv⟩
  inv_mem' := by
    rintro x ⟨hx, hxv⟩
    refine ⟨C.E.inv_mem hx, ?_⟩
    have h1 : C.vec x⁻¹ = - C.vec x := by
      have := C.vec_mul hx (C.E.inv_mem hx)
      rw [mul_inv_cancel, C.vec_one] at this
      exact eq_neg_of_add_eq_zero_right this.symm
    have h2 : -C.vec x = C.vec x := by
      have := hQ.f_two _ hxv
      exact neg_eq_of_add_eq_zero_right this
    rw [h1, h2]
    exact hxv

theorem mem_Fsub (hQ : Q0Facts) {x : G} : x ∈ C.Fsub hQ ↔ x ∈ C.E ∧ C.vec x ∈ fVecs := Iff.rfl

end ECoord

namespace Sect8Hyp

variable {C : ECoord G} {f n : G} {S₀ : Subgroup G} (h : Sect8Hyp C f n S₀)
include h

theorem sq_fusion {s : G} (hQ : Q0Facts) (hf : orderOf f = 4)
    (hn : ¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹) (hs2z : s ^ 2 = C.elt zpVec) :
    ∀ g : G, g⁻¹ * f ^ 2 * g ∈ C.E →
      g⁻¹ * f ^ 2 * g ∈ {x : G | ∃ u ∈ C.Fsub hQ, x = f ^ 2 * u} := by
  have hf2 : f ^ 2 = C.elt tVec := h.f2_eq hQ
  have hs2f : s ^ 2 * f ^ 2 = C.elt zmVec := by
    rw [hs2z, hf2, ← C.elt_add]
    congr 1
    rw [hQ.zp_eq, add_comm tVec zmVec, add_assoc, hQ.t_two, add_zero]
  have hE_inv : ∀ x ∈ C.E, x * x = 1 →
      x ∈ C.Fsub hQ ∨ ∃ u ∈ C.Fsub hQ, x = f ^ 2 * u := by
    intro x hx hxx
    have h1 : C.vec x + C.vec x = 0 := by
      rw [← C.vec_mul hx hx, hxx, C.vec_one]
    rcases hQ.om_f _ h1 with h2 | h2
    · exact Or.inl ⟨hx, h2⟩
    · refine Or.inr ⟨C.elt (C.vec x - tVec), ⟨C.elt_mem _, ?_⟩, ?_⟩
      · rw [C.vec_elt]; exact h2
      · rw [hf2, ← C.elt_add, add_sub_cancel, C.elt_vec hx]
  have hF_conj : ∀ u ∈ C.Fsub hQ, u ≠ 1 → ∃ g : G, u = g * (s ^ 2 * f ^ 2) * g⁻¹ := by
    rintro u ⟨hu, huv⟩ hu1
    have hu0 : C.vec u ≠ 0 := by
      intro h0
      apply hu1
      rw [← C.elt_vec hu, h0, C.elt_zero]
    obtain ⟨A, hA, hAz⟩ := hQ.zm_trans _ huv hu0
    obtain ⟨x, -, hxn, hxA⟩ := h.actN' A hA
    refine ⟨x, ?_⟩
    rw [hs2f, C.conj_elt hxn, hxA, hAz, C.elt_vec hu]
  exact sq_fusion_of_phase1 (F := C.Fsub hQ) (E := C.E) (f := f) (s := s) hf hE_inv hF_conj hn

theorem exists_fus {s : G} (hQ : Q0Facts) (hf : orderOf f = 4)
    (hn : ¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹) (hs2z : s ^ 2 = C.elt zpVec)
    {m : G} (hm : m ∈ normalizer (C.E : Set G)) :
    ∃ w ∈ fVecs, C.mat m *ᵥ tVec = tVec + w := by
  have hf2 : f ^ 2 = C.elt tVec := h.f2_eq hQ
  have hmE : m⁻¹⁻¹ * f ^ 2 * m⁻¹ ∈ C.E := by
    rw [inv_inv, hf2, C.conj_elt hm]
    exact C.elt_mem _
  obtain ⟨u, ⟨huE, huv⟩, hu⟩ := h.sq_fusion hQ hf hn hs2z m⁻¹ hmE
  refine ⟨C.vec u, huv, ?_⟩
  have h1 : C.vec (m * f ^ 2 * m⁻¹) = C.mat m *ᵥ tVec := by
    rw [hf2, C.conj_elt hm, C.vec_elt]
  rw [inv_inv] at hu
  rw [← h1, hu, hf2, C.vec_mul (C.elt_mem _) huE, C.vec_elt]

theorem mat_mem_sList {s n₀ : G} (hQ : Q0Facts) (hn0 : n₀ ∈ normalizer (C.E : Set G))
    (hn0t : n₀ * f ^ 2 * n₀⁻¹ = s ^ 2) (hs2z : s ^ 2 = C.elt zpVec)
    (hfus : ∀ m ∈ normalizer (C.E : Set G), ∃ w ∈ fVecs, C.mat m *ᵥ tVec = tVec + w)
    {m : G} (hm : m ∈ normalizer (C.E : Set G)) : C.mat m ∈ sList (C.mat n₀) := by
  have hf2 : f ^ 2 = C.elt tVec := h.f2_eq hQ
  obtain ⟨w, hw, hmw⟩ := hfus m hm
  by_cases hw0 : w = 0
  · subst hw0
    have hc : m * f ^ 2 = f ^ 2 * m := by
      have h1 : m * f ^ 2 * m⁻¹ = f ^ 2 := by rw [hf2, C.conj_elt hm, hmw, add_zero]
      calc m * f ^ 2 = (m * f ^ 2 * m⁻¹) * m := by group
        _ = f ^ 2 * m := by rw [h1]
    exact List.mem_append_left _ (h.actN m hc hm)
  · obtain ⟨r, hr, hrz⟩ := hQ.reps_spec w hw hw0
    obtain ⟨x, -, hxn, hxr⟩ := h.actN' r (hQ.reps_mem r hr)
    have hxn0 : x * n₀ ∈ normalizer (C.E : Set G) := mul_mem hxn hn0
    have h1 : (x * n₀) * f ^ 2 * (x * n₀)⁻¹ = m * f ^ 2 * m⁻¹ := by
      have e1 : (x * n₀) * f ^ 2 * (x * n₀)⁻¹ = x * (n₀ * f ^ 2 * n₀⁻¹) * x⁻¹ := by group
      rw [e1, hn0t, hs2z, C.conj_elt hxn, hxr, hrz, hf2, C.conj_elt hm, hmw]
    have hc : (x * n₀)⁻¹ * m * f ^ 2 = f ^ 2 * ((x * n₀)⁻¹ * m) := by
      calc (x * n₀)⁻¹ * m * f ^ 2
          = (x * n₀)⁻¹ * (m * f ^ 2 * m⁻¹) * m := by group
        _ = (x * n₀)⁻¹ * ((x * n₀) * f ^ 2 * (x * n₀)⁻¹) * m := by rw [h1]
        _ = f ^ 2 * ((x * n₀)⁻¹ * m) := by group
    have hq := h.actN _ hc (mul_mem (inv_mem hxn0) hm)
    have e2 : m = (x * n₀) * ((x * n₀)⁻¹ * m) := by group
    have hmat : C.mat m = r * C.mat n₀ * C.mat ((x * n₀)⁻¹ * m) := by
      conv_lhs => rw [e2]
      rw [C.mat_mul hxn0 (mul_mem (inv_mem hxn0) hm), C.mat_mul hxn hn0, hxr]
    rw [hmat]
    exact List.mem_append_right _
      (List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨_, hq, rfl⟩⟩)

theorem exists_mat_of_mem_sList {n₀ : G} (hn0 : n₀ ∈ normalizer (C.E : Set G)) (hQ : Q0Facts)
    {B : M4} (hB : B ∈ sList (C.mat n₀)) : ∃ m ∈ normalizer (C.E : Set G), C.mat m = B := by
  rcases List.mem_append.1 hB with hB | hB
  · obtain ⟨x, -, hxn, hx⟩ := h.actN' B hB
    exact ⟨x, hxn, hx⟩
  · obtain ⟨r, hr, hB⟩ := List.mem_flatMap.1 hB
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hB
    obtain ⟨xr, -, hxr, hxrm⟩ := h.actN' r (hQ.reps_mem r hr)
    obtain ⟨xq, -, hxq, hxqm⟩ := h.actN' q hq
    refine ⟨xr * n₀ * xq, mul_mem (mul_mem hxr hn0) hxq, ?_⟩
    rw [C.mat_mul (mul_mem hxr hn0) hxq, C.mat_mul hxr hn0, hxrm, hxqm]

end Sect8Hyp

end CFSG.EvenSporadicStandard.TwoHS
