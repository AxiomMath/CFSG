module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Orbit

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix Finset

variable {G : Type*} [Group G]

@[expose] def Tα (C : ECoord G) {α : M4} (hT : TFacts α) : Subgroup G :=
  Tsub C (tList α) hT.one_mem hT.mul_mem hT.inv_mem

@[expose] def Kα (C : ECoord G) {α : M4} (hT : TFacts α) : Subgroup G :=
  Tα C hT ⊓ centralizer {a : G | a ∈ C.E ∧ a * a = 1}

theorem mem_Kα {C : ECoord G} {α : M4} {hT : TFacts α} {x : G} :
    x ∈ Kα C hT ↔ x ∈ Tα C hT ∧ ∀ a ∈ C.E, a * a = 1 → a * x = x * a := by
  simp only [Kα, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_ofPred_eq, and_imp]

namespace ECoord

variable (C : ECoord G)

theorem mul_self_eq_one_iff {x : G} (hx : x ∈ C.E) : x * x = 1 ↔ C.vec x + C.vec x = 0 := by
  constructor
  · intro h
    rw [← C.vec_mul hx hx, h, C.vec_one]
  · intro h
    rw [← C.elt_vec (C.E.mul_mem hx hx), C.vec_mul hx hx, h, C.elt_zero]

theorem Fsub_mul_self (hQ : Q0Facts) {x : G} (hx : x ∈ C.Fsub hQ) : x * x = 1 :=
  (C.mul_self_eq_one_iff hx.1).2 (hQ.f_two _ hx.2)

end ECoord

section SylowFields

variable [Finite G] {C : ECoord G} {f n : G} {S₀ : Subgroup G} (h : Sect8Hyp C f n S₀)
  (hQ : Q0Facts) {α : M4} (hT : TFacts α)
  (hS : ∀ m ∈ normalizer (C.E : Set G), C.mat m ∈ sList α)
  (hR : ∀ B ∈ sList α, ∃ m ∈ normalizer (C.E : Set G), C.mat m = B)
include h hQ hT hS hR

theorem realize_T : ∀ A ∈ tList α, ∃ z ∈ Tα C hT, C.mat z = A := by
  intro A hA
  obtain ⟨m, hm, hmA⟩ := hR A (hT.sub_s A hA)
  exact ⟨m, ⟨hm, hmA ▸ hA⟩, hmA⟩

theorem T_pgroup : IsPGroup 2 (Tα C hT) := by
  rintro ⟨x, hx⟩
  refine ⟨9, ?_⟩
  have hxn := hx.1
  have h128 : C.mat x ^ 128 = 1 := hT.pow128 _ hx.2
  have hm : C.mat (x ^ 128) = 1 := by rw [C.mat_pow hxn, h128]
  have hE : x ^ 128 ∈ C.E := h.mem_E_of_mat_eq_one (pow_mem hxn 128) hm
  have h4 := C.pow_four hE
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  calc x ^ 2 ^ 9 = (x ^ 128) ^ 4 := by rw [← pow_mul]; norm_num
    _ = 1 := h4

theorem T_star : ∀ x ∈ Tα C hT, x * x = 1 → (tConjClass (Tα C hT) x).ncard ≤ 4 → x ∈ C.E := by
  intro x hx hxx hcl
  by_contra hxE
  have hB1 : C.mat x ≠ 1 := fun h1 => hxE (h.mem_E_of_mat_eq_one hx.1 h1)
  have hBB : C.mat x * C.mat x = 1 := by rw [← C.mat_mul hx.1 hx.1, hxx, C.mat_one]
  have h5 := hT.star _ hx.2 hB1 hBB
  have h6 : ∑ B' ∈ clSet (tList α) (C.mat x), (imSet B').card ≤
      (tConjClass (Tα C hT) x).ncard := class_ge (realize_T h hQ hT hS hR) hx
  omega

theorem T_F_small : ∀ x ∈ C.Fsub hQ, (tConjClass (Tα C hT) x).ncard ≤ 4 := by
  intro x hx
  have h1 : (tConjClass (Tα C hT) x).ncard ≤ ((tList α).map fun A => A *ᵥ C.vec x).toFinset.card :=
    class_le_orbit hx.1
  exact h1.trans (hT.fsmall _ hx.2)

theorem T_tF_large (hf2 : f ^ 2 = C.elt tVec) :
    ∀ u ∈ C.Fsub hQ, ¬ (tConjClass (Tα C hT) (f ^ 2 * u)).ncard ≤ 4 := by
  intro u hu hle
  have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
  have hx : f ^ 2 * u ∈ C.E := C.E.mul_mem hf2E hu.1
  have hv : C.vec (f ^ 2 * u) = tVec + C.vec u := by
    rw [C.vec_mul hf2E hu.1, hf2, C.vec_elt]
  have h1 : ((tList α).map fun A => A *ᵥ C.vec (f ^ 2 * u)).toFinset.card ≤
      (tConjClass (Tα C hT) (f ^ 2 * u)).ncard := orbit_le_class (realize_T h hQ hT hS hR) hx
  rw [hv] at h1
  have h2 := hT.tflarge _ hu.2
  omega

theorem T_CF_sq : ∀ x ∈ Tα C hT, (∀ a ∈ C.Fsub hQ, x * a = a * x) → x * x ∈ C.E := by
  intro x hx hc
  apply h.mem_E_of_mat_eq_one (mul_mem hx.1 hx.1)
  rw [C.mat_mul hx.1 hx.1]
  refine hT.cfsq _ hx.2 fun v hv => ?_
  have hvE : C.elt v ∈ C.Fsub hQ := ⟨C.elt_mem v, by rw [C.vec_elt]; exact hv⟩
  have h1 := hc _ hvE
  have h2 : x * C.elt v * x⁻¹ = C.elt v := by rw [h1]; group
  rw [C.conj_elt hx.1] at h2
  exact C.elt_injective h2

theorem T_K_def : ∀ x ∈ Tα C hT, (∀ a ∈ C.E, a * a = 1 → x * a = a * x) → x ∈ Kα C hT := by
  intro x hx hc
  exact mem_Kα.2 ⟨hx, fun a ha haa => (hc a ha haa).symm⟩

theorem K_mat {x : G} (hx : x ∈ Kα C hT) : C.mat x = 1 ∨ C.mat x = -1 := by
  obtain ⟨hxT, hxc⟩ := mem_Kα.1 hx
  refine hT.kker _ hxT.2 fun v hv => ?_
  have hvE : C.elt v ∈ C.E := C.elt_mem v
  have hvv : C.elt v * C.elt v = 1 := by rw [← C.elt_add, hv, C.elt_zero]
  have h1 := hxc _ hvE hvv
  have h2 : x * C.elt v * x⁻¹ = C.elt v := by rw [← h1]; group
  rw [C.conj_elt hxT.1] at h2
  exact C.elt_injective h2

theorem K_mat_neg {x : G} (hx : x ∈ Kα C hT) (hxE : x ∉ C.E) : C.mat x = -1 := by
  rcases K_mat h hQ hT hS hR hx with h1 | h1
  · exact absurd (h.mem_E_of_mat_eq_one (mem_Kα.1 hx).1.1 h1) hxE
  · exact h1

theorem T_K_cent : ∀ x ∈ Kα C hT, x * f = f * x → x ∈ C.E := by
  intro x hx hxf
  by_contra hxE
  have hm := K_mat_neg h hQ hT hS hR hx hxE
  have hxn := (mem_Kα.1 hx).1.1
  have hfe : f = C.elt fVec := by rw [← h.vec_f, C.elt_vec h.f_mem]
  have h1 : x * C.elt fVec * x⁻¹ = C.elt fVec := by
    rw [← hfe]
    calc x * f * x⁻¹ = (f * x) * x⁻¹ := by rw [hxf]
      _ = f := by group
  rw [C.conj_elt hxn, hm] at h1
  have h2 := C.elt_injective h1
  simp only [neg_mulVec, one_mulVec] at h2
  exact hQ.neg_f h2

end SylowFields

end CFSG.EvenSporadicStandard.TwoHS
