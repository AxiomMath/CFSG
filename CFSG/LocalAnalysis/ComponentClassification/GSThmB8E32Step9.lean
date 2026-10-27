module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Step8

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

namespace Eight

open S6M

namespace E32Conf

variable {X : Type} [Group X] [Finite X] (C : E32Conf X)

theorem conj_E0_mem (n : ↥C.N) {e : X} (he : e ∈ C.E0) : (n : X) * e * (n : X)⁻¹ ∈ C.E0 := by
  obtain ⟨v, hv, rfl⟩ := C.mem_E0_iff.mp he
  rw [C.θ_conj]
  exact C.mem_E0_iff.mpr ⟨_, (isEven_act _ _).mpr hv, rfl⟩

theorem W_le_normalizer_E0 : C.W ≤ normalizer (C.E0 : Set X) :=
  le_normalizer_of_conj fun w hw _ he => C.conj_E0_mem ⟨w, hw.2⟩ he

theorem mul_mem_E0 {e e' : X} (he : e ∈ C.E) (he' : e' ∈ C.E) (h0 : e ∉ C.E0)
    (h0' : e' ∉ C.E0) : e * e' ∈ C.E0 := by
  obtain ⟨v, rfl⟩ := C.mem_E_iff.mp he
  obtain ⟨w, rfl⟩ := C.mem_E_iff.mp he'
  have hv : ¬ IsEven v := fun h => h0 (C.mem_E0_iff.mpr ⟨v, h, rfl⟩)
  have hw : ¬ IsEven w := fun h => h0' (C.mem_E0_iff.mpr ⟨w, h, rfl⟩)
  rw [← C.θ_add]
  refine C.mem_E0_iff.mpr ⟨v + w, ?_, rfl⟩
  simp only [IsEven, Pi.add_apply, Finset.sum_add_distrib] at *
  rcases zmod2_cases (∑ i, v i) with h1 | h1 <;> rcases zmod2_cases (∑ i, w i) with h2 | h2
  · exact absurd h1 hv
  · exact absurd h1 hv
  · exact absurd h2 hw
  · rw [h1, h2]
    rfl

theorem Klist_even {v : V5} (hv : v ∈ Klist) : C.θ v ∈ C.E0 := by
  have h1 := List.all_eq_true.mp Vlist_fix.2 v hv
  simp only [Bool.and_eq_true] at h1
  exact C.mem_E0_iff.mpr ⟨v, isEvenB_iff.mp h1.1, rfl⟩

theorem conj_E0_le_W {y : X} (hyN : y ∈ normalizer (C.W : Set X)) : conjugate C.E0 y ≤ C.W :=
  C.conj_le_W C.E0_le_E hyN

section Step9

variable {y : X} (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)
include hyU hyN hyW

theorem card_inf_four : Nat.card ↥(conjugate C.E y ⊓ C.E) = 4 := by
  have hcard := C.card_inf_mul hyN
  rw [C.range_ψ_eq hyU hyN hyW, card_Vsub] at hcard
  omega

theorem K_le_E0y {v : V5} (hv : v ∈ Klist) : C.θ v ∈ conjugate C.E0 y := by
  have hcard := C.card_inf_mul0 hyN
  rw [C.range_ψ0_eq hyU hyN hyW, card_V0sub] at hcard
  have h4 : Nat.card ↥(conjugate C.E0 y ⊓ C.E) = 4 := by omega
  have hle : conjugate C.E0 y ⊓ C.E ≤ conjugate C.E y ⊓ C.E := inf_le_inf_right _ (C.conj_E0_le y)
  have heq : conjugate C.E0 y ⊓ C.E = conjugate C.E y ⊓ C.E :=
    eq_of_le_of_card_ge hle (by rw [C.card_inf_four hyU hyN hyW, h4])
  have hK : C.θ v ∈ conjugate C.E y ⊓ C.E := (C.mem_inf_iff hyU hyN hyW).mpr ⟨v, hv, rfl⟩
  rw [← heq] at hK
  exact (Subgroup.mem_inf.mp hK).1

theorem inf_le_E0 {k : X} (hk : k ∈ conjugate C.E y ⊓ C.E) : k ∈ C.E0 := by
  obtain ⟨v, hv, rfl⟩ := (C.mem_inf_iff hyU hyN hyW).mp hk
  exact C.Klist_even hv

theorem mem_or_mem_of_sq {x : X} (hx : x ∈ C.E0 ⊔ conjugate C.E0 y) (hx2 : x * x = 1) :
    x ∈ C.E0 ∨ x ∈ conjugate C.E0 y := by
  have hle : conjugate C.E0 y ≤ normalizer (C.E0 : Set X) :=
    (C.conj_E0_le_W hyN).trans C.W_le_normalizer_E0
  have hx' : x ∈ ((C.E0 : Set X) * (conjugate C.E0 y : Set X)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hx
  obtain ⟨e, he, f, hf, rfl⟩ := Set.mem_mul.mp hx'
  have hfW := C.conj_E0_le_W hyN hf
  have hfE : f ∈ conjugate C.E y := C.conj_E0_le y hf
  have he2 := C.E_sq (C.E0_le_E he)
  have hf2 := C.conj_E_sq hfE
  have hfe : f * e = e * f := by
    calc f * e = (e * e) * (f * e) * (f * f) := by rw [he2, hf2]; group
      _ = e * (e * f * (e * f)) * f := by group
      _ = e * f := by rw [hx2]; group
  obtain ⟨v, hv, rfl⟩ := C.mem_E0_iff.mp he
  have hfix : act (C.π ⟨f, hfW.2⟩) v = v := (C.comm_iff ⟨f, hfW.2⟩ v).mp hfe
  have hπ : C.π ⟨f, hfW.2⟩ ∈ V0sub := by
    rw [← C.range_ψ0_eq hyU hyN hyW]
    exact (C.mem_range_ψ C.E0_le_E hyN).mpr ⟨f, hf, rfl⟩
  by_cases h1 : C.π ⟨f, hfW.2⟩ = 1
  · left
    have hfK : f ∈ conjugate C.E y ⊓ C.E :=
      Subgroup.mem_inf.mpr ⟨hfE, C.π_ker ⟨f, hfW.2⟩ hfW.1 h1⟩
    exact mul_mem he (C.inf_le_E0 hyU hyN hyW hfK)
  · right
    have h2 := List.all_eq_true.mp V0list_evenfix _ hπ
    simp only [Bool.or_eq_true, beq_iff_eq, h1, false_or] at h2
    have h3 := List.all_eq_true.mp h2 v (mem_allV v)
    simp only [isEvenB_iff.mpr hv, veq_iff.mpr hfix, Bool.and_self, Bool.not_true,
      Bool.false_or, List.contains_iff_mem] at h3
    exact mul_mem (C.K_le_E0y hyU hyN hyW h3) hf

end Step9

@[expose] noncomputable def pre0 : Subgroup X := (V0sub.comap C.π).map C.N.subtype

theorem mem_pre0 {x : X} : x ∈ C.pre0 ↔ ∃ hx : x ∈ C.N, C.π ⟨x, hx⟩ ∈ V0sub := by
  constructor
  · rintro ⟨⟨x, hx⟩, h, rfl⟩
    exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

section Step9b

variable {y u : X} (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)
  (huU : u ∈ C.U) (huN : u ∈ normalizer (C.W : Set X)) (huW : u ∉ C.W)
include hyU hyN hyW huU huN huW

theorem mem_K_of_mem_inf (hw : u * y⁻¹ ∉ C.W) {x : X}
    (hx : x ∈ conjugate C.E u ⊓ conjugate C.E y) : ∃ v ∈ Klist, C.θ v = x := by
  have hwU : u * y⁻¹ ∈ C.U := mul_mem huU (inv_mem hyU)
  have hwN : u * y⁻¹ ∈ normalizer (C.W : Set X) := mul_mem huN (inv_mem hyN)
  have hconj : conjugate (conjugate C.E (u * y⁻¹) ⊓ C.E) y =
      conjugate C.E u ⊓ conjugate C.E y := by
    unfold conjugate
    rw [map_inf _ _ _ (MulAut.conj y⁻¹).injective]
    congr 1
    rw [← conjugate, ← conjugate, ← conjugate, conjugate_conjugate, inv_mul_cancel_right]
  have h4 : Nat.card ↥(conjugate C.E u ⊓ conjugate C.E y) = 4 := by
    rw [← hconj, Eight.card_conjugate_eq, C.card_inf_four hwU hwN hw]
  have hKsub : ∀ v ∈ Klist, C.θ v ∈ conjugate C.E u ⊓ conjugate C.E y := by
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_inf.mp ((C.mem_inf_iff huU huN huW).mpr ⟨v, hv, rfl⟩)).1
    · exact (Subgroup.mem_inf.mp ((C.mem_inf_iff hyU hyN hyW).mpr ⟨v, hv, rfl⟩)).1
  have hle : C.θ '' {v | v ∈ Klist} ⊆ (conjugate C.E u ⊓ conjugate C.E y : Subgroup X) := by
    rintro _ ⟨v, hv, rfl⟩
    exact hKsub v hv
  have heq : C.θ '' {v | v ∈ Klist} = (conjugate C.E u ⊓ conjugate C.E y : Subgroup X) := by
    refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ C.θ_injective, Klist_ncard, ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, h4]
  have : x ∈ C.θ '' {v | v ∈ Klist} := by
    rw [heq]
    exact hx
  obtain ⟨v, hv, rfl⟩ := this
  exact ⟨v, hv, rfl⟩

theorem mul_inv_mem_W : u * y⁻¹ ∈ C.W := by
  by_contra hw
  set A := conjugate C.E u with hA
  set Q0 := C.E0 ⊔ conjugate C.E0 y with hQ0
  have hA32 : Nat.card A = 32 := by rw [hA, Eight.card_conjugate_eq, C.card_E]
  have h1 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ C.pre0) := by
    refine Eight.card_le_two_mul_card_inf fun x hx x' hx' hxP hx'P => ?_
    have hxW := C.conj_le_W le_rfl huN hx
    have hx'W := C.conj_le_W le_rfl huN hx'
    have hπx : C.π ⟨x, hxW.2⟩ ∈ Vsub := by
      rw [← C.range_ψ_eq huU huN huW]
      exact (C.mem_range_ψ le_rfl huN).mpr ⟨x, hx, rfl⟩
    have hπx' : C.π ⟨x', hx'W.2⟩ ∈ Vsub := by
      rw [← C.range_ψ_eq huU huN huW]
      exact (C.mem_range_ψ le_rfl huN).mpr ⟨x', hx', rfl⟩
    have hn : C.π ⟨x, hxW.2⟩ ∉ V0list := fun h => hxP (C.mem_pre0.mpr ⟨hxW.2, h⟩)
    have hn' : C.π ⟨x', hx'W.2⟩ ∉ V0list := fun h => hx'P (C.mem_pre0.mpr ⟨hx'W.2, h⟩)
    have h2 := List.all_eq_true.mp (List.all_eq_true.mp Vlist_coset _ hπx) _ hπx'
    simp only [Bool.or_eq_true, List.contains_iff_mem, hn, hn', false_or] at h2
    refine C.mem_pre0.mpr ⟨mul_mem (inv_mem hxW.2) hx'W.2, ?_⟩
    rw [show (⟨x⁻¹ * x', mul_mem (inv_mem hxW.2) hx'W.2⟩ : ↥C.N) =
      (⟨x, hxW.2⟩ : ↥C.N)⁻¹ * ⟨x', hx'W.2⟩ from rfl, map_mul, map_inv]
    exact h2
  have hdecomp : ∀ x ∈ A ⊓ C.pre0, ∃ e ∈ C.E, ∃ f ∈ conjugate C.E0 y, x = e * f := by
    intro x hx
    obtain ⟨hxA, hxP⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxN, hπ⟩ := C.mem_pre0.mp hxP
    rw [← C.range_ψ0_eq hyU hyN hyW] at hπ
    obtain ⟨f, hf, hfx⟩ := (C.mem_range_ψ C.E0_le_E hyN).mp hπ
    have hfW := C.conj_E0_le_W hyN hf
    have hxW := C.conj_le_W le_rfl huN hxA
    have h3 : C.π ⟨x * f⁻¹, mul_mem hxN (inv_mem hfW.2)⟩ = 1 := by
      rw [show (⟨x * f⁻¹, mul_mem hxN (inv_mem hfW.2)⟩ : ↥C.N) = ⟨x, hxN⟩ * ⟨f, hfW.2⟩⁻¹ from rfl,
        map_mul, map_inv, ← hfx]
      exact mul_inv_cancel _
    refine ⟨x * f⁻¹, C.π_ker _ (mul_mem (Subgroup.mem_inf.mp hxW).1
      (inv_mem (Subgroup.mem_inf.mp hfW).1)) h3, f, hf, by group⟩
  have h2 : Nat.card ↥(A ⊓ C.pre0) ≤ 2 * Nat.card ↥(A ⊓ C.pre0 ⊓ Q0) := by
    refine Eight.card_le_two_mul_card_inf fun x hx x' hx' hxQ hx'Q => ?_
    obtain ⟨e, he, f, hf, rfl⟩ := hdecomp x hx
    obtain ⟨e', he', f', hf', rfl⟩ := hdecomp x' hx'
    have he0 : e ∉ C.E0 := fun h => hxQ (mul_mem (mem_sup_left h) (mem_sup_right hf))
    have he0' : e' ∉ C.E0 := fun h => hx'Q (mul_mem (mem_sup_left h) (mem_sup_right hf'))
    have hfW := C.conj_E0_le_W hyN hf
    have hee : e⁻¹ * e' ∈ C.E0 := by
      rw [inv_eq_of_mul_eq_one_right (C.E_sq he)]
      exact C.mul_mem_E0 he he' he0 he0'
    have hconj : f⁻¹ * (e⁻¹ * e') * f⁻¹⁻¹ ∈ C.E0 :=
      C.conj_E0_mem ⟨f⁻¹, inv_mem hfW.2⟩ hee
    rw [show (e * f)⁻¹ * (e' * f') = (f⁻¹ * (e⁻¹ * e') * f⁻¹⁻¹) * (f⁻¹ * f') by group]
    exact mul_mem (mem_sup_left hconj) (mem_sup_right (mul_mem (inv_mem hf) hf'))
  have h3 : Nat.card ↥(A ⊓ C.pre0 ⊓ Q0) ≤ 4 := by
    rw [← Klist_ncard]
    refine C.card_le_ncard _ fun x hx => ?_
    obtain ⟨hx1, hxQ⟩ := Subgroup.mem_inf.mp hx
    have hxA := (Subgroup.mem_inf.mp hx1).1
    have hx2 := C.conj_E_sq hxA
    rcases C.mem_or_mem_of_sq hyU hyN hyW hxQ hx2 with h | h
    · obtain ⟨v, hv, hvx⟩ := (C.mem_inf_iff huU huN huW).mp
        (Subgroup.mem_inf.mpr ⟨hxA, C.E0_le_E h⟩)
      exact ⟨v, hv, hvx⟩
    · exact C.mem_K_of_mem_inf hyU hyN hyW huU huN huW hw
        (Subgroup.mem_inf.mpr ⟨hxA, C.conj_E0_le y h⟩)
  omega

end Step9b

end E32Conf

end Eight

end CFSG.ComponentClassification.GSThmB
