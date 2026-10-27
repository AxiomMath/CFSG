module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Iwasawa
public import CFSG.LieType.Universal.Spin.Forms

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement

variable {K : Type} [Field K] [IsF2 K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} [FiniteDimensional K V]

theorem exists_singular_orth_three (hd : 6 ≤ finrank K V) (u w f : V) :
    ∃ x : V, x ≠ 0 ∧ Q x = 0 ∧ polar Q u x = 0 ∧ polar Q w x = 0 ∧ polar Q f x = 0 := by
  set ψ : V →ₗ[K] K × (K × K) := (polarBilin Q u).prod ((polarBilin Q w).prod (polarBilin Q f))
    with hψ
  have h2 := LinearMap.finrank_range_add_finrank_ker ψ
  have h3 : finrank K (LinearMap.range ψ) ≤ 3 := (Submodule.finrank_le _).trans (by simp)
  obtain ⟨x, hx0, hxQ⟩ := exists_ne_zero_map_eq_zero' (Q := Q.restrict (LinearMap.ker ψ))
    (by omega)
  have hxmem := x.2
  rw [LinearMap.mem_ker] at hxmem
  have h1 := congrArg Prod.fst hxmem
  have h2' := congrArg (fun p => p.2.1) hxmem
  have h3' := congrArg (fun p => p.2.2) hxmem
  simp only [hψ, LinearMap.prod_apply, Prod.fst_zero, Prod.snd_zero] at h1 h2' h3'
  exact ⟨x, fun h => hx0 (Subtype.ext h), hxQ, h1, h2', h3'⟩

theorem eichler_mem_commutator_E_of_map_eq_one (hQ : (polarBilin Q).Nondegenerate)
    (hd : 6 ≤ finrank K V) {u w : V} (hu0 : u ≠ 0) (hu : Q u = 0) (huw : polar Q u w = 0)
    (hw : Q w = 1) :
    eichler Q u w ∈ ⁅elementaryGroup Q, elementaryGroup Q⁆ := by
  have hw0 : w ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at hw; exact zero_ne_one hw
  have huwne : u ≠ w := fun h0 => by rw [← h0, hu] at hw; exact zero_ne_one hw
  obtain ⟨f, hf⟩ := exists_polar_prescribed hQ (linearIndependent_pair_of_ne hu0 hw0 huwne)
    ![1, 0]
  have hf1 : polar Q u f = 1 := by simpa using hf 0
  have hf0 : polar Q w f = 0 := by simpa using hf 1
  obtain ⟨x, hx0, hxQ, hux, hwx, hfx⟩ := exists_singular_orth_three (Q := Q) hd u w f
  have hxu : x ≠ u := fun h0 => by
    rw [h0, polar_comm, hf1] at hfx
    exact one_ne_zero hfx
  have hli : LinearIndependent K ![u, x, w] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hg
    have hg0 : g 0 = 0 := by
      have := congrArg (fun z => polar Q z f) hg
      simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, hf1, hf0,
        polar_comm Q x f, hfx] at this
      simpa using this
    rw [hg0, zero_smul, zero_add] at hg
    have hxw : x ≠ w := fun h0 => by rw [← h0, hxQ] at hw; exact zero_ne_one hw
    have key : ∀ i : Fin 3, g i = 0 := by
      intro i
      fin_cases i
      · exact hg0
      · rcases IsF2.eq_zero_or_one (g 1) with h1 | h1
        · exact h1
        · rcases IsF2.eq_zero_or_one (g 2) with h2 | h2
          · rw [h1, h2, one_smul, zero_smul, add_zero] at hg
            exact absurd hg hx0
          · rw [h1, h2, one_smul, one_smul] at hg
            exact absurd (eq_neg_of_add_eq_zero_left hg |>.trans
              (neg_eq_self_of_two_eq_zero (K := K) IsF2.two_eq_zero w)) hxw
      · rcases IsF2.eq_zero_or_one (g 2) with h2 | h2
        · exact h2
        · rcases IsF2.eq_zero_or_one (g 1) with h1 | h1
          · rw [h1, h2, zero_smul, one_smul, zero_add] at hg
            exact absurd hg hw0
          · rw [h1, h2, one_smul, one_smul] at hg
            exact absurd (eq_neg_of_add_eq_zero_left hg |>.trans
              (neg_eq_self_of_two_eq_zero (K := K) IsF2.two_eq_zero w)) hxw
    exact key
  obtain ⟨v, hv⟩ := exists_polar_prescribed hQ hli ![0, 1, 1]
  have hv1 : polar Q u v = 0 := by simpa using hv 0
  have hv2 : polar Q x v = 1 := by simpa using hv 1
  have hv3 : polar Q w v = 1 := by simpa using hv 2
  have hxw : polar Q x w = 0 := by rw [polar_comm, hwx]
  have hgE := eichler_mem_elementaryGroup Q x w
  have hgO := eichler_mem_orthogonalGroup Q x w
  have hgu : eichler Q x w u = u :=
    eichler_apply_of_polar_eq_zero hux huw
  have hgv : eichler Q x w v - v = w := by
    rw [eichler_apply hxQ hxw, polar_comm Q v x, hv2, polar_comm Q v w, hv3, hw, one_smul,
      mul_one, IsF2.one_add_one, zero_smul]
    abel
  have := Subgroup.commutator_mem_commutator hgE (eichler_mem_elementaryGroup Q u v)
  rwa [commutatorElement_eichler hgO hgu hv1, hgv] at this

theorem eichler_mem_commutator_E (hQ : (polarBilin Q).Nondegenerate) (hd : 6 ≤ finrank K V)
    {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0) :
    eichler Q u w ∈ ⁅elementaryGroup Q, elementaryGroup Q⁆ := by
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact one_mem _
  by_cases hw : Q w = 0
  · obtain ⟨a, hua, hwa, ha⟩ := exists_polar_eq_zero_map_ne_zero hQ (by omega) u w
    have ha1 := IsF2.eq_one_of_ne_zero ha
    have huwa : polar Q u (w - a) = 0 := by rw [polar_sub_right, huw, hua, sub_zero]
    have hQwa : Q (w - a) = 1 := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, hw, ha1,
        hwa, neg_zero, add_zero, zero_add]
    have : eichler Q u w = eichler Q u a * eichler Q u (w - a) := by
      rw [eichler_mul hua huwa, add_sub_cancel]
    rw [this]
    exact mul_mem (eichler_mem_commutator_E_of_map_eq_one hQ hd hu0 hu hua ha1)
      (eichler_mem_commutator_E_of_map_eq_one hQ hd hu0 hu huwa hQwa)
  · exact eichler_mem_commutator_E_of_map_eq_one hQ hd hu0 hu huw (IsF2.eq_one_of_ne_zero hw)

theorem commutator_elementaryGroup_eq_top_f2 (hQ : (polarBilin Q).Nondegenerate)
    (hd : 6 ≤ finrank K V) : commutator (elementaryGroup Q) = ⊤ := by
  have h1 : elementaryGroup Q ≤ ⁅elementaryGroup Q, elementaryGroup Q⁆ :=
    elementaryGroup_le_of_eichler_mem fun u w hu huw => eichler_mem_commutator_E hQ hd hu huw
  have h2 : ⁅elementaryGroup Q, elementaryGroup Q⁆ = elementaryGroup Q :=
    le_antisymm (Subgroup.commutator_le_self _) h1
  have h3 := Subgroup.map_subtype_commutator (elementaryGroup Q)
  have h4 : (⊤ : Subgroup (elementaryGroup Q)).map (elementaryGroup Q).subtype =
      elementaryGroup Q := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rw [h2] at h3
  exact Subgroup.map_injective (elementaryGroup Q).subtype_injective (h3.trans h4.symm)

theorem isSimpleGroup_elementaryGroup_of_six_le_finrank (hQ : (polarBilin Q).Nondegenerate)
    (hd : 6 ≤ finrank K V) : IsSimpleGroup (elementaryGroup Q) :=
  isSimpleGroup_elementaryGroup_of_perfect hQ (by omega) (Or.inl (by omega))
    (commutator_elementaryGroup_eq_top_f2 hQ hd)

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
