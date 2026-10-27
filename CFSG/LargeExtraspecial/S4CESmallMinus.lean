module

public import CFSG.LargeExtraspecial.S4CESmallTool
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.LargeExtraspecial.S4Lin
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  (exists_symplectic_basis_prescribed_pair)
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem card_omegaGroup_of_minus_four (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    Nat.card (omegaGroup Q hQ) = 60 := by
  obtain ⟨-, -, -, hidx, -, h4', -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ (Or.inl h4)
      (fun U hU => hmin U (by rw [hU, h4]))
  obtain ⟨F, _, _, D, ψ, ρ, -, -, -, hrange, hcard⟩ := h4' h4
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hOdef
  set N := ⁅O, O⁆ with hNdef
  have hNΩ : N ≤ omegaGroup Q hQ := by
    rw [hNdef, commutator_le]
    intro g hg k hk
    have hker : (⟨⁅g, k⁆, commutator_le_self O (commutator_mem_commutator hg hk)⟩ : O) ∈
        (dicksonHom Q hQ).ker := by
      rw [MonoidHom.mem_ker]
      have : (⟨⁅g, k⁆, commutator_le_self O (commutator_mem_commutator hg hk)⟩ : O) =
          ⁅(⟨g, hg⟩ : O), ⟨k, hk⟩⁆ := rfl
      rw [this, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    rw [dicksonHom_ker, mem_subgroupOf] at hker
    exact hker
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hrel := relIndex_mul_relIndex N (omegaGroup Q hQ) O hNΩ (omegaGroup_le Q hQ)
  rw [relIndex_omegaGroup Q hQ, show N.relIndex O = 2 from hidx] at hrel
  have hNeq : N = omegaGroup Q hQ := le_antisymm hNΩ (relIndex_eq_one.mp (by omega))
  rw [hrange, hNeq, Nat.card_zmod] at hcard
  rw [hcard]
  norm_num

omit [FiniteDimensional (ZMod 2) V] in
theorem map_ne_zero_of_minus
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0) {a x : V}
    (ha : Q a = 0) (hax : polar Q a x = 0) (hli : LinearIndependent (ZMod 2) ![a, x]) :
    Q x ≠ 0 := by
  intro hx
  obtain ⟨u, hu, hu0⟩ := hmin (Submodule.span (ZMod 2) (Set.range ![a, x]))
    (by rw [finrank_span_eq_card hli, Fintype.card_fin])
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hu
  apply hu0
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right, ha, hx, hax]
  simp

theorem le_commutator_pointRadical_of_minus_four {K : Type*} [Group K]
    {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0)
    (ha0 : a ≠ 0) (hQa : Q a = 0) (h : CEHyp π E a (omegaGroup Q hQ) (pointRadical Q a)) :
    pointRadical Q a ≤ ⁅pointRadical Q a, stabIn (omegaGroup Q hQ) a⁆ := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  have halt : Q.polarBilin.IsAlt := fun x => by
    rw [polarBilin_apply_apply]
    exact polar_self_eq_zero Q x
  obtain ⟨b, hb⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hQ ha0
  have hab : polar Q a b = 1 := zmod2_eq_one_of_ne_zero hb
  obtain ⟨m, e, hm, h11, h22, h12, he0, hf0⟩ :=
    exists_symplectic_basis_prescribed_pair
      Q.polarBilin halt hQ a b hab
  obtain rfl : m = 1 := by omega
  set c := e (Sum.inl 1) with hcdef
  set d := e (Sum.inr 1) with hddef
  simp only [polarBilin_apply_apply] at h11 h22 h12
  have hac : polar Q a c = 0 := by rw [← he0]; exact h11 0 1
  have had : polar Q a d = 0 := by rw [← he0]; simpa using h12 0 1
  have hbc : polar Q b c = 0 := by rw [← hf0, polar_comm]; simpa using h12 1 0
  have hbd : polar Q b d = 0 := by rw [← hf0]; exact h22 0 1
  have hcd : polar Q c d = 1 := by simpa using h12 1 1
  have hdc : polar Q d c = 1 := by rw [polar_comm, hcd]
  have hcc : polar Q c c = 0 := polar_self_eq_zero Q c
  have hdd : polar Q d d = 0 := polar_self_eq_zero Q d
  have hnot : ∀ x : V, polar Q x b = 0 → (∃ y, polar Q x y ≠ 0) → x ∉ (ZMod 2) ∙ a := by
    rintro x hxb ⟨y, hy⟩ hx
    rcases mem_span_singleton_iff.mp hx with rfl | rfl
    · exact hy (polar_zero_left Q y)
    · rw [hab] at hxb
      exact one_ne_zero hxb
  have hcb : polar Q c b = 0 := by rw [polar_comm, hbc]
  have hdb : polar Q d b = 0 := by rw [polar_comm, hbd]
  have hc : c ∉ (ZMod 2) ∙ a := hnot c hcb ⟨d, by rw [hcd]; exact one_ne_zero⟩
  have hd : d ∉ (ZMod 2) ∙ a := hnot d hdb ⟨c, by rw [hdc]; exact one_ne_zero⟩
  have hdcb : polar Q (d - c) b = 0 := by rw [polar_sub_left, hdb, hcb, sub_zero]
  have hdc' : d - c ∉ (ZMod 2) ∙ a := hnot (d - c) hdcb ⟨d, by
    rw [polar_sub_left, hdd, hcd]
    decide⟩
  have hli : ∀ x : V, x ∉ (ZMod 2) ∙ a → LinearIndependent (ZMod 2) ![a, x] := fun x hx =>
    linearIndependent_pair_iff.mpr ⟨ha0, fun h0 => hx (h0 ▸ Submodule.zero_mem _),
      fun hax => hx (hax ▸ Submodule.mem_span_singleton_self a)⟩
  have hQc : Q c = 1 := zmod2_eq_one_of_ne_zero (map_ne_zero_of_minus hmin hQa hac (hli c hc))
  have hQd : Q d = 1 := zmod2_eq_one_of_ne_zero (map_ne_zero_of_minus hmin hQa had (hli d hd))
  set g := CFSG.ClassicalGroups.Orthogonal.reflect Q c *
    CFSG.ClassicalGroups.Orthogonal.reflect Q d with hg
  have hcO := CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q c
  have hdO := CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q d
  have hdim : ∀ v : V, Q v = 1 →
      finrank (ZMod 2) (commSpace (CFSG.ClassicalGroups.Orthogonal.reflect Q v)) = 1 := by
    intro v hv
    let _ : Invertible (Q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
    exact finrank_commSpace_reflection hQ v
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hcO hdO
  have hgΩ : g ∈ omegaGroup Q hQ := by
    refine ⟨hgO, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hcO hdO,
      hdim c hQc, hdim d hQd]
    decide
  have hrc : ∀ x, CFSG.ClassicalGroups.Orthogonal.reflect Q c x = x + polar Q x c • c :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hQc
  have hrd : ∀ x, CFSG.ClassicalGroups.Orthogonal.reflect Q d x = x + polar Q x d • d :=
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hQd
  have hga : g a = a := by
    rw [hg, LinearEquiv.mul_apply, hrd, had, zero_smul, add_zero, hrc, hac, zero_smul, add_zero]
  have hgc : g c - c = d - c := by
    rw [hg, LinearEquiv.mul_apply, hrd, hcd, one_smul, hrc, polar_add_left, hcc, hdc, zero_add,
      one_smul, add_comm c d, add_assoc, vec_add_self, add_zero]
  have hgd : g d - d = c := by
    rw [hg, LinearEquiv.mul_apply, hrd, hdd, zero_smul, add_zero, hrc, hdc, one_smul,
      add_sub_cancel_left]
  have hgX : g ∈ stabIn (omegaGroup Q hQ) a := ⟨hgΩ, hga⟩
  have hcomm : ∀ v : V, polar Q a v = 0 →
      CFSG.ClassicalGroups.Orthogonal.eichler Q a (g v - v) ∈
        ⁅pointRadical Q a, stabIn (omegaGroup Q hQ) a⁆ := by
    intro v hv
    rw [commutator_comm, ← CFSG.ClassicalGroups.Orthogonal.commutatorElement_eichler hgO hga hv]
    exact commutator_mem_commutator hgX (eichler_mem_pointRadical hQa hv)
  have h1 := hcomm d had
  have h2 := hcomm c hac
  rw [hgd] at h1
  rw [hgc] at h2
  have hadc : polar Q a (d - c) = 0 := by rw [polar_sub_right, had, hac, sub_zero]
  refine h.le_commutator_of_card_eq_four (by rw [card_pointRadical hQ ha0 hQa, h4]; rfl) h1 h2
    (fun h0 => hc ((eichler_eq_one_iff hQ ha0 hQa hac).mp h0))
    (fun h0 => hdc' ((eichler_eq_one_iff hQ ha0 hQa hadc).mp h0)) fun heq => hd ?_
  have hmul := CFSG.ClassicalGroups.Orthogonal.eichler_mul (Q := Q) hadc hac
  rw [← heq, eichler_mul_self hac, sub_add_cancel] at hmul
  exact (eichler_eq_one_iff hQ ha0 hQa had).mp hmul.symm

theorem ker_eq_bot_of_omegaPair_minus_four {K : Type*} [Group K] [Finite K]
    {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0)
    (ha0 : a ≠ 0) (hQa : Q a = 0) (h : CEHyp π E a (omegaGroup Q hQ) (pointRadical Q a)) :
    π.ker = ⊥ := by
  have hcard := card_omegaGroup_of_minus_four hQ h4 hmin
  have hE : Nat.card E = 4 := by rw [h.card_E_eq, card_pointRadical hQ ha0 hQa, h4]; rfl
  refine h.ker_eq_bot_of_sq_not_dvd
    (le_commutator_pointRadical_of_minus_four hQ h4 hmin ha0 hQa h) h.inf_ker_eq_bot (m := 15)
    ⟨7, rfl⟩ (by rw [hcard, hE]) fun p hp hp2 hdvd => ?_
  rw [hcard] at hdvd
  have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hp8 : p < 8 := by nlinarith
  interval_cases p <;> revert hp hp2 hdvd <;> norm_num

end CFSG.LargeExtraspecial.S4
