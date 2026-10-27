module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLFix
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLMat

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL

open Module

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_triangular_basis {S : Type} [Group S] (hS : IsPGroup 2 S)
    (ρ : S →* Module.End F (Fin 3 → F)) :
    ∃ b : Basis (Fin 3) F (Fin 3 → F), ∀ s : S, ∃ a β γ : F,
      LinearMap.toMatrix b b (ρ s) = tMat a β γ := by
  have hfV : finrank F (Fin 3 → F) = 3 := by simp
  obtain ⟨v1, hv1, hfix1⟩ := exists_fixed_ne_zero hS ρ (inferInstance : Nontrivial (Fin 3 → F))
  set L1 : Submodule F (Fin 3 → F) := Submodule.span F {v1} with hL1
  have hL1inv : ∀ s, L1 ≤ L1.comap (ρ s) := by
    intro s
    rw [hL1, Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show ρ s y ∈ Submodule.span F {y}
    rw [hfix1 s]
    exact Submodule.subset_span rfl
  have hL1rank : finrank F L1 = 1 := finrank_span_singleton hv1
  have hQ1 : finrank F ((Fin 3 → F) ⧸ L1) = 2 := by
    have := L1.finrank_quotient_add_finrank
    omega
  have : Nontrivial ((Fin 3 → F) ⧸ L1) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨wb, hwb, hfix2⟩ := exists_fixed_ne_zero hS (qAct ρ L1 hL1inv) this
  obtain ⟨w2, rfl⟩ := Submodule.Quotient.mk_surjective L1 wb
  have hw2 : w2 ∉ L1 := fun h => hwb ((Submodule.Quotient.mk_eq_zero L1).2 h)
  have hρw2 : ∀ s, ρ s w2 - w2 ∈ L1 := fun s => by
    have := hfix2 s
    rw [qAct_mk] at this
    exact (Submodule.Quotient.eq L1).1 this
  set L2 : Submodule F (Fin 3 → F) := Submodule.span F {v1, w2} with hL2
  have hL1L2 : L1 ≤ L2 := Submodule.span_mono (by simp)
  have hv1L2 : v1 ∈ L2 := Submodule.subset_span (by simp)
  have hw2L2 : w2 ∈ L2 := Submodule.subset_span (by simp)
  have hL2inv : ∀ s, L2 ≤ L2.comap (ρ s) := by
    intro s
    rw [hL2, Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · show ρ s y ∈ L2
      rw [hfix1 s]; exact hv1L2
    · show ρ s y ∈ L2
      have h1 : ρ s y = (ρ s y - y) + y := by abel
      rw [h1]
      exact L2.add_mem (hL1L2 (hρw2 s)) hw2L2
  have hli2 : LinearIndependent F ![v1, w2] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hb : b = 0 := by
      by_contra hb
      apply hw2
      have : w2 = (-(b⁻¹ * a)) • v1 := by
        have h1 : b • w2 = -(a • v1) := eq_neg_of_add_eq_zero_right hab
        calc w2 = b⁻¹ • (b • w2) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = _ := by rw [h1, smul_neg, smul_smul, neg_smul, mul_comm b⁻¹ a, ← neg_smul]
      rw [this]
      exact L1.smul_mem _ (Submodule.subset_span rfl)
    subst hb
    refine ⟨?_, rfl⟩
    rw [zero_smul, add_zero, smul_eq_zero] at hab
    exact hab.resolve_right hv1
  have hL2rank : finrank F L2 = 2 := by
    have := finrank_span_eq_card hli2
    have hr : Set.range ![v1, w2] = {v1, w2} := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hr] at this
    simpa using this
  have hQ2 : finrank F ((Fin 3 → F) ⧸ L2) = 1 := by
    have := L2.finrank_quotient_add_finrank
    omega
  have hρL2 : ∀ s v, ρ s v - v ∈ L2 := by
    intro s v
    have h1 := eq_one_of_finrank_eq_one hS (qAct ρ L2 hL2inv) hQ2 s
    have := congrArg (fun f => f (Submodule.Quotient.mk v)) h1
    simp only [qAct_mk, Module.End.one_apply] at this
    exact (Submodule.Quotient.eq L2).1 this
  have hL2ne : L2 ≠ ⊤ := fun h => by
    rw [h, finrank_top, hfV] at hL2rank
    omega
  obtain ⟨v3, hv3⟩ : ∃ v3, v3 ∉ L2 := by
    by_contra hcon
    push Not at hcon
    exact hL2ne (eq_top_iff.2 fun v _ => hcon v)
  have hli : LinearIndependent F ![v1, w2, v3] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three] at hg
    simp at hg
    have hg2 : g 2 = 0 := by
      by_contra h2
      apply hv3
      have : v3 = (-((g 2)⁻¹ * g 0)) • v1 + (-((g 2)⁻¹ * g 1)) • w2 := by
        have h1 : g 2 • v3 = -(g 0 • v1 + g 1 • w2) := eq_neg_of_add_eq_zero_right
          (by linear_combination (exp := 1) hg)
        calc v3 = (g 2)⁻¹ • (g 2 • v3) := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
          _ = _ := by rw [h1, smul_neg, smul_add, smul_smul, smul_smul, neg_add, ← neg_smul,
                ← neg_smul]
      rw [this]
      exact Submodule.mem_span_pair.2 ⟨_, _, rfl⟩
    rw [hg2, zero_smul, add_zero] at hg
    have hg1 : g 1 = 0 := by
      have := (LinearIndependent.pair_iff.1 hli2) (g 0) (g 1) hg
      exact this.2
    have hg0 : g 0 = 0 := by
      have := (LinearIndependent.pair_iff.1 hli2) (g 0) (g 1) hg
      exact this.1
    intro i
    fin_cases i <;> simp [hg0, hg1, hg2]
  let b : Basis (Fin 3) F (Fin 3 → F) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfV])
  have hb : ∀ j, b j = ![v1, w2, v3] j := fun j => by
    simp [b]
  refine ⟨b, fun s => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hρw2 s)
  obtain ⟨q, p, hqp⟩ := Submodule.mem_span_pair.1 (hρL2 s v3)
  have e0 : ρ s (b 0) = b 0 := by simpa [hb] using hfix1 s
  have e1 : ρ s (b 1) = b 1 + a • b 0 := by
    simp only [hb]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [ha]; abel
  have e2 : ρ s (b 2) = b 2 + p • b 1 + q • b 0 := by
    simp only [hb]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    have : ρ s v3 = v3 + (q • v1 + p • w2) := by rw [hqp]; abel
    rw [this]; abel
  refine ⟨a, p, q, ?_⟩
  ext i j
  fin_cases j <;> fin_cases i <;>
    simp [LinearMap.toMatrix_apply, e0, e1, e2, tMat]

theorem exists_scalar_of_centralizes {Γ : Type} [Group Γ] (ρ : Γ →* Module.End F (Fin 3 → F))
    (S : Subgroup Γ) (hS : IsPGroup 2 S) {x y : Γ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : ρ x * ρ y ≠ ρ y * ρ x) (t : Γ) (hodd : Odd (orderOf t))
    (ht : ∀ s ∈ S, s * t = t * s) :
    ∃ c : F, ρ t = c • (1 : Module.End F (Fin 3 → F)) := by
  obtain ⟨b, hb⟩ := exists_triangular_basis hS (ρ.comp S.subtype)
  let Φ := LinearMap.toMatrixAlgEquiv b
  have hΦ : ∀ f, Φ f = LinearMap.toMatrix b b f := fun f => rfl
  obtain ⟨a, β, γ, hxm⟩ := hb ⟨x, hx⟩
  obtain ⟨a', β', γ', hym⟩ := hb ⟨y, hy⟩
  have hxm' : Φ (ρ x) = tMat a β γ := by rw [hΦ]; exact hxm
  have hym' : Φ (ρ y) = tMat a' β' γ' := by rw [hΦ]; exact hym
  have hD : a * β' - a' * β ≠ 0 := by
    intro hD
    apply hxy
    apply Φ.injective
    rw [map_mul, map_mul, hxm', hym', tMat_mul, tMat_mul]
    have h1 : a * β' = a' * β := sub_eq_zero.1 hD
    congr 1
    · exact add_comm _ _
    · exact add_comm _ _
    · rw [h1]; ring
  set T := Φ (ρ t) with hT
  have hcx : T * tMat a β γ = tMat a β γ * T := by
    rw [← hxm', hT, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ht x hx]
  have hcy : T * tMat a' β' γ' = tMat a' β' γ' * T := by
    rw [← hym', hT, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ht y hy]
  obtain ⟨h10, h20, h21, h01, h12⟩ := commute_tMat_pair hD hcx hcy
  have hTr : T ^ orderOf t = 1 := by
    rw [hT, ← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
  obtain ⟨c, hc⟩ := eq_smul_one_of_tri_odd (CharP.cast_eq_zero F 2) hodd hTr h10 h20 h21 h01 h12
  refine ⟨c, Φ.injective ?_⟩
  rw [map_smul, map_one]
  exact hc

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL
