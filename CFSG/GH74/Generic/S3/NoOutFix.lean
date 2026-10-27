module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
public import CFSG.GH74.Generic.S3.V1InnerUni
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.S3.NbrR

public section

namespace CFSG.GH74.Generic.S3

open Matrix Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear
open scoped MatrixGroups commutatorElement

@[expose] def OuterFixPerfect (K : Type) [Group K] : Prop :=
  ∀ σ : MulAut K, σ * σ = 1 → σ ∉ (inner K : Subgroup (MulAut K)) →
    ∃ P : Subgroup K, P ≠ ⊥ ∧ ⁅P, P⁆ = P ∧ ∀ s ∈ P, σ s = s

theorem OuterFixPerfect.of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L)
    (h : OuterFixPerfect L) : OuterFixPerfect K := by
  intro σ hσ2 hout
  have hσ2' : conjAutEquiv e σ * conjAutEquiv e σ = 1 := by
    rw [← conjAutEquiv_mul, hσ2, conjAutEquiv_one]
  have hout' : conjAutEquiv e σ ∉ (inner L : Subgroup (MulAut L)) := fun h' =>
    hout (conjAutEquiv_mem_inner e h')
  obtain ⟨P, hP1, hPperf, hPfix⟩ := h _ hσ2' hout'
  refine ⟨P.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro hbot
    apply hP1
    have := congrArg (Subgroup.map e.toMonoidHom) hbot
    rw [Subgroup.map_map, Subgroup.map_bot] at this
    simpa [MulEquiv.toMonoidHom_eq_coe, ← MonoidHom.comp_assoc] using this
  · rw [← Subgroup.map_commutator, hPperf]
  · rintro _ ⟨s, hs, rfl⟩
    have h1 := hPfix s hs
    have h2 : conjAutEquiv e σ (e (e.symm s)) = e (σ (e.symm s)) := conjAutEquiv_apply e σ _
    rw [MulEquiv.apply_symm_apply, h1] at h2
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← h2, MulEquiv.apply_symm_apply]

section PSL

variable {F : Type} [Field F]

theorem lin_outer_fixed_perfect [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hFc : Nat.card F = p ^ f)
    (h5 : 5 ≤ p ^ f) {c : MulAut (projectiveSL 3 F)} (hc2 : c * c = 1)
    (hout : c ∉ (inner (projectiveSL 3 F) : Subgroup (MulAut (projectiveSL 3 F)))) :
    ∃ P : Subgroup (projectiveSL 3 F), P ≠ ⊥ ∧ ⁅P, P⁆ = P ∧ ∀ s ∈ P, c s = s := by
  classical
  have hodd : Odd (Nat.card F) := by rw [hFc]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h5
    · exact h
  have hne : ∀ P : Subgroup (projectiveSL 3 F), Even (Nat.card P) → P ≠ ⊥ := by
    intro P hP hbot
    rw [hbot, Subgroup.card_bot] at hP
    exact absurd hP (by decide)
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hcA⟩ := hform c
  by_cases hσ1 : σ = 1
  · rw [hσ1] at hcA
    interval_cases ε
    · exfalso
      rw [pow_zero, mul_one, map_one, mul_one] at hcA
      have hsq : conjAut 3 F A * conjAut 3 F A = 1 := by rw [← hcA]; exact hc2
      have h1 : conjAut 3 F (A * A) * fieldAut 3 F 1 = 1 := by
        rw [map_one, mul_one, map_mul]; exact hsq
      obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl (A * A) 1 h1
      have hscal : ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) = (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
        rw [smul_one_eq_diagonal]; rfl
      have hAA : (A : Matrix (Fin 3) (Fin 3) F) * A = (u : F) • 1 := by
        rw [← hscal, hu, Units.val_mul]
      exact hout (hcA ▸ conjAut_mem_inner_of_sq_scalar A u hAA)
    · rw [pow_one, map_one, mul_one] at hcA
      have hsq : (conjAut 3 F A * fieldAut 3 F 1 * dualAut 3 F) ^ 2 = 1 := by
        rw [map_one, mul_one, pow_two, ← hcA]; exact hc2
      have hAs : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A := by
        rcases transpose_eq_or_eq_neg_of_sq le_rfl A hsq with h | h
        · exact h
        · exfalso
          have hdet := congrArg Matrix.det h
          rw [Matrix.det_transpose, Matrix.det_neg] at hdet
          have hd0 : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
            ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
          simp only [Fintype.card_fin] at hdet
          apply hd0
          have h22 : (2 : F) * (A : Matrix (Fin 3) (Fin 3) F).det = 0 := by
            linear_combination hdet
          exact (mul_eq_zero.1 h22).resolve_left h2
      have h4 : ∃ s : Finset F, s.card = 4 := by
        let _ : Fintype F := Fintype.ofFinite F
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4) (by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hFc]; omega)
        exact ⟨t, ht⟩
      obtain ⟨P, hP, hPe, hfix⟩ := exists_fixed_perfect_even_conjAut_dualAut_of_transpose_eq hF2 h4 le_rfl A hAs
      refine ⟨P, hne P hPe, Subgroup.isPerfect_iff.mp hP, fun s hs => ?_⟩
      rw [hcA]
      exact hfix s hs
  · interval_cases ε
    · rw [pow_zero, mul_one] at hcA
      have hα : (conjAut 3 F A * fieldAut 3 F σ) ^ 2 = 1 := by rw [pow_two, ← hcA]; exact hc2
      obtain ⟨P, hP, hPe, hfix⟩ :=
        exists_fixed_perfect_even_conjAut_fieldAut hp hf hFc le_rfl A σ hσ1 hα
      refine ⟨P, hne P hPe, Subgroup.isPerfect_iff.mp hP, fun s hs => ?_⟩
      rw [hcA]
      exact hfix s hs
    · rw [pow_one] at hcA
      have hα : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) ^ 2 = 1 := by rw [pow_two, ← hcA]; exact hc2
      obtain ⟨P, hP, hPe, hfix⟩ :=
        exists_fixed_perfect_even_conjAut_fieldAut_dualAut hp hp2 hf hFc le_rfl A σ hσ1 hα
      refine ⟨P, hne P hPe, Subgroup.isPerfect_iff.mp hP, fun s hs => ?_⟩
      rw [hcA]
      exact hfix s hs

end PSL

theorem outerFixPerfect_PSL {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hX : StatedClassicalModel K .PSL 3 p f) : OuterFixPerfect K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  refine OuterFixPerfect.of_mulEquiv e fun c hc2 hout => ?_
  exact lin_outer_fixed_perfect hp hp2 hF h5 hc2 hout

theorem outerFixPerfect_PSU {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hX : StatedClassicalModel K .PSU 3 p f) : OuterFixPerfect K := by
  intro σ hσ2 hout
  obtain ⟨N, hN⟩ := ((libData_uni hp hp2 h5) K hX).2 σ hσ2 hout
  refine ⟨N, ?_, CFSG.GH74.KGroups.Bal.commutator_self_of_quasisimple hN.quasisimple, hN.fixed⟩
  intro hbot
  have : Nontrivial ↥N := CFSG.LocalCores.isQuasisimple_nontrivial hN.quasisimple
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥N)
  exact ha (Subtype.ext (by simpa [hbot] using a.2))

section Nbr

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.outerFixPerfect (hnd : NbrData G t p f x y Iw Iv) : OuterFixPerfect (↥Iw ⧸ center ↥Iw) := by
  rcases hnd.tag with rfl | rfl
  · exact outerFixPerfect_PSL hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 (stated_of_lieModel_PSL hnd.model_w)
  · exact outerFixPerfect_PSU hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 (stated_of_lieModel_PSU hnd.model_w)

end Nbr

end CFSG.GH74.Generic.S3
