module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Inner
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K]

theorem su3_triple_or_split (h : UnitaryFieldData p f K) (hp : p ≠ 2) {r ε : ℕ}
    (hn : 2 * r + ε = 4) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K}
    (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1) (hN : h.norm l = 1) :
    (∃ (d : K) (v : Fin 3 → HypIndex r ε → K),
      (∀ i, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v i = d • v i) ∧
      ∀ i j, hypForm h r ε (v i) (v j) = if i = j then 1 else 0) ∨
    finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) = 2 := by
  classical
  have hAA' := mulVecLin_mul_self hAA
  rw [← coe_unitaryOfHyp h hA] at hAA'
  obtain ⟨-, hsepP, hsepM, -⟩ := exists_split_centralizer_equiv hp (hypForm_isSymm h)
    (hypForm_separatingLeft h) hl0 hAA' hN
  rw [coe_unitaryOfHyp] at hsepP hsepM hAA'
  have hc : IsCompl (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K)))
      (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) :=
    isCompl_ker_sub_one_ker_add_one (two_ne_zero_of_odd h hp) (invSMulOp_mul_self hl0 hAA')
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_hypIndex_fun] at hdim
  by_cases hP : 3 ≤ finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε)
      (HypIndex r ε) K)))
  · left
    have hBW := (⟨fun x y => (hypForm_isSymm h).eq x.1 y.1⟩ :
      ((hypForm h r ε).domRestrict₁₂ (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε)
        (HypIndex r ε) K))) (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε)
          (HypIndex r ε) K)))).IsSymm)
    obtain ⟨e, he⟩ := h.exists_orthonormal_basis hBW hsepP
    refine ⟨l, fun i => (e ⟨i, by omega⟩ : HypIndex r ε → K), fun i =>
      mulVec_eq_of_mem_eigenPlus hl0 (e ⟨i, by omega⟩).2, fun i j => ?_⟩
    have := he ⟨i, by omega⟩ ⟨j, by omega⟩
    simp only [LinearMap.domRestrict₁₂_apply, Fin.mk.injEq] at this
    simpa [Fin.ext_iff] using this
  · by_cases hM : 3 ≤ finrank K (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε)
        (HypIndex r ε) K)))
    · left
      have hBW := (⟨fun x y => (hypForm_isSymm h).eq x.1 y.1⟩ :
        ((hypForm h r ε).domRestrict₁₂ (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε)
          (HypIndex r ε) K))) (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε)
            (HypIndex r ε) K)))).IsSymm)
      obtain ⟨e, he⟩ := h.exists_orthonormal_basis hBW hsepM
      refine ⟨-l, fun i => (e ⟨i, by omega⟩ : HypIndex r ε → K), fun i =>
        mulVec_eq_of_mem_eigenMinus hl0 (e ⟨i, by omega⟩).2, fun i j => ?_⟩
      have := he ⟨i, by omega⟩ ⟨j, by omega⟩
      simp only [LinearMap.domRestrict₁₂_apply, Fin.mk.injEq] at this
      simpa [Fin.ext_iff] using this
    · right
      omega

@[expose] def SurvU4 (h : UnitaryFieldData p f K) (α : MulAut (hypPSU h 2 0)) : Prop :=
  (∃ (A : GL (HypIndex 2 0) K) (l : K)
      (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ l ≠ 0 ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 ∧ h.norm l = 1 ∧
      finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) = 2 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) ∨
    (∃ (A : GL (HypIndex 2 0) K) (l : K)
      (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ l ≠ 0 ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 ∧ h.norm l = -1 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) ∨
    (∃ (A : GL (HypIndex 2 0) K) (σ : K ≃+* K)
      (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ (∀ c, σ c = h.bar c) ∧ ∃ c : K, c ≠ 0 ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = c • 1 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩)

theorem unitary4_involution_cases (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (α : MulAut (hypPSU h 2 0)) (hα : α ^ 2 = 1) :
    (∃ ψ : ↥(StatedSU 3 (p ^ f) K) →* hypSU h 2 0,
        Function.Injective ((hypProj h 2 0).comp ψ) ∧
        ∀ s ∈ ((hypProj h 2 0).comp ψ).range, α s = s) ∨ SurvU4 h α := by
  classical
  have := h.finite
  have hinj : ∀ ψ : ↥(StatedSU 3 (p ^ f) K) →* hypSU h 2 0,
      (∀ x, hypProj h 2 0 (ψ x) = 1 → x = 1) → Function.Injective ((hypProj h 2 0).comp ψ) :=
    fun ψ hψ => by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact hψ x hx
  by_cases hα1 : α = 1
  · subst hα1
    obtain ⟨ψ, hψs⟩ := exists_su3Hom_hypSU h (r := 2) (ε := 0) (by norm_num)
    exact Or.inl ⟨ψ, hinj ψ hψs, fun s _ => rfl⟩
  have hα2 : orderOf α = 2 := orderOf_eq_prime hα hα1
  obtain ⟨A, σ, hx, hA, hαeq, hσ, hrefl, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp (by norm_num : 1 ≤ 2)
      (by norm_num : 0 ≤ 1) (by norm_num : 3 ≤ 2 * 2 + 0)).2.2.2 α hα2
  subst hαeq
  rcases hσ with rfl | hσ
  · have hord := hrefl rfl
    have hsq : (QuotientGroup.mk (⟨A, hA⟩ * ⟨A, hA⟩) : hypUnitaryMod h 2 0) = 1 := by
      rw [QuotientGroup.mk_mul, ← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
    obtain ⟨d, hd, -, hAA⟩ := mem_normOneScalars.mp ((QuotientGroup.eq_one_iff _).mp hsq)
    obtain ⟨l, hl0, hld⟩ := exists_sq_eq_of_norm_eq_one h hp hd
    have hAA' : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 := by
      have h1 := congrArg (fun g : GL (HypIndex 2 0) K =>
        (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) hAA
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
      rw [h1, hld, scalar_apply, smul_one_eq_diagonal]
    have hN : h.norm l = 1 ∨ h.norm l = -1 := by
      have h1 : h.norm l * h.norm l = 1 := by
        rw [← norm_mul_eq h, ← pow_two, hld, hd]
      exact mul_self_eq_one_iff.mp h1
    rcases hN with hN | hN
    · rcases su3_triple_or_split h hp (by norm_num) hA hl0 hAA' hN with
        ⟨d, v, hAv, hvv⟩ | hdim
      · obtain ⟨ψ, hψ, hψs⟩ := exists_su3Hom_of_triple h (by norm_num) hA v hAv hvv
        exact Or.inl ⟨ψ, hinj ψ hψs, fixed_of_comm h _ _ hx ψ hψ⟩
      · exact Or.inr (Or.inl ⟨A, l, hx, hA, hl0, hAA', hN, hdim, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨A, l, hx, hA, hl0, hAA', hN, rfl⟩))
  · obtain ⟨c, hc, hAA⟩ := hbar hσ
    exact Or.inr (Or.inr (Or.inr ⟨A, σ, hx, hA, hσ, c, hc, hAA, rfl⟩))

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
