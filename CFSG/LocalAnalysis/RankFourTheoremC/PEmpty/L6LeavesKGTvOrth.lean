module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem mem_normalizer_map {X G : Type*} [Group X] [Group G] (f : X →* G) (N : Subgroup X)
    [N.Normal] (x : X) : f x ∈ Subgroup.normalizer ((N.map f : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨x * n * x⁻¹, Subgroup.Normal.conj_mem inferInstance n hn x, by simp⟩
  · rintro ⟨n, hn, hnh⟩
    refine ⟨x⁻¹ * n * x, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance n hn x⁻¹
    · rw [map_mul, map_mul, map_inv, hnh]
      group

theorem exists_basis_quadratic' {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 1 ≤ n)
    (hdim : finrank (ZMod 2) V = 2 * n) :
    (∃ b : Module.Basis (Fin n ⊕ Fin n) (ZMod 2) V,
        ∀ v, Q v = StatedQuadPlus n (ZMod 2) (b.equivFun v)) ∨
      ∃ b : Module.Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (ZMod 2) V,
        ∀ v, Q v = StatedQuadMinus n (ZMod 2) 1 1 (b.equivFun v) := by
  rcases (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
    Q hQ).2.2.1 n hn hdim with ⟨b, hb⟩ | ⟨β, γ, hβ, hroot, b, hb⟩
  · refine Or.inl ⟨b, fun v => ?_⟩
    have hv : v = ∑ i, b.repr v (.inl i) • b (.inl i) + ∑ i, b.repr v (.inr i) • b (.inr i) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [Fintype.sum_sum_type]
    conv_lhs => rw [hv]
    rw [hb]
    rfl
  · obtain rfl : β = 1 := mclt_zmod2_eq_one hβ
    obtain rfl : γ = 1 := mclt_zmod2_eq_one fun h => hroot 0 (by rw [h]; ring)
    refine Or.inr ⟨b, fun v => ?_⟩
    have hv : v = ∑ i, b.repr v (.inl i) • b (.inl i) +
        ∑ i, b.repr v (.inr (.inl i)) • b (.inr (.inl i)) +
          b.repr v (.inr (.inr 0)) • b (.inr (.inr 0)) +
            b.repr v (.inr (.inr 1)) • b (.inr (.inr 1)) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
      abel
    conv_lhs => rw [hv]
    rw [hb]
    rfl

section Orth

variable {X : Type} [Group X] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem orth_core {N : Subgroup X} [N.Normal] (hNc : N = ⁅(⊤ : Subgroup X), ⊤⁆)
    (ψ : X →* LinearMap.GeneralLinearGroup (ZMod 2) U) (hinj : Function.Injective ψ) {a : X}
    (hτ : IsF2Transvection (ψ a)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 2) U) (Q : U → ZMod 2) (Q₀ : (ι → ZMod 2) → ZMod 2)
    (hQ : ∀ v, Q v = Q₀ (b.equivFun v))
    (hmem : ∀ g, g ∈ ψ.range ↔ ∀ v, Q ((g : U →ₗ[ZMod 2] U) v) = Q v) {m : ℕ}
    (h96 : ∀ (t : GL ι (ZMod 2))
      (ht : t ∈ Subgroup.normalizer (StatedOmega Q₀ : Set (GL ι (ZMod 2)))),
      (∀ x, Q₀ (Matrix.mulVec (t : Matrix ι ι (ZMod 2)) x) = Q₀ x) →
      CFSG.LocalAnalysis.GLTheoremB.IsTransvection t →
      Nonempty (↥(fixSub ((StatedOmega Q₀).normalizerMonoidHom ⟨t, ht⟩)) ≃*
        ↥(StatedSp m (ZMod 2)))) :
    Nonempty (↥N ≃* ↥(StatedOmega Q₀)) ∧
      Nonempty (↥(N ⊓ Subgroup.centralizer ({a} : Set X)) ≃* ↥(StatedSp m (ZMod 2))) := by
  set Θ : LinearMap.GeneralLinearGroup (ZMod 2) U ≃* GL ι (ZMod 2) := mclt_glMatrixEquiv b
    with hΘ
  set Θ' : X →* GL ι (ZMod 2) := Θ.toMonoidHom.comp ψ with hΘ'
  have hΘinj : Function.Injective Θ' := Θ.injective.comp hinj
  have hrange : Θ'.range = CFSG.MatrixModel.isometryCore Q₀ := by
    rw [hΘ', MonoidHom.range_comp]
    exact mclt_map_glMatrixEquiv_eq_closure b hQ hmem
  have hNmap : N.map Θ' = StatedOmega Q₀ := by
    have h1 : StatedOmega Q₀ = ⁅CFSG.MatrixModel.isometryCore Q₀,
        CFSG.MatrixModel.isometryCore Q₀⁆ := rfl
    rw [h1, ← hrange, MonoidHom.range_eq_map, hNc, Subgroup.map_commutator]
  have eN : ↥N ≃* ↥(StatedOmega Q₀) :=
    (N.equivMapOfInjective Θ' hΘinj).trans (MulEquiv.subgroupCongr hNmap)
  refine ⟨⟨eN⟩, ?_⟩
  set t : GL ι (ZMod 2) := Θ' a with ht_def
  have ht : t ∈ Subgroup.normalizer ((StatedOmega Q₀ : Subgroup (GL ι (ZMod 2))) : Set _) := by
    rw [← hNmap]
    exact mem_normalizer_map Θ' N a
  have hψa := (hmem (ψ a)).1 ⟨a, rfl⟩
  have hmul : ∀ v, Matrix.mulVec (t : Matrix ι ι (ZMod 2)) (b.equivFun v) =
      b.equivFun ((ψ a : U →ₗ[ZMod 2] U) v) := fun v => mclt_glMatrixEquiv_mulVec b (ψ a) v
  have hQt : ∀ x, Q₀ (Matrix.mulVec (t : Matrix ι ι (ZMod 2)) x) = Q₀ x := by
    intro x
    obtain ⟨v, rfl⟩ := b.equivFun.surjective x
    rw [hmul, ← hQ, ← hQ, hψa]
  obtain ⟨φ, a₀, hφa, hφ, ha₀, hτeq⟩ := (isF2Transvection_iff _).1 hτ
  have hT : CFSG.LocalAnalysis.GLTheoremB.IsTransvection t := by
    refine ⟨b.equivFun a₀, φ ∘ₗ b.equivFun.symm.toLinearMap, ?_, ?_, ?_, ?_⟩
    · intro h0
      exact ha₀ (b.equivFun.injective (by rw [h0, map_zero]))
    · intro h0
      obtain ⟨u, hu⟩ := exists_apply_eq_one hφ
      have := LinearMap.congr_fun h0 (b.equivFun u)
      simp [hu] at this
    · simp [hφa]
    · intro x
      obtain ⟨v, rfl⟩ := b.equivFun.surjective x
      rw [hmul, hτeq, tv_apply, map_add, map_smul]
      simp
  have hSp := (h96 t ht hQt hT)
  obtain ⟨F⟩ := OmegaFacts.fixSub_equiv_centralizer (Ω := StatedOmega Q₀) (t := t) ht
  obtain ⟨S⟩ := hSp
  have hC : (N ⊓ Subgroup.centralizer ({a} : Set X)).map Θ' =
      StatedOmega Q₀ ⊓ Subgroup.centralizer ({t} : Set (GL ι (ZMod 2))) := by
    ext y
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hc' : c ∈ N ⊓ Subgroup.centralizer ({a} : Set X) := hc
      rw [Subgroup.mem_inf] at hc'
      obtain ⟨hcN, hca⟩ := hc'
      refine ⟨hNmap ▸ ⟨c, hcN, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hca ⊢
      rw [ht_def, ← map_mul, ← map_mul, hca]
    · rintro ⟨hyΩ, hyt⟩
      rw [← hNmap] at hyΩ
      obtain ⟨c, hcN, rfl⟩ := hyΩ
      refine ⟨c, ?_, rfl⟩
      change c ∈ N ⊓ Subgroup.centralizer ({a} : Set X)
      rw [Subgroup.mem_inf]
      refine ⟨hcN, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyt ⊢
      rw [ht_def, ← map_mul, ← map_mul] at hyt
      exact hΘinj hyt
  exact ⟨((N ⊓ Subgroup.centralizer ({a} : Set X)).equivMapOfInjective Θ' hΘinj).trans
    ((MulEquiv.subgroupCongr hC).trans (F.symm.trans S))⟩

theorem orth_case {N : Subgroup X} [N.Normal] (hNc : N = ⁅(⊤ : Subgroup X), ⊤⁆)
    [FiniteDimensional (ZMod 2) U] (ψ : X →* LinearMap.GeneralLinearGroup (ZMod 2) U)
    (hinj : Function.Injective ψ) {a : X} (hτ : IsF2Transvection (ψ a))
    (Q : QuadraticForm (ZMod 2) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hH : ψ.range = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom)
    (hd : 5 ≤ finrank (ZMod 2) U) :
    ∃ (ε : Bool) (n : ℕ), 2 ≤ n ∧ IsOmegaTwo ε (n + 1) ↥N ∧
      Nonempty (↥(N ⊓ Subgroup.centralizer ({a} : Set X)) ≃* ↥(StatedSp n (ZMod 2))) := by
  have hmem : ∀ g, g ∈ ψ.range ↔ ∀ v, Q ((g : U →ₗ[ZMod 2] U) v) = Q v := by
    intro g
    rw [hH, Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  obtain ⟨hplus, hminus⟩ := OmegaFacts.input9_6OmegaTransv_holds
  obtain ⟨n', hn'⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  obtain ⟨n, rfl⟩ : ∃ n, n' = n + 1 := ⟨n' - 1, by omega⟩
  have hdim : finrank (ZMod 2) U = 2 * (n + 1) := by omega
  have hn2 : 2 ≤ n := by omega
  rcases exists_basis_quadratic' Q hQ (n := n + 1) (by omega) hdim with ⟨b, hb⟩ | ⟨b, hb⟩
  · refine ⟨true, n, hn2, ?_⟩
    exact orth_core hNc ψ hinj hτ b ⇑Q (StatedQuadPlus (n + 1) (ZMod 2)) hb hmem (m := n)
      (fun t ht hQt hT => (hplus n (by omega) t ht hQt hT).2)
  · refine ⟨false, n, hn2, ?_⟩
    exact orth_core hNc ψ hinj hτ b ⇑Q (StatedQuadMinus (n + 1) (ZMod 2) 1 1) hb hmem (m := n)
      (fun t ht hQt hT => (hminus n (by omega) t ht hQt hT).2)

end Orth

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv
