module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.SeitzReduction.F4Pilot

open scoped Matrix
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal (plusPair minusPair toLinEquiv toLinEquiv_apply)
open CFSG.SectionRank.EvenCover (spinMatrixEquiv ker_symm_comp
  statedScalars_subgroupOf_statedOmega_eq_bot)
open CFSG.Adapters.RankTwoModelTransports (glCongr)
open CFSG.ClassicalInvolution.Upgrade (map_statedOmega map_statedOmega_conj fieldIsoOfCard
  irreducible_map)

theorem exists_surjective_ker_le_center_of_statedProj {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {M : Type} [Group M] {H : Subgroup (GL ι K)} (ψ : M ≃* H) {S : Type}
    [Group S] (e : S ≃* StatedProj H) :
    ∃ π : M →* S, Function.Surjective π ∧ π.ker ≤ Subgroup.center M := by
  refine ⟨e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp ψ.toMonoidHom),
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp ψ.surjective), fun x hx => ?_⟩
  have h1 : ψ x ∈ (StatedScalars ι K).subgroupOf H := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  have h2 := Subgroup.mem_center_iff.1
    (CFSG.LieType.Universal.Spin.statedScalars_subgroupOf_le_center H h1)
  refine Subgroup.mem_center_iff.2 fun y => ψ.injective ?_
  rw [map_mul, map_mul, h2 (ψ y)]

theorem statedClassicalModel_of_lieModel_pomega {S : Type} [Group S] {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel S t n p f) : StatedClassicalModel S t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by rcases ht with rfl | rfl <;> decide)

theorem exists_gl_isometry_statedQuadMinus {K : Type} [Field K] [Finite K] (n : ℕ)
    {b c b' c' : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hirr' : ∀ s : K, s ^ 2 + b' * s + c' ≠ 0) :
    ∃ g : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K,
      ∀ v, StatedQuadMinus n K b' c' ((g : Matrix _ _ K) *ᵥ v) = StatedQuadMinus n K b c v := by
  obtain ⟨ι⟩ := CFSG.GroupTheory.WeirSylow.binForm_isometry hirr' hirr
  let e : (quadMinus n K b c).IsometryEquiv (quadMinus n K b' c') :=
    (CFSG.GroupTheory.WeirSylow.quadMinusIsometry n b c).trans
      (((QuadraticMap.IsometryEquiv.refl _).prod ι).trans
        (CFSG.GroupTheory.WeirSylow.quadMinusIsometry n b' c').symm)
  refine ⟨(toLinEquiv _ K).symm e.toLinearEquiv, fun v => ?_⟩
  have h1 : (((toLinEquiv _ K).symm e.toLinearEquiv : GL _ K) : Matrix _ _ K) *ᵥ v = e v := by
    rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [h1, ← coe_quadMinus, ← coe_quadMinus]
  exact e.map_app v

section Plus

theorem isPerfect_omegaPlus8 (k : Type) [Field k] :
    Group.IsPerfect (StatedOmega (StatedQuadPlus 4 k)) :=
  isPerfect_statedOmega_quadPlus (by norm_num)

theorem center_omegaPlus8 (k : Type) [Field k] [CharP k 2] :
    Subgroup.center (StatedOmega (StatedQuadPlus 4 k)) = ⊥ :=
  (center_statedOmega_quadPlus (by norm_num)).trans
    (statedScalars_subgroupOf_statedOmega_eq_bot (coe_quadPlus 4 k)
      (exists_map_ne_zero_of_hypPair _ (plusPair k (⟨0, by norm_num⟩ : Fin 4))))

theorem omegaPlus8_exists_section (k : Type) [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) (E : Type) [Group E] [Finite E]
    (π : E →* StatedOmega (StatedQuadPlus 4 k)) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) :
    ∃ s : StatedOmega (StatedQuadPlus 4 k) →* E, ∀ g, π (s g) = g := by
  set Φ := spinMatrixEquiv (ker_spinMatrix_quadPlus_eq_bot (n := 4) (K := k) CharTwo.two_eq_zero)
    (range_spinMatrix_quadPlus (by norm_num))
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_exists_section_of_central
      (n := 4) (by norm_num) hk (π := Φ.symm.toMonoidHom.comp π) (Φ.symm.surjective.comp hπ)
      (by rw [ker_symm_comp]; exact hc)
  exact ⟨s.comp Φ.symm.toMonoidHom, fun g => Φ.symm.injective (hs (Φ.symm g))⟩

theorem omegaPlus8_covers (k : Type) [Field k] [Finite k] {f : ℕ} (hk : Nat.card k = 2 ^ f)
    (S : Type) [Group S] (hS : CFSG.Blueprint.LieModel S .POmegaPlus 4 2 f) :
    ∃ π : StatedOmega (StatedQuadPlus 4 k) →* S, Function.Surjective π ∧
      π.ker ≤ Subgroup.center (StatedOmega (StatedQuadPlus 4 k)) := by
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := statedClassicalModel_of_lieModel_pomega (Or.inl rfl) hS
  let σ : k ≃+* K' := fieldIsoOfCard (hk.trans hK'.symm)
  let ψ : StatedOmega (StatedQuadPlus 4 k) ≃* StatedOmega (StatedQuadPlus 4 K') :=
    ((glCongr σ).subgroupMap _).trans (MulEquiv.subgroupCongr
      (map_statedOmega σ (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp σ)))
  exact exists_surjective_ker_le_center_of_statedProj ψ e

end Plus

section Minus

theorem isPerfect_omegaMinus8 (k : Type) [Field k] [Finite k] {b c : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    Group.IsPerfect (StatedOmega (StatedQuadMinus 4 k b c)) :=
  isPerfect_statedOmega_quadMinus (by norm_num) hirr

theorem center_omegaMinus8 (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center (StatedOmega (StatedQuadMinus 4 k b c)) = ⊥ :=
  (center_statedOmega_quadMinus (by norm_num) hirr).trans
    (statedScalars_subgroupOf_statedOmega_eq_bot (coe_quadMinus 4 k b c)
      (exists_map_ne_zero_of_hypPair _ (minusPair k b c (⟨0, by norm_num⟩ : Fin (4 - 1)))))

theorem omegaMinus8_exists_section
    (k : Type) [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (E : Type) [Group E] [Finite E] (π : E →* StatedOmega (StatedQuadMinus 4 k b c))
    (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) :
    ∃ s : StatedOmega (StatedQuadMinus 4 k b c) →* E, ∀ g, π (s g) = g := by
  set Φ := spinMatrixEquiv (ker_spinMatrix_quadMinus_eq_bot (n := 4) hirr CharTwo.two_eq_zero)
    (range_spinMatrix_quadMinus (by norm_num) hirr)
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_central hirr
      (n := 4) (by norm_num) hk (π := Φ.symm.toMonoidHom.comp π) (Φ.symm.surjective.comp hπ)
      (by rw [ker_symm_comp]; exact hc)
  exact ⟨s.comp Φ.symm.toMonoidHom, fun g => Φ.symm.injective (hs (Φ.symm g))⟩

theorem omegaMinus8_covers (k : Type) [Field k] [Finite k] {f : ℕ} (hk : Nat.card k = 2 ^ f)
    {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) (S : Type) [Group S]
    (hS : CFSG.Blueprint.LieModel S .POmegaMinus 4 2 f) :
    ∃ π : StatedOmega (StatedQuadMinus 4 k b c) →* S, Function.Surjective π ∧
      π.ker ≤ Subgroup.center (StatedOmega (StatedQuadMinus 4 k b c)) := by
  obtain ⟨-, K', _, _, hK', b', c', hirr', ⟨e⟩⟩ :=
    statedClassicalModel_of_lieModel_pomega (Or.inr rfl) hS
  let σ : k ≃+* K' := fieldIsoOfCard (hk.trans hK'.symm)
  obtain ⟨g, hg⟩ := exists_gl_isometry_statedQuadMinus 4 (irreducible_map σ hirr) hirr'
  let ψ₁ : StatedOmega (StatedQuadMinus 4 k b c) ≃*
      StatedOmega (StatedQuadMinus 4 K' (σ b) (σ c)) :=
    ((glCongr σ).subgroupMap _).trans (MulEquiv.subgroupCongr
      (map_statedOmega σ (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp σ rfl rfl)))
  let ψ₂ : StatedOmega (StatedQuadMinus 4 K' (σ b) (σ c)) ≃*
      StatedOmega (StatedQuadMinus 4 K' b' c') :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr (map_statedOmega_conj g hg))
  exact exists_surjective_ker_le_center_of_statedProj (ψ₁.trans ψ₂) e

end Minus

end CFSG.SeitzReduction.F4Pilot
