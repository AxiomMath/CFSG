module

public import CFSG.CharacterTheory.Semidihedral.FixedTorusDerived
public import CFSG.CharacterTheory.Semidihedral.LocalLayerAbelianQuotients
public import CFSG.CharacterTheory.Semidihedral.CentralKernelTorusSplitModel
public import CFSG.CharacterTheory.Semidihedral.MatrixFourGroupNormalizer

public section

namespace CFSG.Semidihedral.StationaryConfinement

noncomputable section

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData
open CFSG.Semidihedral.ActualFourGroupCentralizer (originalOddInclusion OriginalWProduct
  fixed_coefficient_action)
open CFSG.Semidihedral.CentralKernelTorusSplit (commutator_le_originalSlInH_range
  originalOddInclusion_mem_range_iff card_SL_two_congr)

theorem fixed_core_derived_centralizer_le_layer {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap
          (nu t)).map (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    let D := Subgroup.centralizer ({s} : Set (C t))
    let R := (CFSG.pPrimeCore 2 D).map D.subtype
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    ⁅R, R⁆ ≤ Y ∧ ∀ x ∈ R, (∀ y ∈ ⁅R, R⁆, x * y = y * x) → x ∈ Y := by
  intro D R T₀ Y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCY : commutator (C t) ≤ Y :=
    (LocalLayerAbelianQuotients.original_local_layer_preimage_has_abelian_quotient n hn S0 f0 hG
      t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel).2
  have hRR : ⁅R, R⁆ ≤ Y := by
    refine le_trans ?_ hCY
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  refine ⟨hRR, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨F', hF', hF'fin, eta', -, hF'card, -, -, -, -⟩,
      -, -, -⟩ :=
    (Local.all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel).1 hcov
  have hcardT₀' : Nat.card T₀ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F') :=
    Nat.card_congr eta'.toEquiv
  obtain ⟨-, F, hF, hFfin, A, a, hFcard, hAodd, -, -, -, -, -, haF, -, -, htorus, hPsiex⟩ :=
    ActualFourGroupCentralizer.actual_simple_layer_four_group_centralizer_odd_core
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, -, -, hCdata, -⟩ := hPsiex s hs hst
  set a' := MatrixCover.fixedUnit F A a with ha'
  have hfix : ∀ sigma : A, (sigma : F ≃+* F) (a' : F) = a' := fixed_coefficient_action F A a
  have hFodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
  obtain ⟨-, -, -, hAutcyc, -, -⟩ :=
    CFSG.Semidihedral.SemilinearOuterQuotient.odd_field_projective_semilinear_exact_outer_quotient
      F hp hpodd hf hFcard
  have hAcyc : IsCyclic A := Subgroup.isCyclic A
  have hAcomm : ∀ σ τ : A, σ * τ = τ * σ := by
    obtain ⟨g, hg⟩ := hAcyc.exists_generator
    intro σ τ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg σ)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg τ)
    exact (Commute.zpow_zpow_self g i j).eq
  have hT₀perf : Group.IsPerfect T₀ := by
    have : Fintype F' := Fintype.ofFinite F'
    have h4 : ∃ s : Finset F', s.card = 4 := by
      obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F'))
        (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF'card]; omega)
      exact ⟨u, hu⟩
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    exact Group.IsPerfect.ofSurjective (f := eta'.symm.toMonoidHom) eta'.symm.surjective
  let SLim := (originalSlInH F a' A hfix).range
  have hSLinj := MatrixFourGroupNormalizer.originalSlInH_injective F a' A hfix
  have hcommH : commutator (H t) =
      (commutator (OriginalH F a' A hfix)).map Psi.toMonoidHom := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ Psi.surjective]
  have hT₀le : T₀ ≤ SLim.map Psi.toMonoidHom :=
    calc T₀ = ⁅T₀, T₀⁆ := (Subgroup.isPerfect_iff.mp hT₀perf).symm
      _ ≤ commutator (H t) := Subgroup.commutator_mono le_top le_top
      _ = (commutator (OriginalH F a' A hfix)).map Psi.toMonoidHom := hcommH
      _ ≤ SLim.map Psi.toMonoidHom :=
        Subgroup.map_mono (commutator_le_originalSlInH_range F a' A hfix hAcomm)
  have hcardT₀ : Nat.card (SLim.map Psi.toMonoidHom) ≤ Nat.card T₀ := by
    rw [Subgroup.card_map_of_injective Psi.injective, hcardT₀',
      ← Nat.card_congr (MonoidHom.ofInjective hSLinj).toEquiv]
    exact (card_SL_two_congr (hFcard.trans hF'card.symm)).le
  have hT₀eq : T₀ = SLim.map Psi.toMonoidHom := Subgroup.eq_of_le_of_card_ge hT₀le hcardT₀
  let Ds := ActualFourGroupCentralizer.D s
  let Rs := ActualFourGroupCentralizer.R s
  let N0 := ActualFourGroupCentralizer.N0InR s
  have : N0.Normal := hCdata.kernel_normal
  have hRs : (Rs : Subgroup Ds) = CFSG.pPrimeCore 2 Ds :=
    CFSG.Semidihedral.KleinFourOddKernel.piCore_odd_eq_pPrimeCore
  obtain ⟨eR, heR⟩ := hCdata.original_quotient
  let ψ : Rs →* OriginalWProduct F A a' hfix := eR.toMonoidHom.comp (QuotientGroup.mk' N0)
  have hψsurj : Function.Surjective ψ :=
    eR.surjective.comp (QuotientGroup.mk'_surjective N0)
  obtain ⟨-, -, -, -, -, -, -, -, hderived, -⟩ :=
    FixedTorusDerived.odd_field_fixed_torus_derived_subgroup_has_exact_torus_centralizer
      F hp hpodd hf hFcard A hAodd a' haF hfix
  have hcentW : Subgroup.centralizer
      (commutator (OriginalWProduct F A a' hfix) : Set (OriginalWProduct F A a' hfix)) =
        (SemidirectProduct.inl : MatrixTorus.W F a' →* OriginalWProduct F A a' hfix).range :=
    hderived
  have hcommψ : (commutator Rs).map ψ = commutator (OriginalWProduct F A a' hfix) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hψsurj]
  let ι : Rs →* C t := Ds.subtype.comp Rs.subtype
  have hRι : R = (⊤ : Subgroup Rs).map ι := by
    change (CFSG.pPrimeCore 2 Ds).map Ds.subtype = _
    rw [← hRs, ← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype]
  intro x hxR hxc
  rw [hRι] at hxR
  obtain ⟨x₀, -, rfl⟩ := hxR
  have hx₀c : ψ x₀ ∈ Subgroup.centralizer
      (commutator (OriginalWProduct F A a' hfix) : Set (OriginalWProduct F A a' hfix)) := by
    rw [Subgroup.mem_centralizer_iff, ← hcommψ]
    rintro _ ⟨y₀, hy₀, rfl⟩
    have hyR : ι y₀ ∈ ⁅R, R⁆ := by
      rw [hRι, ← Subgroup.map_commutator, ← commutator_def]
      exact Subgroup.mem_map_of_mem ι hy₀
    have h := hxc (ι y₀) hyR
    have hιinj : Function.Injective ι := Ds.subtype_injective.comp Rs.subtype_injective
    have h' : x₀ * y₀ = y₀ * x₀ := by
      apply hιinj
      rw [map_mul, map_mul]
      exact h
    rw [← map_mul, ← map_mul, h']
  rw [hcentW] at hx₀c
  obtain ⟨w₀, hw₀⟩ := hx₀c
  have hmem : originalOddInclusion F A a' hfix (eR (QuotientGroup.mk' N0 x₀)) ∈ SLim := by
    apply (originalOddInclusion_mem_range_iff F a' A hfix _).mpr
    change (ψ x₀).right = 1
    rw [← hw₀]
    rfl
  have hY : nu t (ι x₀) ∈ T₀ := by
    rw [hT₀eq]
    refine ⟨_, hmem, ?_⟩
    exact heR x₀
  exact hY

end

end CFSG.Semidihedral.StationaryConfinement
