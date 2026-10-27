module

public import CFSG.ClassicalInvolution.Uniform.U9NoExcSplit
public import CFSG.ClassicalInvolution.Uniform.U9NoExcTw

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.ModelFacts (Gen3 gen3_of_equiv_sl2)
open scoped MatrixGroups commutatorElement



section F4E8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3 (uniqIsolated_F4 uniqIsolated_E8)

variable {n : ℕ}

theorem noTwinExc3_F4 (hadm : StatedLieAdmissible .F4 n 3 1) :
    ∀ R₁ ∈ fundamentalSubgroups .F4 (modelUniv .F4 n 3 1 Fact.out).D,
    ∀ R₂ ∈ fundamentalSubgroups .F4 (modelUniv .F4 n 3 1 Fact.out).D, R₁ ≠ R₂ →
    ∀ (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)),
      sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center (modelUniv .F4 n 3 1 Fact.out).K := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag .F4 := trivial
  obtain ⟨δ₂, δ₃, hS, hlong⟩ := layerShape_F4
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .F4 n 3 1 Fact.out
    trivial hadm (by decide) (by decide)
  have hlongE := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .F4 n 3 1 Fact.out
    trivial hadm ⟨0, by show 0 < 4; decide⟩ (by show 0 < 2; decide)
  have hRstd := (⟨1, _, Or.inl hlongE, (conjSub_one _).symm⟩ :
    _ ∈ fundamentalSubgroups .F4 (modelUniv .F4 n 3 1 Fact.out).D)
  have hgen : ∀ R ∈ fundamentalSubgroups .F4 (modelUniv .F4 n 3 1 Fact.out).D, Gen3 R := by
    intro R hR
    obtain ⟨φ⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 hfund hadm (by decide) (by decide) hR
    exact gen3_of_equiv_sl2 φ
  obtain ⟨e₀⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRstd
  intro R₁ h₁ R₂ h₂ hne e₁ e₂
  exact twinRatio_notMem_center_adjoint (τ := .F4) (⟨0, by decide⟩ : Fin Tag.F4.rank) hS
    uniqIsolated_F4 hsingle hgen hRstd rfl e₀ h₁ h₂ hne e₁ e₂

theorem noTwinExc3_E8 (hadm : StatedLieAdmissible .E8 n 3 1) :
    ∀ R₁ ∈ fundamentalSubgroups .E8 (modelUniv .E8 n 3 1 Fact.out).D,
    ∀ R₂ ∈ fundamentalSubgroups .E8 (modelUniv .E8 n 3 1 Fact.out).D, R₁ ≠ R₂ →
    ∀ (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)),
      sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center (modelUniv .E8 n 3 1 Fact.out).K := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag .E8 := trivial
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E8
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E8 n 3 1 Fact.out
    trivial hadm (by decide) (by decide)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E8 n 3 1 Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ →
      IsLongestRoot (modelUniv .E8 n 3 1 Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial) (mem_adjDatum_roots.2 hγ)
  have hRstd := (⟨1, _, Or.inl (hall _ (IsRoot.basis (⟨0, by decide⟩ : Fin Tag.E8.rank))),
    (conjSub_one _).symm⟩ : _ ∈ fundamentalSubgroups .E8 (modelUniv .E8 n 3 1 Fact.out).D)
  have hgen : ∀ R ∈ fundamentalSubgroups .E8 (modelUniv .E8 n 3 1 Fact.out).D, Gen3 R := by
    intro R hR
    obtain ⟨φ⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 hfund hadm (by decide) (by decide) hR
    exact gen3_of_equiv_sl2 φ
  obtain ⟨e₀⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRstd
  intro R₁ h₁ R₂ h₂ hne e₁ e₂
  exact twinRatio_notMem_center_adjoint (τ := .E8) (⟨0, by decide⟩ : Fin Tag.E8.rank) hS
    uniqIsolated_E8 hsingle hgen hRstd rfl e₀ h₁ h₂ hne e₁ e₂

end F4E8

section Isogeny

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.Exotic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3 (uniqIsolated_E6 uniqIsolated_E7)

variable {n : ℕ}

theorem noTwinExc3_E6 (hadm : StatedLieAdmissible .E6 n 3 1) :
    ∀ R₁ ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 3 1 Fact.out).D,
    ∀ R₂ ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 3 1 Fact.out).D, R₁ ≠ R₂ →
    ∀ (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)),
      sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center (modelUniv .E6 0 3 1 Fact.out).K := by
  classical
  obtain rfl : n = 0 := hadm.2.2
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag .E6 := trivial
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E6
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E6 0 3 1
    Fact.out trivial hadm (by decide) (by decide)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E6 0 3 1 Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      IsLongestRoot (modelUniv .E6 0 3 1 Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial)
      ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField 3 1)).2 hγ)
  have hqs := isQuasisimple_e6 (GaloisField 3 1)
  have hθ := e6Isogeny_surjective (GaloisField 3 1)
  have hker : (e6Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (e6Isogeny_ne_one (GaloisField 3 1))
  have hk3 : ∀ x ∈ (e6Isogeny (GaloisField 3 1)).ker, x ^ 3 = 1 → x = 1 := fun x hx hx3 =>
    CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime .E6 0 3 1 Nat.prime_three
      hp2 hfund hadm x (hker hx) hx3
  set e : Fin Tag.E6.rank → ℤ := Pi.single ⟨0, by decide⟩ 1 with he
  set Rstd : Subgroup ↥(e6Data_valid.minGroup (GaloisField 3 1)) :=
    (e6Datum (GaloisField 3 1)).rootGroup e ⊔
      (e6Datum (GaloisField 3 1)).rootGroup (-e) with hRstd
  have hRstdmem : Rstd ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 3 1 Fact.out).D :=
    ⟨1, e, Or.inl (hall e (IsRoot.basis _)), (conjSub_one _).symm⟩
  have himg : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      ((e6Datum (GaloisField 3 1)).rootGroup γ ⊔
          (e6Datum (GaloisField 3 1)).rootGroup (-γ)).map
        (e6Isogeny (GaloisField 3 1)) =
        rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) γ ⊔
          rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-γ) := fun γ hγ => by
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup _ hγ)
      (CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup _ (IsRoot.neg hγ))
  have hgen : ∀ R ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 3 1 Fact.out).D, Gen3 R := by
    intro R hR
    obtain ⟨φ⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 hfund hadm (by decide) (by decide) hR
    exact gen3_of_equiv_sl2 φ
  obtain ⟨e₀⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRstdmem
  have hinj : ∀ x ∈ Rstd, (e6Isogeny (GaloisField 3 1)) x = 1 → x = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic 3 .E6 0 1 hfund hadm
        (by simp) Rstd hRstdmem r hr hcen
  intro R₁ h₁ R₂ h₂ hne e₁ e₂
  exact twinRatio_notMem_center_cover (e6Isogeny (GaloisField 3 1)) hθ hker hk3
    (⟨0, by decide⟩ : Fin Tag.E6.rank) hS uniqIsolated_E6 hsingle hgen hRstdmem e₀
    (himg e (IsRoot.basis _)) hinj h₁ h₂ hne e₁ e₂

theorem noTwinExc3_E7 (hadm : StatedLieAdmissible .E7 n 3 1) :
    ∀ R₁ ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Fact.out).D,
    ∀ R₂ ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Fact.out).D, R₁ ≠ R₂ →
    ∀ (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)),
      sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center (modelUniv .E7 0 3 1 Fact.out).K := by
  classical
  obtain rfl : n = 0 := hadm.2.2
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag .E7 := trivial
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E7
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E7 0 3 1
    Fact.out trivial hadm (by decide) (by decide)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E7 0 3 1 Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      IsLongestRoot (modelUniv .E7 0 3 1 Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2 hγ)
  have hqs := isQuasisimple_e7 (GaloisField 3 1)
  have hθ := e7Isogeny_surjective (GaloisField 3 1)
  have hker : (e7Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (exists_e7Isogeny_ne_one (GaloisField 3 1))
  have hk3 : ∀ x ∈ (e7Isogeny (GaloisField 3 1)).ker, x ^ 3 = 1 → x = 1 := fun x hx hx3 =>
    CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime .E7 0 3 1 Nat.prime_three
      hp2 hfund hadm x (hker hx) hx3
  set e : Fin Tag.E7.rank → ℤ := Pi.single ⟨0, by decide⟩ 1 with he
  set Rstd : Subgroup ↥(e7Data_valid.minGroup (GaloisField 3 1)) :=
    (e7Datum (GaloisField 3 1)).rootGroup e ⊔
      (e7Datum (GaloisField 3 1)).rootGroup (-e) with hRstd
  have hRstdmem : Rstd ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Fact.out).D :=
    ⟨1, e, Or.inl (hall e (IsRoot.basis _)), (conjSub_one _).symm⟩
  have himg : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      ((e7Datum (GaloisField 3 1)).rootGroup γ ⊔
          (e7Datum (GaloisField 3 1)).rootGroup (-γ)).map
        (e7Isogeny (GaloisField 3 1)) =
        rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) γ ⊔
          rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) (-γ) := fun γ hγ => by
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup _ hγ)
      (CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup _ (IsRoot.neg hγ))
  have hgen : ∀ R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Fact.out).D, Gen3 R := by
    intro R hR
    obtain ⟨φ⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 hfund hadm (by decide) (by decide) hR
    exact gen3_of_equiv_sl2 φ
  obtain ⟨e₀⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRstdmem
  have hinj : ∀ x ∈ Rstd, (e7Isogeny (GaloisField 3 1)) x = 1 → x = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic 3 .E7 0 1 hfund hadm
        (by simp) Rstd hRstdmem r hr hcen
  intro R₁ h₁ R₂ h₂ hne e₁ e₂
  exact twinRatio_notMem_center_cover (e7Isogeny (GaloisField 3 1)) hθ hker hk3
    (⟨0, by decide⟩ : Fin Tag.E7.rank) hS uniqIsolated_E7 hsingle hgen hRstdmem e₀
    (himg e (IsRoot.basis _)) hinj h₁ h₂ hne e₁ e₂

end Isogeny

section Final

open CFSG.Assembly.LowTwoRank

theorem noTwinExc3 :
    ∀ (t : StatedLieTag) (k : ℕ), (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
      StatedLieAdmissible t k 3 1 →
      ∀ R₁ ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups t
        (CFSG.ClassicalInvolution.ModelFacts.modelUniv t k 3 1 Fact.out).D,
      ∀ R₂ ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups t
        (CFSG.ClassicalInvolution.ModelFacts.modelUniv t k 3 1 Fact.out).D, R₁ ≠ R₂ →
      ∀ (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)),
        sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉
          Subgroup.center (CFSG.ClassicalInvolution.ModelFacts.modelUniv t k 3 1 Fact.out).K := by
  intro t k ht hadm
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact noTwinExc3_F4 hadm
  · obtain rfl : k = 0 := hadm.2.2
    exact noTwinExc3_E6 hadm
  · obtain rfl : k = 0 := hadm.2.2
    exact noTwinExc3_E7 hadm
  · exact noTwinExc3_E8 hadm
  · obtain rfl : k = 0 := hadm.2.2
    exact noTwinExc3_twistedE6 hadm

end Final

end CFSG.ClassicalInvolution.Uniform
