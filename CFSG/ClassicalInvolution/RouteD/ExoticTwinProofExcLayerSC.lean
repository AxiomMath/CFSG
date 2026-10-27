module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerAdj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section Assembly

variable {p : ℕ} [Fact p.Prime]

theorem hasQuasisimpleLayer_of_std {t : StatedLieTag} {n e : ℕ}
    (hfin : Finite (modelUniv t n p e Fact.out).K)
    (hsingle : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ∀ R' ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ∃ g, R' = conjSub g R)
    {Rstd R₂ : Subgroup (modelUniv t n p e Fact.out).K}
    (hRstd : Rstd ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (h : StdLayer Rstd R₂) : HasQuasisimpleLayer p t n e := by
  intro R₀ hR₀
  obtain ⟨g, hg⟩ := hsingle Rstd hRstd R₀ hR₀
  rw [hg]
  exact LayerAt.conj (fun S hS g => CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups
    hS g) (layerAt_of_stdLayer hsingle hR₂ h) g

end Assembly

section Adjoint

variable {p f n : ℕ} [Fact p.Prime]

theorem ringChar_galoisField_ne_two (hp2 : p ≠ 2) : ringChar (GaloisField p f) ≠ 2 := by
  rw [ringChar.eq (GaloisField p f) p]
  exact hp2

theorem hasQuasisimpleLayer_F4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .F4 n p f) : HasQuasisimpleLayer p .F4 n f := by
  have hfund : IsFundTag .F4 := trivial
  obtain ⟨-, h5⟩ := CFSG.ClassicalInvolution.ModelFacts.odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨δ₂, δ₃, hS, hlong⟩ := layerShape_F4
  have hstd := stdLayer_adjoint (K := GaloisField p f) (ringChar_galoisField_ne_two hp2) h5
    (⟨0, by decide⟩ : Fin Tag.F4.rank) hS
  have hfin : Finite (modelUniv .F4 n p f Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .F4 n p f Fact.out
    trivial hadm (by decide) (by decide)
  have hlongE := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .F4 n p f Fact.out
    trivial hadm ⟨0, by show 0 < 4; decide⟩ (by show 0 < 2; decide)
  refine hasQuasisimpleLayer_of_std hfin hsingle ?_ ?_ hstd
  · exact ⟨1, _, Or.inl hlongE, (conjSub_one _).symm⟩
  · exact ⟨1, δ₂, Or.inl (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_f4Datum_of_iform_eq_four
      hS.mem₂.1 hlong), (conjSub_one _).symm⟩

theorem hasQuasisimpleLayer_E8 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .E8 n p f) : HasQuasisimpleLayer p .E8 n f := by
  have hfund : IsFundTag .E8 := trivial
  obtain ⟨-, h5⟩ := CFSG.ClassicalInvolution.ModelFacts.odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E8
  have hstd := stdLayer_adjoint (K := GaloisField p f) (ringChar_galoisField_ne_two hp2) h5
    (⟨0, by decide⟩ : Fin Tag.E8.rank) hS
  have hfin : Finite (modelUniv .E8 n p f Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E8 n p f Fact.out
    trivial hadm (by decide) (by decide)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E8 n p f Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ →
      IsLongestRoot (modelUniv .E8 n p f Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial) (mem_adjDatum_roots.2 hγ)
  refine hasQuasisimpleLayer_of_std hfin hsingle ?_ ?_ hstd
  · exact ⟨1, _, Or.inl (hall _ (IsRoot.basis _)), (conjSub_one _).symm⟩
  · exact ⟨1, δ₂, Or.inl (hall _ hS.mem₂.1), (conjSub_one _).symm⟩

end Adjoint

section Isogeny

variable {p f n : ℕ} [Fact p.Prime]

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits

theorem hasQuasisimpleLayer_E6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .E6 n p f) : HasQuasisimpleLayer p .E6 n f := by
  obtain rfl : n = 0 := hadm.2.2
  have hfund : IsFundTag .E6 := trivial
  obtain ⟨-, h5⟩ := CFSG.ClassicalInvolution.ModelFacts.odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E6
  have hstd := stdLayer_adjoint (K := GaloisField p f) (ringChar_galoisField_ne_two hp2) h5
    (⟨0, by decide⟩ : Fin Tag.E6.rank) hS
  have hfin : Finite (modelUniv .E6 0 p f Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E6 0 p f
    Fact.out trivial hadm (by decide) (by decide)
  have hperf := CFSG.ClassicalInvolution.RouteD.Gaps.fundPerfect_modelUniv hp2 hfund hadm
    (by omega)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E6 0 p f Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      IsLongestRoot (modelUniv .E6 0 p f Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial)
      ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField p f)).2 hγ)
  have hqs := isQuasisimple_e6 (GaloisField p f)
  have hθ := e6Isogeny_surjective (GaloisField p f)
  have hker : (e6Isogeny (GaloisField p f)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (e6Isogeny_ne_one (GaloisField p f))
  set e : Fin Tag.E6.rank → ℤ := Pi.single ⟨0, by decide⟩ 1 with he
  set Rstd : Subgroup ↥(e6Data_valid.minGroup (GaloisField p f)) :=
    (e6Datum (GaloisField p f)).rootGroup e ⊔
      (e6Datum (GaloisField p f)).rootGroup (-e) with hRstd
  set R₂ : Subgroup ↥(e6Data_valid.minGroup (GaloisField p f)) :=
    (e6Datum (GaloisField p f)).rootGroup δ₂ ⊔
      (e6Datum (GaloisField p f)).rootGroup (-δ₂) with hR₂
  have hRstdmem : Rstd ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 p f Fact.out).D :=
    ⟨1, e, Or.inl (hall e (IsRoot.basis _)), (conjSub_one _).symm⟩
  have hR₂mem : R₂ ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 p f Fact.out).D :=
    ⟨1, δ₂, Or.inl (hall δ₂ hS.mem₂.1), (conjSub_one _).symm⟩
  have himg : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      ((e6Datum (GaloisField p f)).rootGroup γ ⊔
          (e6Datum (GaloisField p f)).rootGroup (-γ)).map
        (e6Isogeny (GaloisField p f)) =
        rootGroup (rootOperatorFamily .E6) (GaloisField p f) γ ⊔
          rootGroup (rootOperatorFamily .E6) (GaloisField p f) (-γ) := fun γ hγ => by
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup _ hγ)
      (CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup _ (IsRoot.neg hγ))
  exact hasQuasisimpleLayer_of_std hfin hsingle hRstdmem hR₂mem
    (StdLayer.of_central_cover (e6Isogeny (GaloisField p f)) hθ hker
      (hperf Rstd hRstdmem) (hperf R₂ hR₂mem) (himg e (IsRoot.basis _))
      (himg δ₂ hS.mem₂.1) hstd)

theorem hasQuasisimpleLayer_E7 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .E7 n p f) : HasQuasisimpleLayer p .E7 n f := by
  obtain rfl : n = 0 := hadm.2.2
  have hfund : IsFundTag .E7 := trivial
  obtain ⟨-, h5⟩ := CFSG.ClassicalInvolution.ModelFacts.odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E7
  have hstd := stdLayer_adjoint (K := GaloisField p f) (ringChar_galoisField_ne_two hp2) h5
    (⟨0, by decide⟩ : Fin Tag.E7.rank) hS
  have hfin : Finite (modelUniv .E7 0 p f Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E7 0 p f
    Fact.out trivial hadm (by decide) (by decide)
  have hperf := CFSG.ClassicalInvolution.RouteD.Gaps.fundPerfect_modelUniv hp2 hfund hadm
    (by omega)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E7 0 p f Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      IsLongestRoot (modelUniv .E7 0 p f Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2 hγ)
  have hqs := isQuasisimple_e7 (GaloisField p f)
  have hθ := e7Isogeny_surjective (GaloisField p f)
  have hker : (e7Isogeny (GaloisField p f)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (exists_e7Isogeny_ne_one (GaloisField p f))
  set e : Fin Tag.E7.rank → ℤ := Pi.single ⟨0, by decide⟩ 1 with he
  set Rstd : Subgroup ↥(e7Data_valid.minGroup (GaloisField p f)) :=
    (e7Datum (GaloisField p f)).rootGroup e ⊔
      (e7Datum (GaloisField p f)).rootGroup (-e) with hRstd
  set R₂ : Subgroup ↥(e7Data_valid.minGroup (GaloisField p f)) :=
    (e7Datum (GaloisField p f)).rootGroup δ₂ ⊔
      (e7Datum (GaloisField p f)).rootGroup (-δ₂) with hR₂
  have hRstdmem : Rstd ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D :=
    ⟨1, e, Or.inl (hall e (IsRoot.basis _)), (conjSub_one _).symm⟩
  have hR₂mem : R₂ ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D :=
    ⟨1, δ₂, Or.inl (hall δ₂ hS.mem₂.1), (conjSub_one _).symm⟩
  have himg : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      ((e7Datum (GaloisField p f)).rootGroup γ ⊔
          (e7Datum (GaloisField p f)).rootGroup (-γ)).map
        (e7Isogeny (GaloisField p f)) =
        rootGroup (rootOperatorFamily .E7) (GaloisField p f) γ ⊔
          rootGroup (rootOperatorFamily .E7) (GaloisField p f) (-γ) := fun γ hγ => by
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup _ hγ)
      (CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup _ (IsRoot.neg hγ))
  exact hasQuasisimpleLayer_of_std hfin hsingle hRstdmem hR₂mem
    (StdLayer.of_central_cover (e7Isogeny (GaloisField p f)) hθ hker
      (hperf Rstd hRstdmem) (hperf R₂ hR₂mem) (himg e (IsRoot.basis _))
      (himg δ₂ hS.mem₂.1) hstd)

end Isogeny

end CFSG.ClassicalInvolution.RouteD.Exotic
