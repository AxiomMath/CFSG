module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Model
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Lift
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

theorem map_symm_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) (S : Subgroup B) :
    (S.map e.symm.toMonoidHom).map e.toMonoidHom = S := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩

theorem finite_linearEquiv {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : Finite (V ≃ₗ[K] V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    (fun g h hgh => LinearEquiv.ext (congrFun hgh))

attribute [local instance] finite_linearEquiv

variable {H : Type} [Group H] [Finite H] {G : Subgroup H} [G.Normal] {K : Type} [Field K]
  [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {Θ : G ≃* projectiveDerived Q} {t : H} (D : InvData G Q Θ t)
  {T : Type} [Group T] (ι : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃* T)

abbrev FN := (orthogonalDerived Q).subgroupOf
  (fixedSubgroup (similarityConjugation Q D.A D.μ D.hsim))

@[expose] def epsT : FN D →* T :=
  ι.toMonoidHom.comp ((fixedCentralizerEquiv Q D.A D.μ D.hsim).toMonoidHom.comp
    (FN D).subtype)

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem epsT_injective : Function.Injective (epsT D ι) :=
  ι.injective.comp ((fixedCentralizerEquiv Q D.A D.μ D.hsim).injective.comp
    (subtype_injective _))

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem epsT_symm_val (x : FN D) : (ι.symm (epsT D ι x)).val = x.val.val := by
  simp [epsT, fixedCentralizerEquiv]

abbrev toHD : FN D →* H := toH G Q Θ t D.A D.μ D.hsim D.hconj

omit [Finite H] in
theorem epsT_up [Finite T] (M : Subgroup (FN D)) (hM : IsPComponent 2 M) :
    IsPComponent 2 (M.map (epsT D ι)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (chain_normal_iff (orthogonalDerived Q)
    (similarityConjugation Q D.A D.μ D.hsim) M).mp hM
  have h2 := CatalogueBAlternating.pComponent_map_equiv 2
    ((fixedCentralizerEquiv Q D.A D.μ D.hsim).trans ι) _ h1
  rw [map_map] at h2
  exact h2

omit [Finite H] in
theorem epsT_down [Finite T] (M' : Subgroup T) (hM' : IsPComponent 2 M') :
    ∃ M : Subgroup (FN D), IsPComponent 2 M ∧ M.map (epsT D ι) = M' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := (fixedCentralizerEquiv Q D.A D.μ D.hsim).trans ι
  have h1 := CatalogueBAlternating.pComponent_map_equiv 2 e.symm M' hM'
  have hle := chain_le (orthogonalDerived Q) (similarityConjugation Q D.A D.μ D.hsim)
    (le_refl _) _ h1
  refine ⟨(M'.map e.symm.toMonoidHom).subgroupOf (FN D), ?_, ?_⟩
  · rw [chain_normal_iff (orthogonalDerived Q) (similarityConjugation Q D.A D.μ D.hsim),
      map_subgroupOf_eq_of_le hle]
    exact h1
  · have h2 : epsT D ι = e.toMonoidHom.comp (FN D).subtype := rfl
    rw [h2, ← map_map, map_subgroupOf_eq_of_le hle]
    exact map_symm_map e M'

theorem corr_down [Finite T] (L : Subgroup H) (hLC : L ≤ centralizer ({t} : Set H))
    (hLG : L ≤ G) (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H)))) :
    ∃ M : Subgroup (FN D), IsPComponent 2 M ∧ M.map (toHD D) = L ∧
      IsPComponent 2 (M.map (epsT D ι)) := by
  obtain ⟨M, hM, hML⟩ := toH_down G Q Θ t D.A D.μ D.hsim D.hconj L hLC hLG hL
  exact ⟨M, hM, hML, epsT_up D ι M hM⟩

theorem corr_up [Finite T] (M' : Subgroup T) (hM' : IsPComponent 2 M') :
    ∃ M : Subgroup (FN D), IsPComponent 2 M ∧ M.map (epsT D ι) = M' ∧
      M.map (toHD D) ≤ centralizer ({t} : Set H) ∧ M.map (toHD D) ≤ G ∧
      IsPComponent 2 ((M.map (toHD D)).subgroupOf (centralizer ({t} : Set H))) := by
  obtain ⟨M, hM, hMM'⟩ := epsT_down D ι M' hM'
  obtain ⟨h1, h2, h3⟩ := toH_up G Q Θ t D.A D.μ D.hsim D.hconj M hM
  exact ⟨M, hM, hMM', h1, h2, h3⟩

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem corr_inj (M₁ M₂ : Subgroup (FN D)) (h₁ : IsPComponent 2 M₁) (h₂ : IsPComponent 2 M₂)
    (h : M₁.map (toHD D) = M₂.map (toHD D)) : M₁.map (epsT D ι) = M₂.map (epsT D ι) := by
  rw [toH_inj G Q Θ t D.A D.μ D.hsim D.hconj M₁ M₂ h₁ h₂ h]

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem toHD_ker_central (M : Subgroup (FN D)) (x : M) (hx : toHD D x = 1) : x ∈ center M := by
  have hZ : x.val.val.val ∈ scalarSigns Q :=
    (toH_eq_one_iff G Q Θ t D.A D.μ D.hsim D.hconj x.val).mp hx
  refine mem_center_iff.mpr fun y => Subtype.ext (Subtype.ext (Subtype.ext ?_))
  change y.val.val.val * x.val.val.val = x.val.val.val * y.val.val.val
  exact mem_center_iff.mp (scalarSigns_central Q hZ) y.val.val.val

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem card_dvd (M : Subgroup (FN D)) :
    Nat.card (M.map (toHD D)) ∣ Nat.card (M.map (epsT D ι)) := by
  rw [Subgroup.card_map_of_injective (epsT_injective D ι)]
  exact Subgroup.card_map_dvd (H := M) (toHD D)

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem centerQuotient_equiv (M : Subgroup (FN D)) (hq : IsQuasisimple (M.map (epsT D ι))) :
    IsQuasisimple (M.map (toHD D)) ∧
      Nonempty ((M.map (toHD D)) ⧸ center (M.map (toHD D)) ≃*
        (M.map (epsT D ι)) ⧸ center (M.map (epsT D ι))) := by
  have hqM : IsQuasisimple M := LocalCores.isQuasisimple_of_mulEquiv
    (M.equivMapOfInjective _ (epsT_injective D ι)).symm hq
  set f := (toHD D).subgroupMap M
  have hf : Function.Surjective f := (toHD D).subgroupMap_surjective M
  have hker : f.ker ≤ center M := by
    intro x hx
    apply toHD_ker_central D M x
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact this
  obtain ⟨hquot, -, -⟩ := LocalAnalysis.ComponentInitial.quasisimple_central_quotient hqM hker
  have hqL : IsQuasisimple (M.map (toHD D)) := LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientKerEquivOfSurjective f hf) hquot
  obtain ⟨e1⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hqM f hf hker
  have e2 : M ≃* M.map (epsT D ι) := M.equivMapOfInjective _ (epsT_injective D ι)
  exact ⟨hqL, ⟨e1.symm.trans (QuotientGroup.congr _ _ e2 (Subgroup.map_center_eq e2))⟩⟩

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
