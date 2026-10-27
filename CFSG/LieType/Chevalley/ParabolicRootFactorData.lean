module

public import CFSG.LieType.Chevalley.StandardParabolic

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable (τ : Tag)

@[expose] def parabolicRoots (J : Set (Fin τ.rank)) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ ∀ i ∉ J, α i = 0}

@[expose] def parabolicPosRoots (J : Set (Fin τ.rank)) : Set (Fin τ.rank → ℤ) :=
  parabolicRoots τ J ∩ {α | IsRoot τ α ∧ 0 < height α}

@[expose] def parabolicRadicalRoots (J : Set (Fin τ.rank)) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ 0 < height α} \ parabolicPosRoots τ J

@[expose] def parabolicRadicalRootsGe (J : Set (Fin τ.rank)) (h : ℤ) : Set (Fin τ.rank → ℤ) :=
  {α ∈ parabolicRadicalRoots τ J | h ≤ height α}

open _root_.Classical in
@[expose] def parabolicDegree (J : Set (Fin τ.rank)) (v : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, if i ∈ J then 0 else v i

variable (K : Type*) [Field K]

@[expose] def parabolicRadical
    (J : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  rootSpan τ K (parabolicRadicalRoots τ J)

@[expose] def parabolicLeviUnipotent
    (J : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  rootSpan τ K (parabolicPosRoots τ J)

@[expose] def parabolicLevi
    (J : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  torusGroup τ K ⊔ Subgroup.closure
    {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}

@[expose] def parabolicRadicalGe
    (J : Set (Fin τ.rank)) (h : ℤ) : Subgroup (ModGL τ K) :=
  rootSpan τ K (parabolicRadicalRootsGe τ J h)

@[expose] def parabolicGraded (J : Set (Fin τ.rank)) (d : ℤ) : Submodule K (RootModule τ K) :=
  Submodule.span K ({x | ∃ α, IsRoot τ α ∧ parabolicDegree τ J α = d ∧ x = rootVec τ K α} ∪
    {x | d = 0 ∧ ∃ i, x = hVec τ K i})

@[expose] def parabolicFiltration (J : Set (Fin τ.rank)) (d : ℤ) :
    Submodule K (RootModule τ K) :=
  ⨆ (s : ℤ) (_ : d ≤ s), parabolicGraded τ K J s

theorem parabolicLevi_le_adjointGroup
    (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J ≤ adjointGroup τ K := by
  refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_adjointGroup i t
  · rintro _ ⟨j, -, c, rfl | rfl⟩
    · exact xUnit_mem_adjointGroup j c
    · exact yUnit_mem_adjointGroup j c

theorem parabolicFiltration_antitone (J : Set (Fin τ.rank)) {d d' : ℤ} (h : d ≤ d') :
    parabolicFiltration τ K J d' ≤ parabolicFiltration τ K J d :=
  iSup₂_le fun s hs => le_iSup₂_of_le s (h.trans hs) le_rfl

end CFSG.LieType.Chevalley
