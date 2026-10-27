module

public import CFSG.LieType.Chevalley.E6GraphHighestRootData
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

section Ops


abbrev Dr : Type := ↥degOneRoots

abbrev Rv (K : Type) : Type := Dr → K

variable (K : Type) [Field K]

@[expose] def eop (j : Fin TwistTag.E6.tag.rank) : Rv K →ₗ[K] Rv K where
  toFun v γ := if h : γ.1 - Pi.single j 1 ∈ degOneRoots then v ⟨γ.1 - Pi.single j 1, h⟩ else 0
  map_add' v w := by
    funext γ
    by_cases h : γ.1 - Pi.single j 1 ∈ degOneRoots <;> simp [h]
  map_smul' c v := by
    funext γ
    by_cases h : γ.1 - Pi.single j 1 ∈ degOneRoots <;> simp [h]

@[expose] def fop (j : Fin TwistTag.E6.tag.rank) : Rv K →ₗ[K] Rv K where
  toFun v γ := if h : γ.1 + Pi.single j 1 ∈ degOneRoots then v ⟨γ.1 + Pi.single j 1, h⟩ else 0
  map_add' v w := by
    funext γ
    by_cases h : γ.1 + Pi.single j 1 ∈ degOneRoots <;> simp [h]
  map_smul' c v := by
    funext γ
    by_cases h : γ.1 + Pi.single j 1 ∈ degOneRoots <;> simp [h]

@[expose] def xop (j : Fin TwistTag.E6.tag.rank) (c : K) : Rv K →ₗ[K] Rv K :=
  LinearMap.id + c • eop K j

@[expose] def yop (j : Fin TwistTag.E6.tag.rank) (c : K) : Rv K →ₗ[K] Rv K :=
  LinearMap.id + c • fop K j

@[expose] def xorb (σ : K ≃+* K) : Fin TwistTag.E6.foldedTag.rank → K → (Rv K →ₗ[K] Rv K)
  | 0, c => xop K 0 c ∘ₗ xop K 5 (σ c)
  | 1, c => xop K 2 c ∘ₗ xop K 4 (σ c)
  | 2, c => xop K 3 c
  | 3, c => xop K 1 c

@[expose] def yorb (σ : K ≃+* K) : Fin TwistTag.E6.foldedTag.rank → K → (Rv K →ₗ[K] Rv K)
  | 0, c => yop K 0 c ∘ₗ yop K 5 (σ c)
  | 1, c => yop K 2 c ∘ₗ yop K 4 (σ c)
  | 2, c => yop K 3 c
  | 3, c => yop K 1 c

@[expose] def rhoD (γ : Dr) : Dr :=
  ⟨permLattice TwistTag.E6.perm γ.1, permLattice_mem_degOneRoots γ.1 γ.2⟩

@[expose] def reflOrb (a : Fin TwistTag.E6.foldedTag.rank) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) γ

@[expose] def reflD (a : Fin TwistTag.E6.foldedTag.rank) (γ : Dr) : Dr :=
  if h : reflOrb a γ.1 ∈ degOneRoots then ⟨reflOrb a γ.1, h⟩ else γ

@[expose] def RPhi (σ : K ≃+* K) : AddSubgroup (Rv K) where
  carrier := {v | ∀ γ, v (rhoD γ) = σ (v γ)}
  add_mem' {v w} hv hw := fun γ => by simp [hv γ, hw γ]
  zero_mem' := fun γ => by simp
  neg_mem' {v} hv := fun γ => by simp [hv γ]

end Ops

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
