module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankUntw

public section

namespace CFSG.HardMathSupport.Lang.AlphaThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.AGLEmbedding.KFactProofs.CoverE6

abbrev E6Vec := Fin TwistTag.E6.tag.rank → ℤ

@[expose] def fourRootsE (j : Fin 4) : E6Vec := fourRoots j

@[expose] def rhoE6 (v : E6Vec) : E6Vec := permLattice TwistTag.E6.perm v

@[expose] def OrthRoot (γ β : E6Vec) : Prop :=
  γ ≠ β ∧ γ ≠ -β ∧ γ + β ∉ rootFinset TwistTag.E6.tag ∧ γ + -β ∉ rootFinset TwistTag.E6.tag

instance (γ β : E6Vec) : Decidable (OrthRoot γ β) := by unfold OrthRoot; infer_instance

@[expose] def PairGood (γ : E6Vec) : Prop :=
  ∃ j k : Fin 4, j ≠ k ∧ OrthRoot γ (fourRootsE j) ∧ OrthRoot γ (fourRootsE k) ∧
    OrthRoot (rhoE6 γ) (fourRootsE j) ∧ OrthRoot (rhoE6 γ) (fourRootsE k)

instance (γ : E6Vec) : Decidable (PairGood γ) := by
  unfold PairGood
  exact Fintype.decidableExistsFintype

@[expose] def badRoots : Finset E6Vec := {
    ![0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, -1, 0, -1, 0, 0],
    ![0, 1, 0, 1, 0, 0],
    ![0, 0, -1, -1, -1, 0],
    ![0, 0, 1, 1, 1, 0],
    ![0, -1, -1, -1, -1, 0],
    ![0, 1, 1, 1, 1, 0],
    ![-1, 0, -1, -1, -1, -1],
    ![1, 0, 1, 1, 1, 1],
    ![-1, -1, -1, -1, -1, -1],
    ![1, 1, 1, 1, 1, 1],
    ![-1, -1, -2, -3, -2, -1],
    ![1, 1, 2, 3, 2, 1],
    ![-1, -2, -2, -3, -2, -1],
    ![1, 2, 2, 3, 2, 1] }

theorem pairGood_of_not_mem_badRoots :
    ∀ γ ∈ rootFinset TwistTag.E6.tag, γ ∉ badRoots → PairGood γ := by
  decide +kernel

theorem not_pairGood_of_mem_badRoots : ∀ γ ∈ badRoots, γ ∈ rootFinset TwistTag.E6.tag ∧
    ¬ PairGood γ := by
  decide +kernel

@[expose] def badDecomp : List (E6Vec × E6Vec × E6Vec) := [
    (![0, 0, 0, -1, 0, 0], ![-1, -1, -1, -2, -1, 0], ![1, 1, 1, 1, 1, 0]),
    (![0, 0, 0, 1, 0, 0], ![-1, -1, -1, -1, -1, 0], ![1, 1, 1, 2, 1, 0]),
    (![0, -1, 0, -1, 0, 0], ![-1, -1, -1, -2, -1, 0], ![1, 0, 1, 1, 1, 0]),
    (![0, 1, 0, 1, 0, 0], ![-1, 0, -1, -1, -1, 0], ![1, 1, 1, 2, 1, 0]),
    (![0, 0, -1, -1, -1, 0], ![-1, -1, -2, -2, -1, 0], ![1, 1, 1, 1, 0, 0]),
    (![0, 0, 1, 1, 1, 0], ![-1, -1, -1, -1, 0, 0], ![1, 1, 2, 2, 1, 0]),
    (![0, -1, -1, -1, -1, 0], ![-1, -1, -2, -2, -1, 0], ![1, 0, 1, 1, 0, 0]),
    (![0, 1, 1, 1, 1, 0], ![-1, 0, -1, -1, 0, 0], ![1, 1, 2, 2, 1, 0]),
    (![-1, 0, -1, -1, -1, -1], ![-1, -1, -2, -2, -1, -1], ![0, 1, 1, 1, 0, 0]),
    (![1, 0, 1, 1, 1, 1], ![0, -1, -1, -1, 0, 0], ![1, 1, 2, 2, 1, 1]),
    (![-1, -1, -1, -1, -1, -1], ![-1, -1, -2, -2, -1, -1], ![0, 0, 1, 1, 0, 0]),
    (![1, 1, 1, 1, 1, 1], ![0, 0, -1, -1, 0, 0], ![1, 1, 2, 2, 1, 1]),
    (![-1, -1, -2, -3, -2, -1], ![-1, -1, -2, -2, -1, -1], ![0, 0, 0, -1, -1, 0]),
    (![1, 1, 2, 3, 2, 1], ![0, 0, 0, 1, 1, 0], ![1, 1, 2, 2, 1, 1]),
    (![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -2, -1, -1], ![0, -1, 0, -1, -1, 0]),
    (![1, 2, 2, 3, 2, 1], ![0, 1, 0, 1, 1, 0], ![1, 1, 2, 2, 1, 1]) ]

theorem badDecomp_ok : ∀ t ∈ badDecomp, t.2.1 ∈ rootFinset TwistTag.E6.tag ∧
    t.2.2 ∈ rootFinset TwistTag.E6.tag ∧ t.2.1 + t.2.2 = t.1 ∧
    rhoE6 t.2.1 + rhoE6 t.2.2 = t.1 ∧ t.2.1 ≠ rhoE6 t.2.1 ∧ t.2.2 ≠ rhoE6 t.2.2 ∧
    PairGood t.2.1 ∧ PairGood t.2.2 ∧
    t.2.1 + rhoE6 t.2.2 ∉ rootFinset TwistTag.E6.tag ∧
    rhoE6 t.2.1 + t.2.2 ∉ rootFinset TwistTag.E6.tag := by
  decide +kernel

theorem badDecomp_covers : ∀ γ ∈ badRoots, ∃ t ∈ badDecomp, t.1 = γ := by
  decide +kernel

theorem fourRootsE_mem : ∀ j : Fin 4, fourRootsE j ∈ rootFinset TwistTag.E6.tag := by
  decide +kernel

theorem isRoot_fourRootsE (j : Fin 4) : IsRoot TwistTag.E6.tag (fourRootsE j) :=
  mem_rootFinset.1 (fourRootsE_mem j)

theorem rhoE6_of_mem_badRoots : ∀ γ ∈ badRoots, rhoE6 γ = γ := by
  decide +kernel

@[expose] def NoSum (x y : E6Vec) : Prop :=
  x ≠ y ∧ x ≠ -y ∧ x + y ∉ rootFinset TwistTag.E6.tag

instance (x y : E6Vec) : Decidable (NoSum x y) := by unfold NoSum; infer_instance

theorem badDecomp_comm_ok : ∀ t ∈ badDecomp,
    NoSum t.2.1 (rhoE6 t.2.1) ∧ NoSum t.2.2 (rhoE6 t.2.2) ∧ NoSum (rhoE6 t.2.1) t.2.2 ∧
    NoSum t.2.1 (rhoE6 t.2.2) ∧ NoSum t.1 t.2.1 ∧ NoSum t.1 t.2.2 ∧
    t.2.1 ≠ t.2.2 ∧ t.2.1 ≠ -t.2.2 ∧ rhoE6 t.1 = t.1 := by
  decide +kernel

theorem commute_rootSubgroup_of_orth {γ β : E6Vec} (hγ : IsRoot Tag.E6 γ)
    (hβ : IsRoot Tag.E6 β) (h : OrthRoot γ β) (F : Type) [Field F] :
    (∀ x ∈ rootSubgroup Tag.E6 F γ, ∀ y ∈ rootSubgroup Tag.E6 F β, Commute x y) ∧
      ∀ x ∈ rootSubgroup Tag.E6 F γ, ∀ y ∈ rootSubgroup Tag.E6 F (-β), Commute x y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨commute_rootSubgroup hγ hβ h1 h2 (fun hr => h3 (mem_rootFinset.2 hr)) F,
    commute_rootSubgroup hγ (IsRoot.neg hβ) h2 (fun e => h1 (e.trans (neg_neg β)))
      (fun hr => h4 (mem_rootFinset.2 hr)) F⟩

end CFSG.HardMathSupport.Lang.AlphaThree
