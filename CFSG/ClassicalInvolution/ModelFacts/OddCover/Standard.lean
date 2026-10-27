module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Lifting
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4Cover
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeLift
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

universe u v w

section SL3

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem noCover_odd_sl3 (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    NoCover.{u} Odd (Matrix.SpecialLinearGroup (Fin 3) K) :=
  NoCover.of_mulEquiv (specialLinearGroupEquivStatedSL 3 K).symm
    (statedSL_three_noCover_odd hK (by rwa [hK]))

theorem lifting_lemma_sl3 (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {X : Type v} [Group X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) {W : Type w} [Group W] [Group.IsPerfect W]
    {Z : Subgroup W} [Z.Normal] (hZc : Z ≤ Subgroup.center W) (hZ : Odd (Nat.card Z))
    (θbar : X →* W ⧸ Z) (hθbar : Function.Surjective θbar) (hker : θbar.ker ≤ Subgroup.center X) :
    ∃ θ : X →* W, Function.Surjective θ ∧ θ.ker ≤ Subgroup.center X ∧
      ∀ x, (θ x : W ⧸ Z) = θbar x := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact lifting_of_noCover (NoCover.of_mulEquiv e.symm (noCover_odd_sl3 hK h5)) hZc hZ θbar
    hθbar hker

end SL3

section SU3

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem noCover_odd_su3 (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (h5 : 5 ≤ p ^ f) :
    NoCover.{u} Odd (SU (unitaryInvolution K p f) 3) :=
  NoCover.of_mulEquiv (equivStatedSU hK 3).symm (statedSU_three_noCover_odd hp2 hK h5)

theorem lifting_lemma_su3 (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (h5 : 5 ≤ p ^ f)
    {X : Type v} [Group X] (e : X ≃* SU (unitaryInvolution K p f) 3) {W : Type w} [Group W]
    [Group.IsPerfect W] {Z : Subgroup W} [Z.Normal] (hZc : Z ≤ Subgroup.center W)
    (hZ : Odd (Nat.card Z)) (θbar : X →* W ⧸ Z) (hθbar : Function.Surjective θbar)
    (hker : θbar.ker ≤ Subgroup.center X) :
    ∃ θ : X →* W, Function.Surjective θ ∧ θ.ker ≤ Subgroup.center X ∧
      ∀ x, (θ x : W ⧸ Z) = θbar x := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Group.IsPerfect (SU (unitaryInvolution K p f) 3) :=
    CFSG.LieType.Steinberg.isPerfect_SU_three hK hp2
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact lifting_of_noCover (NoCover.of_mulEquiv e.symm (noCover_odd_su3 hp2 hK h5)) hZc hZ θbar
    hθbar hker

end SU3

section Sp4

variable {K : Type} [Field K] {p f : ℕ} [Fact p.Prime]

theorem noCover_odd_sp4 (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    NoCover.{u} Odd (StatedSp 2 K) :=
  sp4_noCover_odd hp2 hK (by rwa [hK])

theorem isPerfect_sp4 (h5 : 5 ≤ Nat.card K) : Group.IsPerfect (StatedSp 2 K) :=
  (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num)
    (Or.inl (Or.inr (by omega)))).1

theorem lifting_lemma_sp4 (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {X : Type v} [Group X] (e : X ≃* StatedSp 2 K) {W : Type w} [Group W] [Group.IsPerfect W]
    {Z : Subgroup W} [Z.Normal] (hZc : Z ≤ Subgroup.center W) (hZ : Odd (Nat.card Z))
    (θbar : X →* W ⧸ Z) (hθbar : Function.Surjective θbar) (hker : θbar.ker ≤ Subgroup.center X) :
    ∃ θ : X →* W, Function.Surjective θ ∧ θ.ker ≤ Subgroup.center X ∧
      ∀ x, (θ x : W ⧸ Z) = θbar x := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Group.IsPerfect (StatedSp 2 K) := isPerfect_sp4 (by rwa [hK])
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact lifting_of_noCover (NoCover.of_mulEquiv e.symm (noCover_odd_sp4 hp2 hK h5)) hZc hZ θbar
    hθbar hker

end Sp4

end CFSG.ClassicalInvolution.ModelFacts.OddCover
