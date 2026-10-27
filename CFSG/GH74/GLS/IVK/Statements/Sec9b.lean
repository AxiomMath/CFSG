module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

@[expose] def IsInvolutionCentralizerOfModel (X : Type) [Group X] (t : StatedLieTag) (p' f' : ℕ) : Prop :=
  ∃ (M : Type) (_ : Group M) (z' : M), LieModel M t 0 p' f' ∧ orderOf z' = 2 ∧
    Nonempty (X ≃* ↥(oPrimeResidualOf 2 (centralizer ({z'} : Set M))))

@[expose] def Hyp94Loc (H : Type) [Group H] (Gs : Type) [Group Gs] (z : H) (t : StatedLieTag) (p' f' : ℕ) : Prop :=
  (t = .G2 ∨ t = .trialityD4) ∧ p'.Prime ∧ p' ≠ 2 ∧
    ∃ (p f : ℕ) (S : Sylow 2 H) (U : Subgroup H), p.Prime ∧ p ≠ 2 ∧ LieModel Gs .G2 0 p f ∧
      (∃ S' : Sylow 2 Gs, Nonempty (↥(S : Subgroup H) ≃* ↥(S' : Subgroup Gs))) ∧
      Subgroup.zpowers z = (Subgroup.center ↥(S : Subgroup H)).map (S : Subgroup H).subtype ∧
      Subgroup.zpowers z ≤ U ∧ U ≤ (S : Subgroup H) ∧ IsFourSubgroup U ∧
      IsInvolutionCentralizerOfModel ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) t p' f' ∧
      (∀ u ∈ U, ∀ v ∈ U, orderOf u = 2 → orderOf v = 2 → IsConj u v)

@[expose] def Hyp94 (H : Type) [Group H] (Gs : Type) [Group Gs] (z : H) (t : StatedLieTag)
    (p' f' : ℕ) : Prop :=
  IsKGroupNative H ∧ pPrimeCore 2 H = ⊥ ∧ Hyp94Loc H Gs z t p' f'

@[expose] def Concl94 (H : Type) [Group H] (z : H) (t : StatedLieTag) (p' f' : ℕ) : Prop :=
  oPrimeResidual 2 H = layer H ∧ LieModel ↥(layer H) t 0 p' f' ∧
    centralizer ({z} : Set H) ⊓ layer H = oPrimeResidualOf 2 (centralizer ({z} : Set H))

@[expose] def IVK_9_4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Gs : Type) [Group Gs] (z : H) (t : StatedLieTag) (p' f' : ℕ),
    Hyp94 H Gs z t p' f' → Concl94 H z t p' f'

end CFSG.GH74.GLS.IVK
