module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup
open scoped commutatorElement

structure ParrottData (C X : Type) [Group C] [Group X] (Q Nt K₁ : Subgroup C) : Prop where
  normal_Q : Q.Normal
  normal_Nt : Nt.Normal
  card_Q : Nat.card Q = 2 ^ 13
  extraspecial_Q : CFSG.IsExtraspecial 2 ↥Q
  centralizer_Q : Subgroup.centralizer (Q : Set C) ≤ Q
  index_K : K₁.index = 2
  Q_le : Q ≤ Nt
  Nt_le : Nt ≤ K₁
  card_Nt : Nat.card Nt = 3 * Nat.card Q
  hom : ∃ π : ↥K₁ →* X, Function.Surjective π ∧ π.ker = Nt.subgroupOf K₁
  noncentral : ∀ h : C, h ∉ K₁ → ∃ n ∈ Nt, ⁅h, n⁆ ∉ Q

end CFSG.EvenSporadicStandard.TwoFi22.DS81
