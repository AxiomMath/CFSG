module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

structure Cfg2 (S : Type) [Group S] (E F : Subgroup S) (z : S) : Prop where
  hEn : E.Normal
  hEa : IsElemAbelian 2 E
  hE8 : Nat.card E = 8
  hFa : IsElemAbelian 2 F
  hF4 : Nat.card F = 4
  hzE : z ∈ E
  hz1 : z ≠ 1
  hzF : ∀ f ∈ F, f * z = z * f
  hFK : ∀ f ∈ F, (∀ e ∈ E, f * e = e * f) → f = 1
  hCE : ∀ e ∈ E, (∀ f ∈ F, f * e = e * f) → e = 1 ∨ e = z
  hCK : ∀ k : S, (∀ e ∈ E, k * e = e * k) → (∀ f ∈ F, k * f = f * k) → k = 1 ∨ k = z

end CFSG.EvenSporadicStandard.Fin76b
