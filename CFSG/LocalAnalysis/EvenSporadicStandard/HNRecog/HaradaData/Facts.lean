module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarHCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

structure HaradaFacts (H : Type) [Group H] (E : Subgroup H) (a z b z₁ : H)
    (S T T' W0 : Subgroup H) (ι : Elem2 6 →* H) : Prop extends TwoHSFacts H a z b z₁ where
  harCore : TwoHS.HarCoreData a z S E T T' W0
  isPGroup_S : IsPGroup 2 S
  card_S : Nat.card S = 2 ^ 11
  injective_ι : Function.Injective ι
  ι_tv : ι (Multiplicative.ofAdd tv) = a
  coords_z : ∃ v : V6, ι (Multiplicative.ofAdd v) = z ∧ lam v = 0 ∧ qm v = 0
  coords_b : ∃ v : V6, ι (Multiplicative.ofAdd v) = b ∧ lam v = 1 ∧ qm v = 1
  coords_z₁ : ∃ v : V6, ι (Multiplicative.ofAdd v) = z₁ ∧ lam v = 1 ∧ qm v = 0
  mem_E_iff : ∀ v : V6, ι (Multiplicative.ofAdd v) ∈ E ↔ lam v = 0
  conj_E64 : ∀ B : Subgroup H, Nat.card B = 64 → CFSG.Open.IsElemAbelian 2 B →
    ∃ h : H, B = ι.range.map (MulAut.conj h).toMonoidHom
  centralizer_le : centralizer (ι.range : Set H) ≤ ι.range
  card_normalizer : Nat.card (normalizer (ι.range : Set H)) = 46080
  fuse : ∀ v w : V6, v ≠ 0 → v ≠ tv → w ≠ 0 → w ≠ tv → lam v = lam w → qm v = qm w →
    ∃ n ∈ normalizer (ι.range : Set H),
      n * ι (Multiplicative.ofAdd v) * n⁻¹ = ι (Multiplicative.ofAdd w)

end CFSG.EvenSporadicStandard.HNRecog
