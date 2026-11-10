module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def ActsTransOutside (T V W X : Subgroup G) : Prop :=
  T ≤ normalizer (V : Set G) ∧ T ≤ normalizer (W : Set G) ∧
    ∀ u ∈ V, u ∉ X → ∀ v ∈ V, v ∉ X → ∃ k ∈ T, v⁻¹ * (k * u * k⁻¹) ∈ W

@[expose] def QuotModIso (X W N Q Z : Subgroup G) : Prop :=
  SecProp Q Z (fun Y' _ _ π' => SecProp W N (fun Y _ _ π =>
    ∃ φ : Y ≃* Y', ∀ n ∈ X, ∀ w w' : ↥W, (w' : G) = n * w * n⁻¹ →
      ∀ q q' : ↥Q, (q' : G) = n * q * n⁻¹ → φ (π w) = π' q → φ (π w') = π' q'))

abbrev GL3Two : Type := Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)

abbrev SL3Four : Type := Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)

@[expose] def C6 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G :=
  pCoreOf 2 (normalizer (C1 e : Set G))

@[expose] def M6 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := centIn (C6 e) (V1 e)

@[expose] def M4 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := centIn (C4 s) (V1 e)

@[expose] def V2 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := M3 s ⊓ M4 e

@[expose] def X7 (s : Setting3 G L) : Subgroup G :=
  normalizer ((s.fr.B ⊔ C3 s : Subgroup G) : Set G) ⊓ normalizer (M3 s : Set G) ⊓
    centralizerSection (s.fr.B ⊔ M3 s) (M3 s)

@[expose] def C7 (s : Setting3 G L) : Subgroup G :=
  pCoreOf 2 ⁅X7 s, normIn s.H s.fr.B⁆ ⊔ (s.fr.B ⊔ C3 s)

@[expose] def M7 (s : Setting3 G L) : Subgroup G := ⁅C7 s, normIn L s.fr.B⁆ ⊔ (s.fr.B ⊔ M3 s)

@[expose] def M5 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := M3 s ⊔ M4 e

@[expose] def P7 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := M6 e ⊔ M7 s

@[expose] def JF (s : Setting3 G L) : Subgroup G := ⁅normIn L s.fr.F, normIn L s.fr.F⁆

@[expose] def K7 (s : Setting3 G L) : Subgroup G :=
  ⨆ x ∈ normalizer (M3 s : Set G), conjSub x (JF s ⊔ M3 s)

@[expose] def IsCompPre (s : Setting3 G L) (L1 : Subgroup G) : Prop :=
  M3 s ≤ L1 ∧ L1 ≤ K7 s ∧ L1 ⊔ conjSub s.t L1 = K7 s ∧ L1 ⊓ conjSub s.t L1 = M3 s ∧
    ⁅L1, conjSub s.t L1⁆ ≤ M3 s ∧
    SecProp L1 (M3 s) (fun Y _ _ _ => Nonempty (Y ≃* GL3Two))

end CFSG.OddStandard.HigherRank.YamadaG23
