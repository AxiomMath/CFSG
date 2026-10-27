module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S265

@[expose] def IvLieRow : Prop := ∀ {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω}, QSCfg 3 S B T x D K → catalogIs (PSimple 3 K) S9.isSp6two →
    Nat.card B = 9 * Nat.card D →
    catalogIs (PSimple 3 S) S8.L84.isSp82 ∨ catalogIs (PSimple 3 S) S9.isF4two

@[expose] def IvCoreAt (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G], catalogIs G Q →
  ∀ {Bb : Subgroup G}, IsElemAbelian 3 Bb → Nat.card Bb = 27 →
  ∀ {d : G}, d ∈ Bb → d ≠ 1 →
  ∀ {K : Subgroup G}, GLAPComponent 3 (Subgroup.centralizer ({d} : Set G)) K →
    catalogIs (PSimple 3 K) S9.isSp6two →
    (∀ e ∈ Bb, e ∉ Subgroup.zpowers d →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({e} : Set G)) = ⊥) →
    (∀ W : Subgroup G, IsPGroup 2 W → W ≤ Subgroup.centralizer ({d} : Set G) →
      Bb ≤ Subgroup.normalizer (W : Set G) → W = ⊥) →
    ∀ W : Subgroup G, IsPGroup 2 W → Bb ≤ Subgroup.normalizer (W : Set G) → W = ⊥

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
