module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def tySp10 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B 5 q => q.card = 2 | _ => False

@[expose] def QSBResSp10 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 3 S B T x D K → catalogIs (PSimple 3 S) tySp10 →
    (catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two) →
    Nat.card B = 3 ^ 5 → ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    QSConcl 3 S B D K

@[expose] def QSBResOm10m : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 3 S B T x D K → catalogIs (PSimple 3 S) tyOm10m →
    (catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two) →
    Nat.card B = 3 ^ 5 → ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    QSConcl 3 S B D K

@[expose] def QSBResU6two : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 3 S B T x D K → catalogIs (PSimple 3 S) S9.isU6two →
    (catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two) →
    Nat.card B = 3 ^ 5 → ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    QSConcl 3 S B D K

@[expose] def QSBResTwE6 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 3 S B T x D K → catalogIs (PSimple 3 S) S9.isTE6two →
    catalogIs (PSimple 3 K) S9.isU6two →
    Nat.card B = 3 ^ 5 → ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    QSConcl 3 S B D K

@[expose] def TwE6U5Inv : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) (a : X), CFSG.Open.IsQuasisimple ↥S →
    GLAPPrimeCore 3 ↥S = ⊥ → catalogIs (PSimple 3 S) S9.isTE6two →
    a ∈ Subgroup.normalizer (S : Set X) → a ^ 3 = 1 →
    (¬ ∃ k ∈ S, k⁻¹ * a ∈ Subgroup.centralizer (S : Set X)) →
    ∀ J : Subgroup X, GLAPComponent 3 (S ⊓ Subgroup.centralizer ({a} : Set X)) J →
      catalogIs (PSimple 3 J) S9.isU5two →
      ∃ t ∈ S ⊓ Subgroup.centralizer ({a} : Set X),
        t ∈ Subgroup.centralizer (J : Set X) ∧ orderOf t = 2

@[expose] def TwE6U6Even : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 3 S B T x D K → catalogIs (PSimple 3 S) S9.isTE6two →
    catalogIs (PSimple 3 K) S9.isU6two →
    Nat.card B = 3 ^ 5 → ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    ∃ t : PSimple 3 K, orderOf t = 2 ∧
      ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (K : Set Ω), chevAut 3 K ⟨b, hb⟩ t = t

end CFSG.LocalAnalysis.GLTheoremA.S265

end
