module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def weakExcIndex (i : TauCeti.CFSGIndex) : Prop :=
  excIndex i ∨
    match i with
    | .lie j =>
      match j.1 with
      | .A 1 q => q.p = 2 ∧ Odd q.exponent ∧ 1 < q.exponent
      | _ => False
    | _ => False

@[expose] def I2013At : Prop :=
  ∀ (Q : Type) [Group Q] (N m : ℕ) (e : Q ≃* ↥(alternatingGroup (Fin N))) (J : Subgroup Q),
    5 ≤ m → m ≤ N → IsRootAlt e J m →
    ∀ T : Subgroup Q, IsPGroup 2 T → J ≤ Subgroup.normalizer (T : Set Q) →
      J ≤ Subgroup.centralizer (T : Set Q)

@[expose] def I1415At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K J : Subgroup G) (y : G) (m : ℕ), CFSG.Open.IsKGroup ↥X →
    GLAPComponent p X K → y ∈ Subgroup.normalizer (K : Set G) → y ^ p = 1 →
    ¬ CentMod p K y → GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J →
    9 < m → IsAltPType p J m → ∃ k : ℕ, 0 < k ∧ IsAltPType p K (m + k * p)

@[expose] def I112StarAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X B' L : Subgroup G), CFSG.Open.IsKGroup ↥X → B' ≤ X →
    IsElemAbelian p B' → GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B' → GLAPComponent p X L →
    ¬ B' ≤ Subgroup.normalizer (L : Set G) →
    p = 3 ∧ ∀ b ∈ B', b ∉ Subgroup.normalizer (L : Set G) → ∀ J : Subgroup G,
      GLAPComponent p (closureIn L B' ⊓ Subgroup.centralizer ({b} : Set G)) J →
        catalogIs (PQuot p J) weakExcIndex

@[expose] def AltNotWeakExcAt : Prop :=
  ∀ m : ℕ, 8 ≤ m → ¬ catalogIs ↥(alternatingGroup (Fin m)) weakExcIndex

end CFSG.LocalAnalysis.GLTheoremA
