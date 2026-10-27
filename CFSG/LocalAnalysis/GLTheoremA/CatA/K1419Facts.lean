module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

abbrev PQ (Q : Type) [Group Q] : Type := Q ⧸ GLAPPrimeCore 3 Q

@[expose] def I1419Rel {Q : Type} [Group Q] (β : MulAut Q) : PQ Q → PQ Q → Prop :=
  fun q q' => ∃ l l' : Q, (QuotientGroup.mk l : PQ Q) = q ∧ (QuotientGroup.mk l' : PQ Q) = q' ∧ β l = l'

@[expose] def I1419Inn {Q : Type} [Group Q] (β : MulAut Q) : Prop :=
  GLAMarking (PQ Q) fun _ _ _ I _ θ => ∀ k : ℤ, ∃ φ ∈ I, GLAInduces θ (I1419Rel (β ^ k)) φ

@[expose] def I1419Nontriv {Q : Type} [Group Q] (β : MulAut Q) : Prop :=
  ∃ l : Q, (QuotientGroup.mk (β l) : PQ Q) ≠ QuotientGroup.mk l

@[expose] def I1419ClassLie : TauCeti.LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ => True
  | _ => False

@[expose] def I1419Classical2 : TauCeti.CFSGIndex → Prop :=
  onLie fun d => d.characteristic = 2 ∧ I1419ClassLie d

@[expose] def I1419SporIndex : TauCeti.CFSGIndex → Prop
  | .sporadic _ => True
  | _ => False

@[expose] def I1419UpFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (β : MulAut Q) (J : Subgroup Q),
    CFSG.Open.IsQuasisimple (PQ Q) → IsCatalogGroup (PQ Q ⧸ Subgroup.center (PQ Q)) →
      β ^ 3 = 1 → I1419Nontriv β →
      GLAPComponent 3 (fixSubgroup β) J → catalogIs (PSimple 3 J) l3u3Index →
      IsChevSimple 2 (PQ Q ⧸ Subgroup.center (PQ Q))

@[expose] def I1419UpAltFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (β : MulAut Q) (J : Subgroup Q),
    CFSG.Open.IsQuasisimple (PQ Q) → catalogIs (PQ Q ⧸ Subgroup.center (PQ Q)) isAltIndex →
      ¬ IsChevSimple 2 (PQ Q ⧸ Subgroup.center (PQ Q)) →
      β ^ 3 = 1 → I1419Nontriv β →
      GLAPComponent 3 (fixSubgroup β) J → catalogIs (PSimple 3 J) l3u3Index → False

@[expose] def I1419UpSporFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (β : MulAut Q) (J : Subgroup Q),
    CFSG.Open.IsQuasisimple (PQ Q) → catalogIs (PQ Q ⧸ Subgroup.center (PQ Q)) I1419SporIndex →
      ¬ IsChevSimple 2 (PQ Q ⧸ Subgroup.center (PQ Q)) →
      β ^ 3 = 1 → I1419Nontriv β →
      GLAPComponent 3 (fixSubgroup β) J → catalogIs (PSimple 3 J) l3u3Index → False

@[expose] def I1419UpLieOddFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (β : MulAut Q) (J : Subgroup Q),
    CFSG.Open.IsQuasisimple (PQ Q) →
      catalogIs (PQ Q ⧸ Subgroup.center (PQ Q)) (onLie fun d => d.characteristic ≠ 2) →
      ¬ IsChevSimple 2 (PQ Q ⧸ Subgroup.center (PQ Q)) →
      β ^ 3 = 1 → I1419Nontriv β →
      GLAPComponent 3 (fixSubgroup β) J → catalogIs (PSimple 3 J) l3u3Index → False

@[expose] def I1419ClassFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (β : MulAut Q) (J : Subgroup Q),
    CFSG.Open.IsQuasisimple (PQ Q) → β ^ 3 = 1 → I1419Nontriv β → I1419Inn β →
      GLAPComponent 3 (fixSubgroup β) J → catalogIs (PSimple 3 J) l3u3Index →
      Subgroup.center (PQuot 3 J) = ⊥ →
      catalogIs (PQ Q ⧸ Subgroup.center (PQ Q)) I1419Classical2 → False

@[expose] def I1419ExcFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (β : MulAut Q) (J : Subgroup Q),
    CFSG.Open.IsQuasisimple (PQ Q) → β ^ 3 = 1 → I1419Nontriv β → I1419Inn β →
      GLAPComponent 3 (fixSubgroup β) J → catalogIs (PSimple 3 J) l3u3Index →
      Subgroup.center (PQuot 3 J) = ⊥ →
      IsChevSimple 2 (PQ Q ⧸ Subgroup.center (PQ Q)) →
      ¬ catalogIs (PQ Q ⧸ Subgroup.center (PQ Q)) I1419Classical2 → False

end CFSG.LocalAnalysis.GLTheoremA.K1419
