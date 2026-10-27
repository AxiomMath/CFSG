module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBig

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

namespace MuTab

inductive MuKind
  | z2 | s3 | e4 | s4 | wyl | big10 | large
  deriving DecidableEq

@[expose] def muKind (π : Bool) (t : StatedLieTag) (k : ℕ) : MuKind :=
  if t = .PSL ∧ k = 3 then (if π then .s3 else .z2)
  else if t = .PSL ∧ k = 4 then (if π then .s4 else .e4)
  else if t = .PSL ∧ k = 5 then (if π then .big10 else .e4)
  else if t = .PSU ∧ k = 3 then (if π then .z2 else .s3)
  else if t = .PSU ∧ k = 4 then (if π then .e4 else .s4)
  else if t = .PSU ∧ k = 5 then (if π then .e4 else .big10)
  else if t = .PSp ∧ k = 2 then .e4
  else if t = .POmegaOdd ∧ k = 3 then .s4
  else if t = .POmegaPlus ∧ k = 4 then .wyl
  else if t = .POmegaMinus ∧ k = 4 then .s4
  else if t = .G2 ∧ k = 0 then .s3
  else if t = .trialityD4 ∧ k = 0 then .s3
  else .large

section Shapes

variable {X : Type} [Group X] (Φ : Set (Subgroup X))

@[expose] def ShapeZ2 : Prop := ∀ K ∈ Φ, omegaStarNbr Φ K = ∅

@[expose] def ShapeS3 : Prop :=
  Disconnected.DEdgeless Φ ∧ ∃ K ∈ Φ, (omegaStarNbr Φ K).Nonempty

@[expose] def ShapeE4 : Prop :=
  (∀ K ∈ Φ, omegaStarNbr Φ K ⊆ omegaNbr Φ K) ∧
    (∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, ∀ L ∈ omegaNbr Φ K, L ∈ omegaNbr Φ J → False) ∧
    ∃ K ∈ Φ, (omegaNbr Φ K).Nonempty

@[expose] def ShapeS4 : Prop :=
  (∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, ∀ L ∈ omegaNbr Φ K, J = L) ∧
    (∃ K ∈ Φ, (omegaNbr Φ K).Nonempty) ∧ ∃ K ∈ Φ, dComp Φ K ≠ dstarComp Φ K

@[expose] def ShapeWyl : Prop :=
  (∀ K ∈ Φ, (omegaNbr Φ K).ncard ≤ 3) ∧
    (∃ K : Fin 4 → Subgroup X, (∀ i, K i ∈ Φ) ∧ Function.Injective K ∧
      ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a) ∧
    ∃ K ∈ Φ, dComp Φ K ≠ dstarComp Φ K

@[expose] def ShapeBig10 : Prop :=
  ∃ (K U : Fin 10 → Subgroup X) (Q : Subgroup X), Function.Injective K ∧ IsPGroup 2 ↥Q ∧
    ∀ i, K i ∈ Φ ∧ U i ∈ USet Φ ∧ U i ≤ K i ∧ U i ≤ Q

@[expose] def ShapeTriple : Prop :=
  ∃ K : Fin 3 → Subgroup X, (∀ i, K i ∈ Φ) ∧ Function.Injective K ∧
    ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a

@[expose] def KindShape : MuKind → Prop
  | .z2 => ShapeZ2 Φ
  | .s3 => ShapeS3 Φ
  | .e4 => ShapeE4 Φ
  | .s4 => ShapeS4 Φ
  | .wyl => ShapeWyl Φ
  | .big10 => ShapeBig10 Φ
  | .large => ShapeTriple Φ

end Shapes

@[expose] def NotSmall {X : Type} [Group X] (Φ : Set (Subgroup X)) (W : Subgroup X) : Prop :=
  ¬ MuIsoZ2 Φ W ∧ ¬ MuIsoS3 Φ W ∧ ¬ MuIsoE4 Φ W ∧ ¬ MuIsoS4 Φ W

@[expose] def MuVal {X : Type} [Group X] (Φ : Set (Subgroup X)) (W : Subgroup X) : MuKind → Prop
  | .z2 => MuIsoZ2 Φ W
  | .s3 => MuIsoS3 Φ W
  | .e4 => MuIsoE4 Φ W
  | .s4 => MuIsoS4 Φ W
  | .wyl => MuIsoWylD4 Φ W
  | .big10 => NotSmall Φ W
  | .large => NotSmall Φ W

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem muVal_of_shape (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) (hne : Ω.Nonempty) (κ : MuKind)
    (h : KindShape Ω κ) : MuVal Ω W κ := by
  cases κ with
  | z2 => exact muIsoZ2_of_shape hP hW hne h
  | s3 => exact muIsoS3_of_shape hP hW h.1 h.2
  | e4 => exact muIsoE4_of_shape hP hW h.1 h.2.1 h.2.2
  | s4 => exact muIsoS4_of_shape hP hW h.1 h.2.1 h.2.2
  | wyl =>
    obtain ⟨hle, ⟨K, hK, hinj, hcomm⟩, hcomp⟩ := h
    exact muIsoWylD4_of_shape hP hW hle K hK hinj hcomm hcomp
  | big10 =>
    obtain ⟨K, U, Q, hinj, hQ, h⟩ := h
    exact not_small_of_big10 hP hW K U hinj (fun i => (h i).1) (fun i => (h i).2.1)
      (fun i => (h i).2.2.1) Q hQ (fun i => (h i).2.2.2)
  | large =>
    obtain ⟨K, hK, hinj, hcomm⟩ := h
    exact not_small_of_triple hP hW K hK hinj hcomm

end MuTab

end CFSG.ClassicalInvolution.Asc77
