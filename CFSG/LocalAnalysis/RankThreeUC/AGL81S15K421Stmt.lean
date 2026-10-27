module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def K421Concl (L : Type) [Group L] [Finite L] : Prop :=
  ∀ (R : Sylow 3 L) (A : Subgroup L), A = jElementary 3 (R : Subgroup L) →
    (CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27) ∧
    (∀ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E →
      ∃ g : L, E.map (MulAut.conj g).toMonoidHom ≤ A) ∧
    ∃ A₁ A₂ A₃ B₁ B₂ B₃ : Subgroup L,
      HasThreeWClasses (Subgroup.normalizer (A : Set L)) A 3 A₁ A₂ A₃ ∧
      HasThreeWClasses (Subgroup.normalizer (A : Set L)) A 9 B₁ B₂ B₃ ∧
      (wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₁ = 2 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₂ = 2 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₃ = 0) ∧
      (wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₁ = 1 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₂ = 1 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₃ = 2) ∧
      (wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₁ = 0 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₂ = 3 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₃ = 1)

@[expose] def K421Good (L : Type) [Group L] [Finite L] (A : Subgroup L) : Prop :=
  (CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27) ∧
    (∀ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E →
      ∃ g : L, E.map (MulAut.conj g).toMonoidHom ≤ A) ∧
    ∃ A₁ A₂ A₃ B₁ B₂ B₃ : Subgroup L,
      HasThreeWClasses (Subgroup.normalizer (A : Set L)) A 3 A₁ A₂ A₃ ∧
      HasThreeWClasses (Subgroup.normalizer (A : Set L)) A 9 B₁ B₂ B₃ ∧
      (wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₁ = 2 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₂ = 2 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₃ = 0) ∧
      (wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₁ = 1 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₂ = 1 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₃ = 2) ∧
      (wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₁ = 0 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₂ = 3 ∧
        wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₃ = 1)

@[expose] def K421Orb (L : Type) [Group L] [Finite L] (A : Subgroup L) : Prop :=
  ∃ A₁ A₂ A₃ B₁ B₂ B₃ : Subgroup L,
    HasThreeWClasses (Subgroup.normalizer (A : Set L)) A 3 A₁ A₂ A₃ ∧
    HasThreeWClasses (Subgroup.normalizer (A : Set L)) A 9 B₁ B₂ B₃ ∧
    (wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₁ = 2 ∧
      wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₂ = 2 ∧
      wClassCount (Subgroup.normalizer (A : Set L)) B₁ A₃ = 0) ∧
    (wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₁ = 1 ∧
      wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₂ = 1 ∧
      wClassCount (Subgroup.normalizer (A : Set L)) B₂ A₃ = 2) ∧
    (wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₁ = 0 ∧
      wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₂ = 3 ∧
      wClassCount (Subgroup.normalizer (A : Set L)) B₃ A₃ = 1)

theorem k421Good_iff_orb (L : Type) [Group L] [Finite L] (A : Subgroup L) :
    K421Good L A ↔ (CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27) ∧
      (∀ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E →
        ∃ g : L, E.map (MulAut.conj g).toMonoidHom ≤ A) ∧ K421Orb L A :=
  Iff.rfl

theorem k421Concl_iff_good (L : Type) [Group L] [Finite L] :
    K421Concl L ↔ ∀ (R : Sylow 3 L) (A : Subgroup L), A = jElementary 3 (R : Subgroup L) →
      K421Good L A :=
  Iff.rfl

@[expose] def K421TableConcl (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex) :
    Prop :=
  ∀ (R : Sylow 3 L) (A H : Subgroup L), A = jElementary 3 (R : Subgroup L) → H ≤ A →
    Nat.card H = 3 →
    ((wConjClass (Subgroup.normalizer (A : Set L)) H).ncard = 3 →
      Table421 ↥(Subgroup.centralizer (H : Set L)) d.1 1) ∧
    ((wConjClass (Subgroup.normalizer (A : Set L)) H).ncard = 6 →
      Table421 ↥(Subgroup.centralizer (H : Set L)) d.1 2) ∧
    ((wConjClass (Subgroup.normalizer (A : Set L)) H).ncard = 4 →
      Table421 ↥(Subgroup.centralizer (H : Set L)) d.1 3)

@[expose] def K421At (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), P d.1 →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → K421Concl L

@[expose] def K421TableAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), P d.1 →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → K421TableConcl L d

theorem K421_iff_at : K421 ↔ K421At Is421Index := by
  constructor
  · intro h L _ _ d hd he
    exact h L ⟨d, hd, he⟩
  · intro h L _ _ hL
    obtain ⟨d, hd, he⟩ := hL
    exact h L d hd he

theorem K421Table_iff_at : K421Table ↔ K421TableAt Is421Index := by
  constructor
  · intro h L _ _ d hd he
    exact h L d hd he
  · intro h L _ _ d hd he
    exact h L d hd he

@[expose] def Is421IndexLin : TauCeti.LieTypeIndex → Prop
  | .A 5 Q => Q.card = 2
  | .A 6 Q => Q.card = 2
  | _ => False

@[expose] def Is421IndexSp : TauCeti.LieTypeIndex → Prop
  | .B 3 Q => Q.p = 2
  | _ => False

@[expose] def Is421IndexOm : TauCeti.LieTypeIndex → Prop
  | .twistedD 4 Q => Q.p = 2
  | _ => False

theorem is421Index_iff (i : TauCeti.LieTypeIndex) :
    Is421Index i ↔ Is421IndexLin i ∨ Is421IndexSp i ∨ Is421IndexOm i := by
  cases i with
  | A n Q =>
    match n with
    | 5 => simp [Is421Index, Is421IndexLin, Is421IndexSp, Is421IndexOm]
    | 6 => simp [Is421Index, Is421IndexLin, Is421IndexSp, Is421IndexOm]
    | 0 | 1 | 2 | 3 | 4 | n + 7 => simp [Is421Index, Is421IndexLin, Is421IndexSp, Is421IndexOm]
  | B n Q =>
    match n with
    | 3 => simp [Is421Index, Is421IndexLin, Is421IndexSp, Is421IndexOm]
    | 0 | 1 | 2 | n + 4 => simp [Is421Index, Is421IndexLin, Is421IndexSp, Is421IndexOm]
  | twistedD n Q =>
    match n with
    | 4 => simp [Is421Index, Is421IndexLin, Is421IndexSp, Is421IndexOm]
    | 0 | 1 | 2 | 3 | n + 5 => simp [Is421Index, Is421IndexLin, Is421IndexSp, Is421IndexOm]
  | _ => simp [Is421Index, Is421IndexLin, Is421IndexSp, Is421IndexOm]

@[expose] def K421Lin : Prop := K421At Is421IndexLin

@[expose] def K421Sp : Prop := K421At Is421IndexSp

@[expose] def K421Om : Prop := K421At Is421IndexOm

@[expose] def K421TableLin : Prop := K421TableAt Is421IndexLin

@[expose] def K421TableSp : Prop := K421TableAt Is421IndexSp

@[expose] def K421TableOm : Prop := K421TableAt Is421IndexOm

theorem K421_of_parts (hL : K421Lin) (hS : K421Sp) (hO : K421Om) : K421 := by
  rw [K421_iff_at]
  intro L _ _ d hd he
  rcases (is421Index_iff _).mp hd with h | h | h
  · exact hL L d h he
  · exact hS L d h he
  · exact hO L d h he

theorem K421Table_of_parts (hL : K421TableLin) (hS : K421TableSp) (hO : K421TableOm) :
    K421Table := by
  rw [K421Table_iff_at]
  intro L _ _ d hd he
  rcases (is421Index_iff _).mp hd with h | h | h
  · exact hL L d h he
  · exact hS L d h he
  · exact hO L d h he

end CFSG.LocalAnalysis.RankThreeUC.S15
