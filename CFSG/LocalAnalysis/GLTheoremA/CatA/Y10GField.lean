module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def InnDiagKind (S : Type) [Group S] (labK : GLALabel) (α : MulAut S) : Prop :=
  CFSG.Assembly.LargeEvenMarking S fun lab _ _ I _ θ =>
    lab = labK ∧ ∃ u ∈ I, CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) u

@[expose] def FieldKind (S : Type) [Group S] (labK : GLALabel) (α : MulAut S) : Prop :=
  CFSG.Assembly.LargeEvenMarking S fun lab _ _ I F θ =>
    lab = labK ∧ (∃ i ∈ I, ∃ f ∈ F, CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) (i * f)) ∧
      ¬ ∃ i ∈ I, CFSG.Assembly.LargeEvenInduces θ (fun s s' => s' = α s) i

@[expose] def FamLin (lab : GLALabel) : Prop :=
  lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2)

@[expose] def FamUni (lab : GLALabel) : Prop :=
  lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)

@[expose] def FamSymp (lab : GLALabel) : Prop :=
  lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .B2der

@[expose] def FamOrth (lab : GLALabel) : Prop :=
  (lab.tag = .D ∧ lab.rank ≠ 3) ∨ (lab.tag = .twD ∧ lab.rank ≠ 2 ∧ lab.rank ≠ 3)

@[expose] def FamExc (lab : GLALabel) : Prop :=
  lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6 ∨ lab.tag = .triD4 ∨
    lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der

theorem fam_cover (lab : GLALabel) :
    FamLin lab ∨ FamUni lab ∨ FamSymp lab ∨ FamOrth lab ∨ FamExc lab := by
  rcases lab with ⟨tag, rank, n⟩
  unfold FamLin FamUni FamSymp FamOrth FamExc
  cases tag <;> by_cases h3 : rank = 3 <;> by_cases h2 : rank = 2 <;> simp_all

@[expose] def ClsLin : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (labK : GLALabel), FamLin labK →
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) → α ^ p = 1 →
      InnDiagKind S labK α ∨ FieldKind S labK α

@[expose] def ClsUni : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (labK : GLALabel), FamUni labK →
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) → α ^ p = 1 →
      InnDiagKind S labK α ∨ FieldKind S labK α

@[expose] def ClsSymp : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (labK : GLALabel), FamSymp labK →
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) → α ^ p = 1 →
      InnDiagKind S labK α ∨ FieldKind S labK α

@[expose] def ClsOrth : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (labK : GLALabel), FamOrth labK →
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) → α ^ p = 1 →
      InnDiagKind S labK α ∨ FieldKind S labK α ∨ (labK.tag = .D ∧ labK.rank = 4 ∧ p = 3)

@[expose] def ClsExc : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (labK : GLALabel), FamExc labK →
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) → α ^ p = 1 →
      InnDiagKind S labK α ∨ FieldKind S labK α

@[expose] def InnDiagLin : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamLin labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → InnDiagKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n ∣ (canonLabel labJ).n

@[expose] def InnDiagUni : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamUni labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → InnDiagKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n ∣ (canonLabel labJ).n

@[expose] def InnDiagSymp : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamSymp labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → InnDiagKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n ∣ (canonLabel labJ).n

@[expose] def InnDiagOrth : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamOrth labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → InnDiagKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n ∣ (canonLabel labJ).n

@[expose] def InnDiagExc : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamExc labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → InnDiagKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n ∣ (canonLabel labJ).n

@[expose] def FldLin : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamLin labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → FieldKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
          (canonLabel labK).rank = (canonLabel labJ).rank

@[expose] def FldUni : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamUni labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → FieldKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
          (canonLabel labK).rank = (canonLabel labJ).rank

@[expose] def FldSymp : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamSymp labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → FieldKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
          (canonLabel labK).rank = (canonLabel labJ).rank

@[expose] def FldOrth : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamOrth labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → FieldKind S labK α → α ^ p = 1 →
      HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
          (canonLabel labK).rank = (canonLabel labJ).rank

@[expose] def FldExc : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    FamExc labK → p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → FieldKind S labK α → ¬(labK.tag = .triD4 ∧ p = 3) →
      α ^ p = 1 → HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
          (canonLabel labK).rank = (canonLabel labJ).rank

@[expose] def TriPiece : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p = 3 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
      (labK.tag = .triD4 ∨ (labK.tag = .D ∧ labK.rank = 4)) → α ^ p = 1 →
        HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
          FieldRel p (canonLabel labK) (canonLabel labJ)

theorem cls_of_families (hLin : ClsLin) (hUni : ClsUni) (hSymp : ClsSymp) (hOrth : ClsOrth) (hExc : ClsExc)
    (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (labK : GLALabel)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hlab : HasLabel S (fun l : GLALabel => l = labK)) (hα : α ^ p = 1) :
    InnDiagKind S labK α ∨ FieldKind S labK α ∨ (labK.tag = .D ∧ labK.rank = 4 ∧ p = 3) := by
  rcases fam_cover labK with h | h | h | h | h
  · exact (hLin S p α labK h hp hp2 hcen hlab hα).elim Or.inl (fun h' => Or.inr (Or.inl h'))
  · exact (hUni S p α labK h hp hp2 hcen hlab hα).elim Or.inl (fun h' => Or.inr (Or.inl h'))
  · exact (hSymp S p α labK h hp hp2 hcen hlab hα).elim Or.inl (fun h' => Or.inr (Or.inl h'))
  · exact hOrth S p α labK h hp hp2 hcen hlab hα
  · exact (hExc S p α labK h hp hp2 hcen hlab hα).elim Or.inl (fun h' => Or.inr (Or.inl h'))

theorem inn_of_families (hLin : InnDiagLin) (hUni : InnDiagUni) (hSymp : InnDiagSymp) (hOrth : InnDiagOrth)
    (hExc : InnDiagExc) (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S)
    (labK labJ : GLALabel) (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : InnDiagKind S labK α) (hα : α ^ p = 1) (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent p (fixSubgroup α) J) : (canonLabel labK).n ∣ (canonLabel labJ).n := by
  rcases fam_cover labK with h | h | h | h | h
  · exact hLin S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ
  · exact hUni S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ
  · exact hSymp S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ
  · exact hOrth S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ
  · exact hExc S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ

theorem fld_of_families (hLin : FldLin) (hUni : FldUni) (hSymp : FldSymp) (hOrth : FldOrth) (hExc : FldExc)
    (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hfld : FieldKind S labK α)
    (hnot : ¬(labK.tag = .triD4 ∧ p = 3)) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) (hJ : GLAPComponent p (fixSubgroup α) J) :
    (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
      (canonLabel labK).rank = (canonLabel labJ).rank := by
  rcases fam_cover labK with h | h | h | h | h
  · exact hLin S p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact hUni S p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact hSymp S p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact hOrth S p α J labK labJ h hp hp2 hcen hfld hα hlabJ hJ
  · exact hExc S p α J labK labJ h hp hp2 hcen hfld hnot hα hlabJ hJ

@[expose] def FldPiece : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → FieldKind S labK α → ¬(labK.tag = .triD4 ∧ p = 3) →
      α ^ p = 1 → HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p (fixSubgroup α) J →
        (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
          (canonLabel labK).rank = (canonLabel labJ).rank

theorem I1441FactS_of_pieces (hC : ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (labK :
    GLALabel), p.Prime → p ≠ 2 → Subgroup.center S = ⊥ → HasLabel S (fun l : GLALabel => l = labK) →
    α ^ p = 1 → InnDiagKind S labK α ∨ FieldKind S labK α ∨ (labK.tag = .D ∧ labK.rank = 4 ∧ p =
    3)) (hI : ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (α :
    MulAut S) (J : Subgroup S) (labK labJ : GLALabel), p.Prime → p ≠ 2 → Subgroup.center S = ⊥ →
    InnDiagKind S labK α → α ^ p = 1 → HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent p
    (fixSubgroup α) J → (canonLabel labK).n ∣ (canonLabel labJ).n) (hF : FldPiece) (hT : TriPiece) :
    I1441FactS := by
  intro S _ _ p α J labK labJ hp hp2 hcen hlabK hlabJ hα hJ
  rcases hC S p α labK hp hp2 hcen hlabK hα with hin | hfld | hD
  · exact Or.inl (hI S p α J labK labJ hp hp2 hcen hin hα hlabJ hJ)
  · by_cases h3 : labK.tag = .triD4 ∧ p = 3
    · exact hT S p α J labK labJ h3.2 hcen hlabK (Or.inl h3.1) hα hlabJ hJ
    · obtain ⟨h1, h2, h4⟩ := hF S p α J labK labJ hp hp2 hcen hfld h3 hα hlabJ hJ
      exact Or.inr ⟨h1, Or.inl ⟨h2, h4⟩⟩
  · exact hT S p α J labK labJ hD.2.2 hcen hlabK (Or.inr ⟨hD.1, hD.2.1⟩) hα hlabJ hJ

theorem I1441FactS_of_families (hClsLin : ClsLin) (hClsUni : ClsUni) (hClsSymp : ClsSymp)
    (hClsOrth : ClsOrth) (hClsExc : ClsExc)
    (hInnLin : InnDiagLin) (hInnUni : InnDiagUni) (hInnSymp : InnDiagSymp) (hInnOrth : InnDiagOrth)
    (hInnExc : InnDiagExc)
    (hFldLin : FldLin) (hFldUni : FldUni) (hFldSymp : FldSymp) (hFldOrth : FldOrth) (hFldExc : FldExc)
    (hTri : TriPiece) : I1441FactS :=
  I1441FactS_of_pieces
    (fun S _ _ p α labK hp hp2 hcen hlab hα =>
      cls_of_families hClsLin hClsUni hClsSymp hClsOrth hClsExc S p α labK hp hp2 hcen hlab hα)
    (fun S _ _ p α J labK labJ hp hp2 hcen hin hα hlabJ hJ =>
      inn_of_families hInnLin hInnUni hInnSymp hInnOrth hInnExc S p α J labK labJ hp hp2 hcen hin hα hlabJ hJ)
    (fun S _ _ p α J labK labJ hp hp2 hcen hfld hnot hα hlabJ hJ =>
      fld_of_families hFldLin hFldUni hFldSymp hFldOrth hFldExc S p α J labK labJ hp hp2 hcen hfld hnot hα
        hlabJ hJ)
    hTri

theorem fieldRel_of_canon_n_one (p : ℕ) (labK labJ : GLALabel) (h : (canonLabel labK).n = 1) :
    FieldRel p (canonLabel labK) (canonLabel labJ) :=
  Or.inl (by rw [h]; exact one_dvd _)

end CFSG.LocalAnalysis.GLTheoremA.Y10GField
