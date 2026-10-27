module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def TriOuterD4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    labK.tag = .D → labK.rank = 4 → Subgroup.center S = ⊥ →
      HasLabel S (fun l : GLALabel => l = labK) → ¬ InnDiagKind S labK α → ¬ FieldKind S labK α →
        α ^ 3 = 1 → HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent 3 (fixSubgroup α) J →
          FieldRel 3 (canonLabel labK) (canonLabel labJ)

@[expose] def TriFieldTD4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel),
    labK.tag = .triD4 → Subgroup.center S = ⊥ →
      HasLabel S (fun l : GLALabel => l = labK) → FieldKind S labK α →
        α ^ 3 = 1 → HasLabel ↥J (fun l : GLALabel => l = labJ) → GLAPComponent 3 (fixSubgroup α) J →
          FieldRel 3 (canonLabel labK) (canonLabel labJ)

theorem triPiece_of_pieces' (hFO : FldOrth) (hCE : ClsExc) (hIO : InnDiagOrth) (hIE : InnDiagExc)
    (hTO : TriOuterD4) (hTF : TriFieldTD4) : TriPiece := by
  intro S _ _ p α J labK labJ hp3 hcen hlabK htag hα hlabJ hJ
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  rcases htag with ht | ⟨ht, hr⟩
  ·
    have hfam : FamExc labK := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
    rcases hCE S 3 α labK hfam hp hp2 hcen hlabK hα with hin | hfld
    · exact Or.inl (hIE S 3 α J labK labJ hfam hp hp2 hcen hin hα hlabJ hJ)
    · exact hTF S α J labK labJ ht hcen hlabK hfld hα hlabJ hJ
  ·
    have hfam : FamOrth labK := Or.inl ⟨ht, by omega⟩
    by_cases hin : InnDiagKind S labK α
    · exact Or.inl (hIO S 3 α J labK labJ hfam hp hp2 hcen hin hα hlabJ hJ)
    · by_cases hfld : FieldKind S labK α
      · obtain ⟨h1, h2, h3⟩ := hFO S 3 α J labK labJ hfam hp hp2 hcen hfld hα hlabJ hJ
        exact Or.inr ⟨h1, Or.inl ⟨h2, h3⟩⟩
      · exact hTO S α J labK labJ ht hr hcen hlabK hin hfld hα hlabJ hJ

theorem triPiece_of_pieces
    (hIO : InnDiagOrth) (hIE : InnDiagExc) (hTO : TriOuterD4) (hTF : TriFieldTD4) : TriPiece :=
  triPiece_of_pieces' CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth.fldOrth_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc.clsExc_holds hIO hIE hTO hTF

end CFSG.LocalAnalysis.GLTheoremA.Y10GField
