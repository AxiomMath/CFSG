module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144InnOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Card
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144OutD4Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144OutTD4Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16005
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2323
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate9124

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieSemisimpleCent LieOrderBridge)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind TriPiece)
open CFSG.StandardType (GGLabelRigidInput)

section OutFalse

theorem out_false_of_two_le (hTri : TriPiece) (hLSC : LieSemisimpleCent) {S : Type} [Group S]
    [Finite S] (hcen : Subgroup.center S = ⊥) {labK : GLALabel}
    (hlab : HasLabel S (fun l : GLALabel => l = labK))
    (htag : labK.tag = .triD4 ∨ (labK.tag = .D ∧ labK.rank = 4)) (hn : 2 ≤ labK.n)
    {β : MulAut S} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {Jb : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup β) Jb) (hcat : catalogIs (PSimple 3 Jb) I144Cat) :
    False := by
  obtain ⟨labJ, hlabJ, hnJ, htagJ⟩ := exists_label_component hLSC hcen hlab hn hβ3 hβ1 hJ hcat
  have hrel := hTri S 3 β Jb labK labJ rfl hcen hlab htag hβ3 hlabJ hJ
  have hcanK : canonLabel labK = labK := by
    obtain ⟨t, r, m⟩ := labK
    rcases htag with h | ⟨h, hr⟩
    · simp only at h
      subst h
      simp [canonLabel]
    · simp only at h hr
      subst h hr
      simp [canonLabel]
  rw [hcanK] at hrel
  rcases hrel with h1 | ⟨-, h2⟩
  · rw [hnJ] at h1
    have := Nat.dvd_one.1 h1
    omega
  · rcases h2 with ⟨ht, -⟩ | ⟨-, -, -, htJ⟩
    · rcases htag with h | ⟨h, -⟩ <;> rcases htagJ with h' | h' <;> simp [h, h'] at ht
    · rcases htagJ with h' | h' <;> simp [h'] at htJ

theorem out_D4two_false (hB : LieOrderBridge) {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥)
    (hlab : HasLabel S (fun l : GLALabel => l = (⟨.D, 4, 1⟩ : GLALabel))) {β : MulAut S}
    (hβ3 : β ^ 3 = 1) (hnin : ¬ InnDiagKind S (⟨.D, 4, 1⟩ : GLALabel) β)
    (hnfld : ¬ FieldKind S (⟨.D, 4, 1⟩ : GLALabel) β) {Jb : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup β) Jb) (hcat : catalogIs (PSimple 3 Jb) I144Cat) :
    False := by
  have h1 := card_fix_le_D4two hcen hlab hβ3 hnin hnfld
  have h2 := card_pSimple_le_fix hJ
  have h3 := card_ge_of_catalog hB hcat
  omega

theorem out_D4_false (hRig : GGLabelRigidInput) (hTri : TriPiece) (hLSC : LieSemisimpleCent)
    (hB : LieOrderBridge) {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {labK : GLALabel} (hlab : HasLabel S (fun l : GLALabel => l = labK)) (htag : labK.tag = .D)
    (hrk : labK.rank = 4) {β : MulAut S} (hβ3 : β ^ 3 = 1) (hnin : ¬ InnDiagKind S labK β)
    (hnfld : ¬ FieldKind S labK β) {Jb : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup β) Jb)
    (hcat : catalogIs (PSimple 3 Jb) I144Cat) : False := by
  by_cases hβ1 : β = 1
  · subst hβ1
    obtain ⟨-, h2⟩ := canon_of_trivial hRig hcen hlab hJ hcat
    obtain ⟨t, r, m⟩ := labK
    simp only at htag hrk
    subst htag hrk
    simp [canonLabel] at h2
  · by_cases hn : 2 ≤ labK.n
    · exact out_false_of_two_le hTri hLSC hcen hlab (Or.inr ⟨htag, hrk⟩) hn hβ3 hβ1 hJ hcat
    · have hn1 : labK.n = 1 := by
        have := (CanonSubcomp.lambda2_of_hasLabel hlab).1
        omega
      obtain ⟨t, r, m⟩ := labK
      simp only at htag hrk hn1
      subst htag hrk hn1
      exact out_D4two_false hB hcen hlab hβ3 hnin hnfld hJ hcat

end OutFalse

end CFSG.LocalAnalysis.GLTheoremA.K144
