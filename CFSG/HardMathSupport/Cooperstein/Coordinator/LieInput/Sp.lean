module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Engine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.AGLEmbeddingD2.ParabLevi

@[expose] def SpLeviOb : Prop :=
  ∀ (n f : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2], StatedLieAdmissible .PSp n 2 f →
    Nat.card F = 2 ^ f → ∀ {Y : Type} [Group Y] (π : StatedSp n F →* Y),
      (∀ z ∈ π.ker, z ∈ Subgroup.center (StatedSp n F)) →
        ∀ I : Set (Fin n), I ≠ Set.univ → LeviOb (rootDatum n F) (torus n F) π I

@[expose] def SpCentOb : Prop :=
  ∀ (n f : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2], StatedLieAdmissible .PSp n 2 f →
    Nat.card F = 2 ^ f → ∀ I : Set (Fin n), I ≠ Set.univ → CentOb (rootDatum n F) I

section Main


theorem simpleStmt_of_psp_model (hL : SpLeviOb) (hC : SpCentOb) {Y : Type} [Group Y] [Finite Y]
    (hcl : IsClassicalTwoOrG2 Y) {n f : ℕ} (h : StatedClassicalModel Y .PSp n 2 f) :
    SimpleStmt Y := by
  obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hcharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨hp, hf, hn, hne⟩ := hadm
  have hq := Symplectic.isQuasisimple_of_admissible n F ⟨hp, hf, hn, hne⟩ hcard
  have hqQ : CFSG.IsQuasisimple (StatedSp n F ⧸ Subgroup.center (StatedSp n F)) :=
    (isQuasisimple_of_central_quotient (QuotientGroup.mk' (Subgroup.center (StatedSp n F)))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hq).1
  have eY : Y ≃* StatedSp n F ⧸ Subgroup.center (StatedSp n F) :=
    e.trans (centerQuotientEquiv n F).symm
  have hsY : IsSimpleGroup Y := by
    have : IsSimpleGroup (StatedSp n F ⧸ Subgroup.center (StatedSp n F)) := hq.2.1
    exact eY.isSimpleGroup
  have hqY : CFSG.IsQuasisimple Y := isQuasisimple_of_mulEquiv eY.symm hqQ
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_quasisimple_simple hqY
  have hKfin : Finite (StatedSp n F) := inferInstance
  have hb := borelQuotient_sp e
  have hX := CFSG.HardMathSupport.Cooperstein.StructureLie.evenLieType_or_alt_six_or_psu_of_isClassicalTwoOrG2
    hcl
  have hrad : CFSG.Quasithin.SmithC27.IsRadicalParabolic (⊤ : Subgroup Y) :=
    CFSG.Quasithin.C22Pf.isRadicalParabolic_c224_holds Y hX
  exact simpleStmt_of_borelQuotient hqY hZ hcl hrad hb
    (fun π' hπ' I hI => hL n f F ⟨hp, hf, hn, hne⟩ hcard π' (fun z hz => hπ'.ker_central z hz) I hI)
    (fun I hI => hC n f F ⟨hp, hf, hn, hne⟩ hcard I hI)

theorem simpleStmt_of_B_index (hL : SpLeviOb) (hC : SpCentOb) {Y : Type} [Group Y] [Finite Y]
    (hcl : IsClassicalTwoOrG2 Y) {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (hdq : d.1 = .B r q) (hp : q.p = 2) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    SimpleStmt Y := by
  obtain ⟨d, hv⟩ := d
  have hdq' : d = .B r q := hdq
  subst hdq'
  have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
  by_cases h2 : r = 2
  · subst h2
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    rw [hp] at h
    exact simpleStmt_of_psp_model hL hC hcl h
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp
      (by omega) e
    rw [hp] at h
    exact simpleStmt_of_psp_model hL hC hcl h

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
