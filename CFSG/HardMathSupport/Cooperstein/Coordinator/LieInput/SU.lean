module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SULevi

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.BorelTits CFSG.LieType.CurtisTits

section Main


theorem simpleStmt_of_psu_model {Y : Type} [Group Y] [Finite Y]
    (hcl : IsClassicalTwoOrG2 Y) {n f : ℕ} (h : StatedClassicalModel Y .PSU n 2 f) :
    SimpleStmt Y := by
  obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hcharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hf, hn, hne⟩ := hadm
  obtain ⟨hq, hZsc⟩ := isQuasisimple_statedSU_of_card hcard hn hne
  have hqQ : CFSG.IsQuasisimple (StatedSU n (2 ^ f) F ⧸ Subgroup.center (StatedSU n (2 ^ f) F)) :=
    (isQuasisimple_of_central_quotient (QuotientGroup.mk' (Subgroup.center (StatedSU n (2 ^ f) F)))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hq).1
  have eY : Y ≃* StatedSU n (2 ^ f) F ⧸ Subgroup.center (StatedSU n (2 ^ f) F) :=
    e.trans (QuotientGroup.quotientMulEquivOfEq hZsc.symm)
  have hsY : IsSimpleGroup Y := by
    have : IsSimpleGroup (StatedSU n (2 ^ f) F ⧸ Subgroup.center (StatedSU n (2 ^ f) F)) := hq.2.1
    exact eY.isSimpleGroup
  have hqY : CFSG.IsQuasisimple Y := isQuasisimple_of_mulEquiv eY.symm hqQ
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_quasisimple_simple hqY
  have hb := borelQuotient_su hcard (by omega) (Classical.choose (exists_traceZero_ne_zero hcard))
    (Classical.choose_spec (exists_traceZero_ne_zero hcard)) e
  have hX := CFSG.HardMathSupport.Cooperstein.StructureLie.evenLieType_or_alt_six_or_psu_of_isClassicalTwoOrG2
    hcl
  have hrad : CFSG.Quasithin.SmithC27.IsRadicalParabolic (⊤ : Subgroup Y) :=
    CFSG.Quasithin.C22Pf.isRadicalParabolic_c224_holds Y hX
  exact simpleStmt_of_borelQuotient hqY hZ hcl hrad hb
    (fun π' hπ' I hI => leviOb_su hcard π' (fun z hz => hπ'.ker_central z hz) I hI)
    (fun I hI => centOb_su hcard hI)

theorem simpleStmt_of_twistedA_index {Y : Type} [Group Y] [Finite Y]
    (hcl : IsClassicalTwoOrG2 Y) {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (hdq : d.1 = .twistedA r q) (hp : q.p = 2) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    SimpleStmt Y := by
  obtain ⟨d, hv⟩ := d
  have hdq' : d = .twistedA r q := hdq
  subst hdq'
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hp] at h
  exact simpleStmt_of_psu_model hcl h

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
