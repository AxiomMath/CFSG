module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAsmRanks
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdSchur
public import CFSG.Assembly.InCatalogConverse
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinModelAutRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAsmBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (finite_mulAut_of_finite)
open scoped commutatorElement


private theorem three_le_of_cfg
    {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω} {L : Subgroup Ω}
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (PSimple 3 L))) :=
  three_le_pRank_mulAut_pSimple hcfg hO

private theorem center_of_glaPPrimeCore_of_nontrivial
    {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω} {L : Subgroup Ω}
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hnt : Nontrivial (PSimple 3 L)) :
    GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L :=
  CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hcfg.qs inferInstance
    (hstd_ne_top_of_one_lt (K := L) (by exact Finite.one_lt_card_iff_nontrivial.2 hnt))

theorem false_of_ambiguousChev_two
    {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω} {L : Subgroup Ω}
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hAmb : catalogIs (PSimple 3 L) (ambiguousChev 2)) : False := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hAmb
  cases i with
  | cyclic p hp => simpa [ambiguousChev] using hi
  | sporadic s => simpa [ambiguousChev] using hi
  | alternating n hn =>
    haveI : Nontrivial (alternatingGroup (Fin n)) := by
      simp only [ambiguousChev] at hi
      rcases hi with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h8, -⟩
      · subst n
        exact alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
      · subst n
        exact alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
      · subst n
        exact alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    haveI : Finite (MulAut (alternatingGroup (Fin n))) := finite_mulAut_of_finite _
    have hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L :=
      center_of_glaPPrimeCore_of_nontrivial hcfg (f.toEquiv.nontrivial)
    have h3 := three_le_of_cfg hcfg hO
    have hEq : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (PSimple 3 L))) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (alternatingGroup (Fin n)))) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (MulAut.congr f)
    have h3' : 3 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (MulAut (alternatingGroup (Fin n)))) := by
      rwa [hEq] at h3
    simp only [ambiguousChev] at hi
    rcases hi with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h8, -⟩
    · subst n
      have := pRank_mulAut_alt_five_le_one
      omega
    · subst n
      have := pRank_mulAut_alt_six_le_two
      omega
    · subst n
      have := pRank_mulAut_alt_eight_le_two
      omega
  | lie dd =>
    obtain ⟨d0, hv⟩ := dd
    cases d0 with
    | A r q =>
      cases r with
      | zero => simpa [ambiguousChev] using hi
      | succ r =>
        cases r with
        | zero =>
          have hq : q.card = 7 := by simpa [ambiguousChev] using hi
          haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group :=
            (CFSG.Assembly.lie_finite_simple ⟨.A 1 q, hv⟩).1
          haveI : Nontrivial (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group :=
            ((CFSG.Assembly.lie_finite_simple ⟨.A 1 q, hv⟩).2).toNontrivial
          haveI : Finite (MulAut (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) :=
            finite_mulAut_of_finite _
          haveI : Nontrivial (PSimple 3 L) :=
            f.toEquiv.nontrivial
          have hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L :=
            center_of_glaPPrimeCore_of_nontrivial hcfg inferInstance
          have h3 := three_le_of_cfg hcfg hO
          have hEq : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (PSimple 3 L))) =
              CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut
                (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group)) :=
            CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (MulAut.congr f)
          have h3' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut
              (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group)) := by
            rwa [hEq] at h3
          have := pRank_mulAut_lie_A1_seven q hv hq
          omega
        | succ r =>
          cases r with
          | zero => exact hi
          | succ r =>
            change False at hi
            exact hi
    | twistedA r q =>
      cases r with
      | zero => simpa [ambiguousChev] using hi
      | succ r =>
        cases r with
        | zero => simpa [ambiguousChev] using hi
        | succ r =>
          cases r with
          | zero =>
            have hq : q.card = 3 := by simpa [ambiguousChev] using hi
            haveI : Finite (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group :=
              (CFSG.Assembly.lie_finite_simple ⟨.twistedA 2 q, hv⟩).1
            haveI : Nontrivial (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group :=
              ((CFSG.Assembly.lie_finite_simple ⟨.twistedA 2 q, hv⟩).2).toNontrivial
            haveI : Finite (MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) :=
              finite_mulAut_of_finite _
            haveI : Nontrivial (PSimple 3 L) :=
              f.toEquiv.nontrivial
            have hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L :=
              center_of_glaPPrimeCore_of_nontrivial hcfg inferInstance
            have h3 := three_le_of_cfg hcfg hO
            have hEq : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (PSimple 3 L))) =
                CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut
                  (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)) :=
              CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (MulAut.congr f)
            have h3' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut
                (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)) := by
              rwa [hEq] at h3
            have := pRank_mulAut_lie_U33 q hv hq
            omega
          | succ r =>
            simp only [ambiguousChev] at hi
            split at hi <;> simp_all
    | _ =>
      change False at hi
      exact hi

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
