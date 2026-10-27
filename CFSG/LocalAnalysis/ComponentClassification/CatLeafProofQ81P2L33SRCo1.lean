module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Co1.Module.TwoB
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Schreier.Co1OddTransport

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.OddCore
open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1Schreier.OddRows CFSG.Sporadic.SmallF2

theorem co1_rows8_ne_one :
    rowsMatrix 24 (Native.oddReg Native.oddACRegs 8) ≠ 1 := by
  intro h
  obtain ⟨h1, h2, -, -⟩ := OddAC.ac_x_counts
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h1 h2
  simp only [h, Matrix.one_mulVec, and_true] at h2
  rw [h1] at h2
  norm_num at h2

theorem co1_rows1520_ne_one :
    rowsMatrix 24 (Native.oddReg Native.oddACRegs 15) ≠ 1 ∨
      rowsMatrix 24 (Native.oddReg Native.oddACRegs 20) ≠ 1 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨-, -, h3, h4⟩ := OddAC.ac_x_counts
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h3 h4
  simp only [hcon.1, hcon.2, Matrix.one_mulVec, and_true] at h4
  rw [h3] at h4
  norm_num at h4

theorem not_isPGroup_centralizer_of_odd {G : Type*} [Group G] {t s : G} (hc : s * t = t * s)
    {m : ℕ} (hm : Odd m) (hs : s ^ m = 1) (h1 : s ≠ 1) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set G)) :=
  not_isPGroup_of_pow (g := (⟨s, mem_centralizer_singleton_iff.mpr hc⟩ : centralizer {t})) hm
    (Subtype.ext (by simp [hs])) (fun h => h1 (congrArg Subtype.val h))

theorem co1_cent_aCo1_not_isPGroup
    : ¬ IsPGroup 2 ↥(centralizer ({aCo1} : Set NativeSporadic.Co1)) := by
  have hs : matHom (co1GAEquiv.symm ⟨((OddAC.acElt 8 : stabH) : GL24),
      stabH_le_GA (OddAC.acElt 8).2⟩) = rowsMatrix 24 (Native.oddReg Native.oddACRegs 8) :=
    (matHom_symm _).trans (OddAC.coe_acElt 8)
  refine not_isPGroup_centralizer_of_odd
    (commute_of_rows matHom_injective hs matHom_aCo1 OddAC.ac_facts.2.2.2.2.1) (m := 15)
    (by decide) (pow_eq_one_of_rows matHom_injective hs OddAC.ac_facts.2.2.2.2.2.1) ?_
  intro h
  exact co1_rows8_ne_one (by rw [← hs, h, map_one])

theorem co1_cent_cCo1_not_isPGroup
    : ¬ IsPGroup 2 ↥(centralizer ({cCo1} : Set NativeSporadic.Co1)) := by
  have hs15 : matHom (co1GAEquiv.symm ⟨((OddAC.acElt 15 : stabH) : GL24),
      stabH_le_GA (OddAC.acElt 15).2⟩) = rowsMatrix 24 (Native.oddReg Native.oddACRegs 15) :=
    (matHom_symm _).trans (OddAC.coe_acElt 15)
  have hs20 : matHom (co1GAEquiv.symm ⟨((OddAC.acElt 20 : stabH) : GL24),
      stabH_le_GA (OddAC.acElt 20).2⟩) = rowsMatrix 24 (Native.oddReg Native.oddACRegs 20) :=
    (matHom_symm _).trans (OddAC.coe_acElt 20)
  rcases co1_rows1520_ne_one with h15 | h20
  · refine not_isPGroup_centralizer_of_odd (commute_of_rows matHom_injective hs15 matHom_cCo1
      OddAC.ac_facts.2.2.2.2.2.2.2.2.1) (m := 3) (by decide)
      (pow_eq_one_of_rows matHom_injective hs15 OddAC.ac_facts.2.2.2.2.2.2.2.2.2.2.1) ?_
    intro h
    exact h15 (by rw [← hs15, h, map_one])
  · refine not_isPGroup_centralizer_of_odd (commute_of_rows matHom_injective hs20 matHom_cCo1
      OddAC.ac_facts.2.2.2.2.2.2.2.2.2.1) (m := 3) (by decide)
      (pow_eq_one_of_rows matHom_injective hs20 OddAC.ac_facts.2.2.2.2.2.2.2.2.2.2.2) ?_
    intro h
    exact h20 (by rw [← hs20, h, map_one])

theorem co1_cent_sBc_not_isPGroup
    : ¬ IsPGroup 2 ↥(centralizer ({TwoB.sBc} : Set NativeSporadic.Co1)) := by
  have hne : OddB.bElt 9 ≠ 1 := by
    intro h
    apply OddB.prod_pow_ne (i := 9) (j := 19) (by simp) (by simp) OddB.b_facts.2.2.2.2.2.2.1
    rw [h, one_mul, show (15 : ℕ) = 3 * 5 by norm_num, pow_mul, OddB.bElt_nineteen_pow, one_pow]
  exact not_isPGroup_centralizer_of_odd
    (mem_centralizer_singleton_iff.mp (OddB.bElt_mem_cent (by simp))) (m := 3) (by decide)
    OddB.bElt_nine_pow hne

theorem co1_centralizer_not_isPGroup
    : ∀ x : NativeSporadic.Co1, orderOf x = 2 →
      ¬ IsPGroup 2 ↥(centralizer ({x} : Set NativeSporadic.Co1)) := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := CFSG.Monster.GMS.co1_involution_classes
  obtain ⟨-, -, -, hfA, hfB, hfC, -, hqB, hqC, -⟩ := hrep
  have hinv := @CFSG.Monster.GMS.co1Inv_isConj_invariants
  have fixEq : ∀ s : NativeSporadic.Co1,
      CFSG.Monster.GMS.co1Fix s = {v | co1Act s v = v} :=
    fun s => CFSG.Monster.GMS.co1Inv_fix_eq s
  have hA : IsConj aCo1 sA := by
    rcases hcls aCo1 orderOf_aCo1 with h | h | h
    · exact h
    · exfalso
      have h1 := (hinv h).1
      rw [fixEq, fixEq, fix_aCo1, hfB] at h1
      norm_num at h1
    · exfalso
      have h1 := (hinv h).1
      rw [fixEq, fixEq, fix_aCo1, hfC] at h1
      norm_num at h1
  have hC : IsConj cCo1 sC := by
    rcases hcls cCo1 orderOf_cCo1 with h | h | h
    · exfalso
      have h1 := (hinv h).1
      rw [fixEq, fixEq, fix_cCo1, hfA] at h1
      norm_num at h1
    · exfalso
      have h1 := (hinv h).2.1
      rw [fixQ_cCo1, hqB] at h1
      norm_num at h1
    · exact h
  have hB : IsConj TwoB.sBc sB := by
    have ho : orderOf TwoB.sBc = 2 := by
      obtain ⟨-, -, ho, -⟩ := repOK_facts repOK_B
      exact orderOf_eq_of_orderIs TwoB.matHom_sBc (by norm_num) ho
    rcases hcls TwoB.sBc ho with h | h | h
    · exfalso
      have h1 := (hinv h).1
      rw [fixEq, fixEq, TwoB.ncard_fix_sBc, hfA] at h1
      norm_num at h1
    · exact h
    · exfalso
      have h1 := (hinv h).2.1
      rw [TwoB.ncard_fixQ_sBc, hqC] at h1
      norm_num at h1
  intro x hx
  rcases hcls x hx with h | h | h
  · exact not_isPGroup_centralizer_of_isConj (hA.trans h.symm) co1_cent_aCo1_not_isPGroup
  · exact not_isPGroup_centralizer_of_isConj (hB.trans h.symm) co1_cent_sBc_not_isPGroup
  · exact not_isPGroup_centralizer_of_isConj (hC.trans h.symm) co1_cent_cCo1_not_isPGroup

theorem sporNoTwoFix_Co1
    : SporNoTwoFix .Co1 := by
  have hZ : center NativeSporadic.Co1 = ⊥ := center_eq_bot_of_not_prime
    CFSG.Sporadic.Co1.isSimpleGroup_Co1 CFSG.Sporadic.Co1.card_Co1 (by norm_num)
  exact sporNoTwoFix_of_mulEquiv (P := NativeSporadic.Co1) (MulEquiv.refl _)
    (forall_of_inner hZ (full_automorphisms_inner_of_inputs
      CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner) co1_centralizer_not_isPGroup)

end CFSG.ComponentClassification.HarrisLit.L33.SR
