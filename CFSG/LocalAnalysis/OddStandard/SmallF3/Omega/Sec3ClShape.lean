module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Four
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutSeven
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInner
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IOrd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem cl_isFStarGroup_omegaGroup_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = -1) :
    IsFStarGroup (omegaGroup hQ) := by
  refine Or.inr ⟨isQuasisimple_omegaGroup_four_minus hQ hdim hs, Or.inl ?_⟩
  have hodd := oddCore_omegaGroup_four_minus hQ hdim hs
  exact LieModel.of_mulEquiv
    ((QuotientGroup.quotientBot (G := omegaGroup hQ)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hodd.symm))
    (lieModel_omegaGroup_four_minus hQ hdim hs)

theorem cl_isFStarGroup_omegaGroup_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) : IsFStarGroup (omegaGroup hQ) := by
  have hq := isQuasisimple_omegaGroup_five hQ hdim
  have hZ : Subgroup.center (omegaGroup hQ) = ⊥ :=
    Subgroup.card_eq_one.mp (natCard_center_omegaGroup_five hQ hdim)
  have hLie : LieModel (omegaGroup hQ) .PSp 2 3 1 :=
    LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      (lieModel_quotient_center_omegaGroup_five hQ hdim)
  have hfs := ff_fin_simple_psp hLie
  haveI : Finite (omegaGroup hQ) := hfs.1
  have hquot := ff_lieModel_quot_oddCore hLie hfs.2
    (by rw [ff_card_model_psp hLie]; norm_num)
  exact Or.inl ⟨hq, Or.inl (Or.inl hquot)⟩

theorem cl_isFStarGroup_omegaGroup_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    IsFStarGroup (omegaGroup hQ) := by
  have hq := isQuasisimple_omegaGroup_six_plus hQ hdim hs
  have hZ : Subgroup.center (omegaGroup hQ) = ⊥ :=
    Subgroup.card_eq_one.mp (natCard_center_omegaGroup_six_plus hQ hdim hs)
  have hLie : LieModel (omegaGroup hQ) .PSL 4 3 1 :=
    LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      (lieModel_quotient_center_omegaGroup_six_plus hQ hdim hs)
  have hfs : Finite (omegaGroup hQ) ∧ IsSimpleGroup (omegaGroup hQ) := by
    have := CFSG.LieType.Simplicity.fam_classical_converse (omegaGroup hQ)
      ⟨.PSL, 4, 3, 1, hLie.statedClassicalModel_of_ne_zero (by norm_num)⟩
    exact ⟨this.1, this.2.2⟩
  haveI : Finite (omegaGroup hQ) := hfs.1
  have hquot := ff_lieModel_quot_oddCore hLie hfs.2
    (by rw [ff_card_model_psl4 hLie]; norm_num)
  exact Or.inl ⟨hq, Or.inl (Or.inr (Or.inl hquot))⟩

theorem cl_isFStarGroup_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    IsFStarGroup (omegaGroup hQ) := by
  have hq := isQuasisimple_omegaGroup_six_minus hQ hdim hs
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaGroup hQ) := Subtype.finite
  have hodd := oddCore_eq_bot_of_isTwoU43 hq (isTwoU43_omegaGroup hQ hdim hs)
  have h2u : IsTwoU43 (omegaGroup hQ ⧸ oddCore (omegaGroup hQ)) :=
    isTwoU43_of_mulEquiv
      ((QuotientGroup.quotientBot (G := omegaGroup hQ)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hodd.symm))
      (isTwoU43_omegaGroup hQ hdim hs)
  exact Or.inl ⟨hq, Or.inr h2u⟩

theorem cl_lieModel_omegaGroup_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) : LieModel (omegaGroup hQ) .POmegaOdd 3 3 1 := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hcard3 : Nat.card (ZMod 3) = 3 ^ 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    norm_num
  obtain ⟨-, hmodel⟩ :=
    CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_derived
      (p := 3) (e := 1) (n := 3) Nat.prime_three (by norm_num) le_rfl
      hcard3 Q hQ' (Or.inl ⟨hdim, le_rfl⟩)
  rw [← omegaGroup_eq_commutator hQ (by omega), hdim] at hmodel
  obtain ⟨t, n, f, hmem, -, hLie⟩ := hmodel
  have htup : (t, n, f) = (.POmegaOdd, 3, 1) := by
    unfold CFSG.ComponentClassification.CatLeafProof.X10Lin.orthTuples at hmem
    simp only [Set.mem_setOf_eq] at hmem
    rcases hmem with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hx⟩ | ⟨h, -⟩
    · omega
    · omega
    · omega
    · omega
    · simp only [hx, show (7 : ℕ) / 2 = 3 by norm_num]
    · omega
  have ht : t = .POmegaOdd := (Prod.mk.inj htup).1
  have hn : n = 3 := (Prod.mk.inj (Prod.mk.inj htup).2).1
  have hf : f = 1 := (Prod.mk.inj (Prod.mk.inj htup).2).2
  rw [ht, hn, hf] at hLie
  have hquot : Nat.card (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) = 4585351680 := by
    rw [hLie.card_eq_lieOrd (by norm_num)]
    decide +kernel
  have hZ1 : Nat.card (Subgroup.center (omegaGroup hQ)) = 1 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (omegaGroup hQ))
    rw [natCard_omegaGroup_seven hQ hdim, hquot] at hcard
    have h : 4585351680 * Nat.card (Subgroup.center (omegaGroup hQ)) = 4585351680 * 1 := by
      rw [mul_one]; exact hcard.symm
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4585351680) h
  have hZ : Subgroup.center (omegaGroup hQ) = ⊥ := Subgroup.card_eq_one.mp hZ1
  exact LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hLie

theorem cl_isFStarGroup_omegaGroup_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) : IsFStarGroup (omegaGroup hQ) := by
  have hLie := cl_lieModel_omegaGroup_seven hQ hdim
  have hq := isQuasisimple_omegaGroup_seven hQ hdim
  have hfs := CFSG.LieType.Simplicity.fam_classical_converse (omegaGroup hQ)
    ⟨.POmegaOdd, 3, 3, 1, hLie.statedClassicalModel_of_ne_zero (by norm_num)⟩
  haveI : Finite (omegaGroup hQ) := hfs.1
  have hquot := ff_lieModel_quot_oddCore hLie hfs.2.2
    (by rw [natCard_omegaGroup_seven hQ hdim]; norm_num)
  exact Or.inl ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hquot))))⟩

end CFSG.OddStandard.SmallF3.Omega
