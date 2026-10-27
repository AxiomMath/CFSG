module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagPSL2
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagAccidental
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Cube
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GorensteinWalter
  CFSG.RankThree.PartOne.Sec66T
open CFSG.HardMathSupport.Dickson.Sec6.I923 (FamPslTwo)

theorem isInnerAut_of_mem_innAutDerived_psl2 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) {K : Type} [Field K] [Finite K]
    (e : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 2 K)) {α : MulAut Y} (h3 : α ^ 3 = 1)
    (hα : α ∈ innAutDerived Y) : IsInnerAut α := by
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  let e1 : (Y ⧸ Subgroup.center Y) ≃* PSL2 K := e.trans (psl2StatedEquiv K).symm
  have h1 : centerDescend Y α ∈ innAutDerived (Y ⧸ Subgroup.center Y) :=
    centerDescend_mem_innAutDerived hα
  have h2 := innAutDerived_le_comap_stdPinnedPSL2_inndiag K e1 h1
  have h4 := isInnerAut_of_mem_inndiag_of_pow_three ((PinnedAut.mem_comap_inndiag _ e1).1 h2)
    (by rw [← map_pow, ← map_pow, h3, map_one, map_one])
  exact isInnerAut_of_isInnerAut_centerDescend ((isInnerAut_congr e1 _).1 h4)

theorem y1431_noCfg_pslTwo (hU : L2OrderUnique) (h1 : L2Aut3Classification) (hF : L2FieldFixed)
    (h0 : L2CentreThree) : Y1431NoCfgAt FamPslTwo := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hFam hm q0 hq0 hqq
  obtain ⟨rfl, rfl⟩ := hFam
  have hq := c.quasisimple
  haveI : Group.IsPerfect Y := ⟨hq.1⟩
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have hs : IsTypeL2 (p ^ f) Y := ⟨K, inferInstance, inferInstance, hK, ⟨e0⟩⟩
  have hq10 : 10 ≤ q := ten_le_of_cube hq0 hqq
  rcases l2fld_core hU h1 hF h0 hq c.core hs c.pow_three c.comp c.typeL2 with
    ⟨ha, -⟩ | ⟨hne, hfld, hsq⟩
  · exact c.ne_one ha
  · have hsq' : p ^ f = q ^ 3 := by
      rcases hsq with h | ⟨h4, -⟩
      · exact h
      · omega
    have hinn : IsInnerAut ξ :=
      isInnerAut_of_mem_innAutDerived_psl2 hq e0 c.pow_three (c.mem_innAutDerived c.mem)
    have h3 : ¬ 3 ∣ p ^ f := fun h =>
      c.not_dvd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hsq' ▸ h))
    have h8 : p ^ f ≠ 8 := by
      rw [hsq']
      have : 10 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq10 3
      omega
    refine not_isInnerAut_descend_of_fieldAut hU hF hq c.pow_three hne hfld hs h3 h8 ?_
    obtain ⟨y, rfl⟩ := hinn
    exact ⟨↑y, (CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj y).symm⟩

end CFSG.HardMathSupport.Dickson.Sec6.I1431
