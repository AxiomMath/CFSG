module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson

import CFSG.Quasithin.Background.P4InspOrthPlus4
import CFSG.LocalAnalysis.SteinbergBVA7BinaryIsometryTwoParts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

open CFSG.GroupTheory.WeirSylow

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem isPlusType_of_ncard_six (Q : QuadraticForm (ZMod 2) W)
    (hQ : Q.polarBilin.Nondegenerate) (h4 : Module.finrank (ZMod 2) W = 4)
    (h6 : {v | Q v = 1}.ncard = 6) : IsPlusType Q := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hnd : ∀ x, (∀ y, QuadraticMap.polar (⇑Q) x y = 0) → x = 0 :=
    fun x hx => hQ.1 x fun y => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hx y
  have hmodel : {v | CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2) v = 1}.ncard = 6 := by
    have h := CFSG.LocalAnalysis.SteinbergBV.BinaryTwoParts.two_mul_ncard_quadPlus 1
    have h2 : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    have h4 : (4 : ℕ) ^ (1 + 1) = 16 := by norm_num
    rw [h2, h4] at h
    have h' : 2 * {v | (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2)) v = 1}.ncard +
        4 = 16 := h
    omega
  have hcardW : Nat.card W = 4 ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod, h4]
    norm_num
  have hcardM : Nat.card (Fin 2 ⊕ Fin 2 → ZMod 2) = 4 ^ 2 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_sum, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
  have hcard : Nat.card W = Nat.card (Fin 2 ⊕ Fin 2 → ZMod 2) :=
    hcardW.trans hcardM.symm
  have hN : {v | Q v = 1}.ncard =
      {v | CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2) v = 1}.ncard :=
    h6.trans hmodel.symm
  have hndM : ∀ x, (∀ y, QuadraticMap.polar
      (⇑(CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2))) x y = 0) → x = 0 :=
    fun x hx => (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 (ZMod 2)).1 x
      fun y => by
        rw [QuadraticMap.polarBilin_apply_apply]
        exact hx y
  obtain ⟨L, hL⟩ := CFSG.Fischer.Classification.exists_linearEquiv_of_ncard_eq Q
    (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2)) hnd hndM hcard hN
  exact (isPlusType_congr ({ toLinearEquiv := L, map_app' := hL } :
    Q.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2)))).2
    (isPlusType_quadPlus (ZMod 2) 2)

theorem isSolvable_orthogonalGroup_plus_four (Q : QuadraticForm (ZMod 2) W)
    (hQ : Q.polarBilin.Nondegenerate) (h4 : Module.finrank (ZMod 2) W = 4)
    (h6 : {v | Q v = 1}.ncard = 6) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hplus := isPlusType_of_ncard_six Q hQ h4 h6
  have hf : CFSG.Quasithin.G11.IsSymplectic Q.polarBilin := by
    refine ⟨fun x => ?_, fun x hx => hQ.1 x hx⟩
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hq : ∀ x y, Q (x + y) = Q x + Q y + Q.polarBilin x y := by
    intro x y
    rw [QuadraticMap.map_add (⇑Q) x y, QuadraticMap.polarBilin_apply_apply]
  have hplus' : IsPlusType (CFSG.Quasithin.G11.P4InspOrth.p4insporth_quad hq) := by
    obtain ⟨Z, hZ, hZs⟩ := hplus
    exact ⟨Z, hZ, fun x hx => by
      rw [CFSG.Quasithin.G11.P4InspOrth.p4insporth_quad_apply hq]
      exact hZs x hx⟩
  have hsub : CFSG.Quasithin.G11.orthSub (⇑Q) =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  have hsolv := CFSG.Quasithin.G11.P4InspOrth.p4insporth_solvable_plus_four hf hq h4 hplus'
  rwa [hsub] at hsolv

theorem isSolvable_omegaGroup_plus_four (Q : QuadraticForm (ZMod 2) W)
    (hQ : Q.polarBilin.Nondegenerate) (h4 : Module.finrank (ZMod 2) W = 4)
    (h6 : {v | Q v = 1}.ncard = 6) :
    Group.IsSolvable ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) := by
  haveI : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
    isSolvable_orthogonalGroup_plus_four Q hQ h4 h6
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ))
    (Subgroup.inclusion_injective (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ))

end CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon
