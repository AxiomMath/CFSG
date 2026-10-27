module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveRigid
public import CFSG.HardMathSupport.Seitz.TrialityEven.TwoThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Outer
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.RankThree.PartTwo.Sec4

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_cat_triD4_two {q : TauCeti.PrimePower} (hq : q.p = 2)
    (hq1 : q.exponent = 1) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    InnerPlaneBalance 3 (CatT ⟨.trialityD4 q, hv⟩) := by
  classical
  have hinj := conj_injective_cat_trialityD4 q hv
  obtain ⟨φ, hG⟩ := CFSG.HardMathSupport.Seitz.TrialityEven.exists_equiv_trialityGroup8 hq hq1 hv
  have hcard : Nat.card (CatT ⟨.trialityD4 q, hv⟩) = 211341312 := by
    rw [Nat.card_congr φ.toEquiv]
    exact hG
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (CatT ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide)
        (MulEquiv.refl _)⟩
  rw [hq, hq1] at hm
  have hO := Item434SmallTwoIII.card_outer_d42 hm
  set Y := CatT ⟨.trialityD4 q, hv⟩ with hY
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  intro E hEin hE hEc H hH
  set E₀ : Subgroup Y := E.comap (MulAut.conj : Y →* MulAut Y) with hE₀def
  have hEE : E₀.map (MulAut.conj : Y →* MulAut Y) = E := Subgroup.map_comap_eq_self hEin
  have hE₀c : Nat.card E₀ = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hEE, hEc]
    norm_num
  have hE₀a : IsElemAbelian 3 E₀ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have := hE.1.is_comm.comm ⟨MulAut.conj (a : Y), a.2⟩ ⟨MulAut.conj (b : Y), b.2⟩
      simpa [map_mul] using congrArg Subtype.val this
    · apply hinj
      rw [map_pow, map_one]
      exact hE.2 _ hx
  have hE₀ne : E₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE₀c
    omega
  refine eq_bot_iff.2 fun g hg => ?_
  rw [← hEE] at hg
  obtain ⟨-, hcop, hfix⟩ := mem_localDeltaIn_props Nat.prime_three hinj hE₀ne hg
  have h3 : ¬ 3 ∣ orderOf g := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  have hgin : g ∈ (MulAut.conj : Y →* MulAut Y).range := by
    refine Item434SmallTwoIII.le_inner_of_card_outer_three hO (Y := Subgroup.zpowers g) ?_
      (Subgroup.mem_zpowers g)
    rw [Nat.card_zpowers]
    exact h3
  obtain ⟨y, rfl⟩ := hgin
  have hord : orderOf y = orderOf (MulAut.conj y) := (orderOf_injective _ hinj y).symm
  have hW : ¬ 3 ∣ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers, hord]
    exact h3
  have hEW : E₀ ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup Y) : Set Y) := by
    intro d hd
    have hcomm : MulAut.conj y d = d := hfix d hd
    have hyd : y * d = d * y := by
      have h1 : y * d * y⁻¹ = d := hcomm
      calc y * d = (y * d * y⁻¹) * y := by group
        _ = d * y := by rw [h1]
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hw : ∀ z ∈ Subgroup.zpowers y, d * z * d⁻¹ = z := by
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have hc : Commute d (y ^ k) := ((Commute.zpow_left (hyd : Commute y d) k).symm)
      calc d * y ^ k * d⁻¹ = (d * y ^ k) * d⁻¹ := rfl
        _ = (y ^ k * d) * d⁻¹ := by rw [hc.eq]
        _ = y ^ k := by group
    constructor
    · intro hwm
      rw [hw w hwm]
      exact hwm
    · intro hwm
      have hz := hw _ hwm
      have hwe : d * w * d⁻¹ = w := by
        calc d * w * d⁻¹ = d⁻¹ * (d * (d * w * d⁻¹) * d⁻¹) * d := by group
          _ = d⁻¹ * (d * w * d⁻¹) * d := by rw [hz]
          _ = w := by group
      rw [← hwe]
      exact hwm
  have hbot := RankThree.PartTwo.Sec4.Item434D42.d4_k3_of_equiv φ hcard hE₀a hE₀c hW hEW
  have hy : y = 1 := by
    have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
    rw [hbot] at this
    exact this
  rw [hy, map_one]
  exact one_mem _

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
