module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Family
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.ThreePlus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2Odd
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2Even
public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false

section SplitCase


theorem innerPlaneBalance_adjointG2_three_dvd_sub_one (K : Type) [Field K] [Finite K]
    (h4 : 4 ≤ Nat.card K) (hq : 3 ∣ Nat.card K - 1) :
    InnerPlaneBalance 3 (adjointGroup Tag.G2 K) := by
  have _ := h4
  intro E hEin hE hcard H hH
  obtain ⟨t, htp, ht⟩ := exists_orderOf_units_of_dvd Nat.prime_three (by norm_num) hq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.G2) (K := K)
  set E₀ := E.comap (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K))
  have hE₀el : IsElemAbelian 3 E₀ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have := hE.1
      change MulAut.conj ((a : adjointGroup Tag.G2 K) * (b : adjointGroup Tag.G2 K)) =
        MulAut.conj ((b : adjointGroup Tag.G2 K) * (a : adjointGroup Tag.G2 K))
      rw [map_mul, map_mul]
      exact setLike_mul_comm (Subgroup.mem_comap.1 a.2) (Subgroup.mem_comap.1 b.2)
    · apply hinj
      rw [map_pow, map_one]
      exact hE.2 _ (Subgroup.mem_comap.1 hx)
  haveI : CFSG.IsElementaryAbelian 3 E₀ :=
    { toIsMulCommutative := hE₀el.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hE₀el.2 g g.2) }
  have hΓY : conjEntrywiseImage K (1 : ModGL .G2 K) ≤ adjointGroup .G2 K := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using baseChangeGL_mem_adjointGroup (algebraMap K K) hx
  obtain ⟨y, hy⟩ := exists_planeImage_conj_le hΓY hq E₀
  refine localDeltaIn_eq_bot_of_conj_toral Nat.prime_three htp ht hH hEin hE.2 ?_ y ?_
  · rw [hcard]; norm_num
  · intro x hx
    have h1 := (mem_torusTorsion_iff.1 (hy x hx)).1
    simpa [twistEmb_apply, baseChangeGL_id] using h1

end SplitCase

section PlusCase


theorem innerPlaneBalance_adjointG2_three_dvd_add_one (K : Type) [Field K] [Finite K]
    (h4 : 4 ≤ Nat.card K) (hq : 3 ∣ Nat.card K + 1) :
    InnerPlaneBalance 3 (adjointGroup Tag.G2 K) :=
  G2Aux.innerPlaneBalance_three_of_dvd_add_one K h4 hq

end PlusCase

section Five


theorem innerPlaneBalance_adjointG2_five (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (adjointGroup Tag.G2 K)] (h5 : ¬ 5 ∣ Nat.card K) :
    InnerPlaneBalance 5 (adjointGroup Tag.G2 K) := by
  have hp : Nat.Prime 5 := by norm_num
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.G2) (K := K)
  have hmod : Nat.card K % 5 = 1 ∨ Nat.card K % 5 = 2 ∨ Nat.card K % 5 = 3 ∨
      Nat.card K % 5 = 4 := by omega
  have hvac : Nat.card K % 5 = 2 ∨ Nat.card K % 5 = 3 → InnerPlaneBalance 5 (adjointGroup Tag.G2 K) := by
    intro h
    have h6 : Nat.card K ^ 6 % 5 = 4 := by
      rw [Nat.pow_mod]
      rcases h with h | h <;> rw [h]
    have h6' : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ hq
    have hd6 : ¬ 5 ∣ Nat.card K ^ 6 - 1 := by omega
    have hnd := G2Aux.not_dvd_card_adjointG2 K hp h5 hd6
    exact innerPlaneBalance_of_rankLE1 hp hinj fun F hF => by
      rw [elemAbelian_card_eq_one_of_not_dvd hp hnd F hF]
      exact hp.one_lt.le
  rcases hmod with h1 | h2 | h3 | h4
  · have hpq : 5 ∣ Nat.card K - 1 := by omega
    exact innerPlanes_adjointG2_of_dvd_sub_one hp le_rfl hpq
  · exact hvac (Or.inl h2)
  · exact hvac (Or.inr h3)
  · have hpq : 5 ∣ Nat.card K + 1 := by omega
    by_cases hodd : Odd (Nat.card K)
    · exact innerPlaneBalance_adjointG2_qplus_odd K hodd hp le_rfl hpq
    · haveI := G2Aux.charP_two_of_even_natCard K (Nat.not_odd_iff_even.1 hodd)
      exact innerPlaneBalance_adjointG2_qplus_even
        (RankThree.PartOne.SEITZ6.maxSL2SL2G2_of_top CFSG.Goldschmidt.topStatement) K hp le_rfl hpq

end Five

section Families


theorem localTwoCrossFamCat_three_G2 : LocalTwoCrossFamCat 3 .G2 :=
  G2Aux.localTwoCrossFamCat_G2_of_inner Nat.prime_three (Or.inl rfl) fun K _ _ hK3 h3 => by
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have hmod : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
    rcases hmod with h | h
    · exact innerPlaneBalance_adjointG2_three_dvd_sub_one K (by omega) (by omega)
    · exact innerPlaneBalance_adjointG2_three_dvd_add_one K (by omega) (by omega)

theorem localTwoCrossFamCat_five_G2 : LocalTwoCrossFamCat 5 .G2 :=
  G2Aux.localTwoCrossFamCat_G2_of_inner (by norm_num) (Or.inr rfl) fun K _ _ hK3 h5 => by
    haveI : IsSimpleGroup (adjointGroup Tag.G2 K) :=
      CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_of_isQuasisimple
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3)
    exact innerPlaneBalance_adjointG2_five K h5

end Families

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
