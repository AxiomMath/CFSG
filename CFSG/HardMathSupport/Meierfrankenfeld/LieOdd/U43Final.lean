module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43BranchB
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inputs
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Small
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.LieType.Multipliers.U43

theorem three_pow_six_dvd_card_X₀ : 3 ^ 6 ∣ Nat.card X₀ := by
  rw [card_X₀]
  norm_num


theorem u43F1 : U43F1 X₀ := fun _ hu => U43Inv.u43_exists_conj_orderOf hu

theorem u43F2 : U43F2 X₀ := fun _ _ ha hb hba hab => by
  obtain ⟨c, hc1, hc2⟩ := U43Inv.u43_F2 ha hb hba hab.symm
  exact ⟨c, hc1, hc2⟩

theorem noIrrFFOffender_X₀_of (hF3 : U43F3 X₀) (hOut : OutElemIndexLE X₀ 4) :
    NoIrrFFOffender X₀ := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel hquad
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center ↥L)
  · exact weight_lt_of_three_dvd_center hW hq hirr e u43_center_eq_bot three_pow_six_dvd_card_X₀
      hZ u43_autTwoRankLE hOut u43F1 u43F2 hF3 hEN hE hel hquad
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact FFToolkit.weight_lt_of_route_A_aut hW hq hirr e u43_center_eq_bot hEN hE hel
      (m := 5) (ρ := 6) (p := 3) (n := 1) (by norm_num) (by norm_num)
      (by rw [orderOf_two_zmod_three]; norm_num) hZ u43_autTwoRankLE u43_hgen

theorem smallU43_of (hF3 : U43F3 X₀) (hOut : OutElemIndexLE X₀ 4) : SmallU43 := by
  intro d q hq hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨φ⟩ := u43_group_equiv hv hq
  exact noFFModule_of_noIrrFFOffender
    (FFSporadic.noIrrFFOffender_transfer (noIrrFFOffender_X₀_of hF3 hOut) ⟨φ.symm⟩)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
