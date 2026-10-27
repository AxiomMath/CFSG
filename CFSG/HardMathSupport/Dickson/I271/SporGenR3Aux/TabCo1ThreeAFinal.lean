module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeASuzInv

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Dickson.I271

section Rank

theorem rkSpor_Suz_of_cover
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) {T : Type} [Group T] [Finite T]
    (hq : CFSG.Open.IsQuasisimple T) (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1)
    (hcard : Nat.card (T ⧸ Subgroup.center T) = 448345497600) : RkSpor 3 [.Suz] T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro (⟨-, ⟨f⟩⟩ | ⟨S, hS, ⟨f⟩⟩)
  · exfalso
    have h360 : Nat.card (T ⧸ Subgroup.center T) = 360 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    omega
  · simp only [List.mem_singleton] at hS
    subst hS
    have hX : ∃ x : NativeSporadic.Carrier .Suz, x ≠ 1 ∧ x ^ 3 = 1 := by
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := T ⧸ Subgroup.center T) 3
        (by rw [hcard]; norm_num)
      have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
      have hy3 : y ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hy)
      let e' : (T ⧸ Subgroup.center T) ≃* NativeSporadic.Carrier .Suz :=
        f.trans (hBr .Suz).some.symm
      exact ⟨e' y, fun h => hy1 (e'.injective (by rw [h, map_one])), by
        rw [← map_pow, hy3, map_one]⟩
    exact rkAut_three_of_sporadic_cover (X := .Suz) hOut hBr rkBMInv_Suz hX hq hZ3 f

end Rank

section Final

theorem co1ThreeAShape_holds
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) : Co1ThreeAShape := by
  intro x hx
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨J, hJC, hJn, hq, hp3, hcard3, hcent, hqcard, ⟨eJ⟩⟩ := threeA_data (hBr .Suz) hx
  haveI : Finite ↥J := inferInstance
  have hGood : GoodSpor 3 [.Suz] (↥J ⧸ Subgroup.center ↥J) :=
    Or.inr (Or.inr ⟨.Suz, List.mem_singleton_self _, ⟨eJ⟩⟩)
  have hRk : RkSpor 3 [.Suz] ↥J :=
    rkSpor_Suz_of_cover hOut hBr hq (rkBM_pow_three_of_card_dvd (by rw [hcard3])) hqcard
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥J) :=
    IsPGroup.of_card (n := 1) (by rw [hcard3]; norm_num)
  exact shapeRkAt_of_subgroup_data_quasi Nat.prime_three
    (fun _ _ _ _ e h => GoodSpor.of_equiv e h) (fun _ _ _ _ e h => RkSpor.of_equiv e h)
    GA x J hJC hJn hq hp3 hZp hcent hGood hRk

end Final

end CFSG.HardMathSupport.Dickson.I271.TabCo1
