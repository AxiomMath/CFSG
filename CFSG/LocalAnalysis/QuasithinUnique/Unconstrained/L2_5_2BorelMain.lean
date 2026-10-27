module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMain

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem isPGroup_ker_of_injective {A B : Type*} [Group A] [Group B] (π : A →* B)
    (h : Function.Injective π) : IsPGroup 2 π.ker := by
  intro x
  refine ⟨0, ?_⟩
  have hx : (x : A) = 1 := h (by rw [map_one]; exact MonoidHom.mem_ker.mp x.2)
  apply Subtype.ext
  simpa using hx

theorem rankTwoBorelFacts : RankTwoBorelFacts := by
  intro G _ _ L P hq hrk hS
  rcases hrk with ⟨n, hn, hL⟩ | ⟨n, hn, hL⟩ | ⟨⟨e⟩⟩ | hcov
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hL.2
    have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
    let e' := e.trans (Fin257.statedSLEquiv F)
    exact Borel252.borelFacts_of_data hq hS Borel252.L3.borelData_L3 e'.toMonoidHom
      e'.surjective (isPGroup_ker_of_injective _ e'.injective)
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hL.2
    have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
    let e' := e.trans (Setup.X7b.antiProjEquiv F).symm
    exact Borel252.borelFacts_of_data hq hS (Borel252.Sp4.borelData_Sp hn hcard) e'.toMonoidHom
      e'.surjective (isPGroup_ker_of_injective _ e'.injective)
  · exact Borel252.borelFacts_of_data hq hS Borel252.A6.borelData_A6 e.toMonoidHom e.surjective
      (isPGroup_ker_of_injective _ e.injective)
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hcov.2
    have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
    let e' := e.trans (Fin257.statedSLEquiv F)
    refine Borel252.borelFacts_of_data hq hS Borel252.L3.borelData_L3 (Fin257.quotMap L e')
      (Fin257.quotMap_surjective L e') ?_
    have hk : (Fin257.quotMap L e').ker = CFSG.pCore 2 ↥L := by
      ext x
      exact Fin257.quotMap_eq_one_iff L e' x
    rw [hk]
    exact CFSG.pCore_isPGroup

end CFSG.QuasithinUnique
