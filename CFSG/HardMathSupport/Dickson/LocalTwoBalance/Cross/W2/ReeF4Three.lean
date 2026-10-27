module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux.Faithful

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LieType.Ree
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux


theorem reeF4InnerThreeBalance_holds : ReeF4InnerThreeBalance := by
  intro a K _ _ _ ha hK E hEin hE hEc H hH
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  have hne : ∃ x ∈ E, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hall
    rw [this, Subgroup.card_bot] at hEc
    norm_num at hEc
  refine localDeltaIn_eq_bot_of_layers_faithful Nat.prime_three hinj hH hne ?_
  intro g hg _ hlayers
  obtain ⟨x, hxE, hx1⟩ := hne
  obtain ⟨y, rfl⟩ := hEin hxE
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hy3 : orderOf y = 3 := by
    refine orderOf_eq_prime ?_ hy1
    apply hinj
    rw [map_pow, hE.2 _ hxE, map_one]
  obtain ⟨e⟩ := reeGamma_centralizer_su3 hK hy3
  have hK' := card_galoisField_su3 a
  have hlayer : IsPLayer 3 E (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) := by
    refine ⟨MulAut.conj y, hxE, hx1, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 ht
      change y * t * y⁻¹ = t
      rw [← h1]
      group
    · intro f hf t ht
      have hfC : f ∈ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) := by
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have h1 : y * f * y⁻¹ = f := hf
        calc f * y = y * f * y⁻¹ * y := by rw [h1]
          _ = y * f := by group
      exact (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))).mul_mem
        ((Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))).mul_mem hfC ht)
        ((Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))).inv_mem hfC)
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (su3_isQuasisimple (by omega) hK')
    · intro hc
      have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) := by
        rw [Nat.card_congr e.toEquiv]
        exact three_dvd_card_su3 rfl hK'
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc h3
  exact eq_one_of_fix_centralizer ha hK hy3 g hg (hlayers _ hlayer)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
