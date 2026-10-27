module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OuterPlane
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeG2
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.DefChar

section Suzuki

theorem crossCharFamCat_suzuki :
    CrossCharFamCat .suzuki := by
  rintro ⟨d, hv⟩ ⟨m, rfl⟩ p hp hp2 _ D hD hcard H hH hDH
  have hcyc : IsCyclic (MulAut (Cat ⟨.suzuki m, hv⟩) ⧸ innerAut (Cat ⟨.suzuki m, hv⟩)) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 (2 * m + 1)
      (CFSG.LieType.SeitzGeneration.suzukiModel_cat hv)).1.1
  obtain ⟨E, -, hEin, hE, hEc⟩ := exists_inner_plane_of_cyclic hcyc hp D hD hcard
  exact (CFSG.LieType.SeitzGeneration.not_innerPlane_suzuki hv hp hp2 hE hEc hEin).elim

end Suzuki

section Ree


theorem crossCharFamCat_reeG2 : CrossCharFamCat .reeG2 := by
  rintro ⟨d, hv⟩ ⟨m, rfl⟩ p hp hp2 hc D hD hcard H hH hDH
  have hp3 : p ≠ 3 := fun h => hc (by simp [h])
  have hp4 : 3 < p := by
    have := hp.two_le
    omega
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat_G2 hv
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hcycΓ : IsCyclic (MulAut (CFSG.LieType.Ree.ReeTag.G2.reeGamma X m) ⧸
      innerAut (CFSG.LieType.Ree.ReeTag.G2.reeGamma X m)) :=
    isCyclic_outer_of_gen _
      (CFSG.ComponentClassification.LiteratureLocal.SmallRee.exists_eq_conj_mul_frobeniusΓ_pow
        hm1 hX)
  have hcyc := isCyclic_outer_of_mulEquiv e hcycΓ
  obtain ⟨E, -, hEin, hE, hEc⟩ := exists_inner_plane_of_cyclic hcyc hp D hD hcard
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.reeG2 m, hv⟩ →* MulAut _) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv e
      (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
        (CFSG.LieType.Ree.ReeTag.center_reeGamma_G2_eq_bot hX))
  exact (CFSG.LieType.SeitzGeneration.false_of_inner_plane_of_no_plane hinj
    (fun F hF hc' => CFSG.LieType.SeitzGeneration.no_plane_cat_reeG2 hv hp hp4 F hF hc')
    hE hEc hEin).elim

end Ree

section Tits


theorem crossCharFamAt_tits : CrossCharFamAt .tits fun _ p => p ≠ 3 := by
  rintro ⟨d, hv⟩ hd p hp hp2 _ hp3 D hD hcard H hH hDH
  have hd' : d = .tits := hd
  subst hd'
  obtain ⟨hT, hOut⟩ := CFSG.LieType.SeitzGeneration.card_cat_tits_outer hv
  have hcop : Nat.Coprime (Nat.card D)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Cat ⟨.tits, hv⟩))) := by
    rw [hcard, hOut]
    exact Nat.Coprime.pow_left 3 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hin := CFSG.LieType.SeitzGeneration.le_inner_of_coprime_card_outer hcop
  have hdvd : p ^ 3 ∣ 17971200 := by
    rw [← hT, ← hcard]
    exact (Subgroup.card_dvd_of_le hin).trans
      (Subgroup.card_dvd_of_surjective (MonoidHom.rangeRestrict_surjective _))
  exfalso
  have hpd : p ∣ 17971200 := (dvd_pow_self p (by norm_num)).trans hdvd
  by_cases h5 : p = 5
  · subst h5
    norm_num at hdvd
  · refine CFSG.LieType.SeitzGeneration.not_sq_dvd_card_tits_of_ne hp hp2 hp3 h5 ?_
    exact (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans hdvd

end Tits

end CFSG.HardMathSupport.Timmesfeld.CrossChar
