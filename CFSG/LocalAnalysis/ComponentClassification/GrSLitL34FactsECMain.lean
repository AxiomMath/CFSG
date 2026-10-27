module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECMult
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECExc
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECO82
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECU42
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECL34
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Reduce

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.ComponentClassification.HarrisLit

theorem evenLieOuterCoverFact_of_multipliers
    (hGA : TBLit.GriessMultipliersAllModels) : N36.EvenLieOuterCoverFact := by
  intro G _ _ hq hO hZ t n f hL τ hτ hτo p m _ hp2 _ h16 K hK _ hKL
  have : Group.IsPerfect G := hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (N36.center_isPGroup hO)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hZ (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
  have h2 : 2 ∣ Nat.card (center G) := hk ▸ dvd_pow_self 2 hk0
  have hKZ := N36.inf_center_eq_bot hO hKL
  have hLbar : Blueprint.LieModel (↥(K.map (QuotientGroup.mk' (center G))) ⧸
      pPrimeCore 2 ↥(K.map (QuotientGroup.mk' (center G)))) .PSL 2 p m := by
    obtain ⟨e⟩ := N36.nonempty_equiv_bar hKZ
    exact GSThmB.OddQuot.lieModel_of_equiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e) hKL
  have key : NoOddPSL2 (G ⧸ center G) → False := fun hY =>
    false_of_noOddPSL2 hY (N36.orderOf_quotAut_eq_two hq hτ)
      (fun h => hτo ((N36.quotAut_mem_innAut_iff τ).mp h)) (N36.isTwoComponentIn_bar hK hKZ)
      hp2 hLbar
  have h168 : 168 ≤ Nat.card K :=
    (HarrisLit.Hin.le_card_of_lieModel_psl2_sixteen hp2 h16 hKL).trans
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))
  have h12 := twelve_of_even_center hGA hq hL h2
  unfold IsTwelve at h12
  rcases h12 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact (key (noOddPSL2_L24 hL)).elim
  · exact (key (noOddPSL2_L32 hL)).elim
  · exact Or.inr ((SymmetricLocal.lie_model_linear_four_two_iff _).mp hL)
  · exfalso
    have hZ2 : Nat.card (center G) = 2 := Nat.dvd_antisymm (card_center_dvd_U42 hGA hq hL) h2
    have := isSimpleGroup_of_lieModel_psl2 hKL
    exact false_of_U42_cover hq hZ2 hL hKZ (nonabelian_of_lieModel_psl2 hKL)
  · exact (key (noOddPSL2_Sp62 hL)).elim
  · exact (key (noOddPSL2_G2 hL)).elim
  · exact (key (noOddPSL2_F4 hL)).elim
  · exact (key (noOddPSL2_O82 hL)).elim
  · exact (key (noOddPSL2_U62 hL)).elim
  · exact (key (noOddPSL2_Sz8 hL)).elim
  · exact (key (noOddPSL2_twistedE6 hL)).elim
  · refine Or.inl ⟨hL, ?_⟩
    have hd := card_center_dvd_L34 hGA hq hL
    rw [hk] at hd ⊢
    have hk4 : k ≤ 4 := by
      by_contra h5
      have h32 : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      exact absurd (h32.trans hd) (by norm_num)
    rcases Nat.lt_or_ge k 4 with hk3 | hk4'
    · calc 2 ^ k < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) hk3
        _ = 16 := by norm_num
    · exfalso
      obtain rfl : k = 4 := by omega
      exact false_of_L34_sixteen hq hL (by rw [hk]; norm_num) hτ hτo hK.1 hKZ h168

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover
