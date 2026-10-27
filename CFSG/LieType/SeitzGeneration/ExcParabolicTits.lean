module

public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.Sporadic.Schreier.TitsOuterTwo
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint TauCeti

theorem not_sq_dvd_card_tits {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) :
    ¬ p ^ 2 ∣ 17971200 := by
  intro h
  have hpd : p ∣ 17971200 := (dvd_pow_self p two_ne_zero).trans h
  have hN : (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
  rw [hN] at hpd h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h4 | h4
    · rcases (Nat.Prime.dvd_mul hp).1 h4 with h6 | h6
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h6))
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h6))
    · exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h4))
  · have h13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h1
    subst h13
    norm_num at h

section Model


theorem card_cat_tits (hv : LieTypeIndex.tits.Valid) :
    Nat.card (Cat ⟨.tits, hv⟩) = 17971200 := by
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  have hmodel : ReeTitsModel (Cat ⟨.tits, hv⟩) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
      ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
        (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
        ⟨e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩
  exact (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound _ 2 1 hmodel).1

theorem seitzExcParabolicFor_tits : SeitzExcParabolicFor IsTitsIndex := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hd, -⟩
  subst hd
  exfalso
  have hT := card_cat_tits hv
  have : Finite (Cat ⟨.tits, hv⟩) := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have h3 : p ≠ 3 := fun h => hex (Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)
  have h5 : p ≠ 5 := fun h => hex (Or.inr ⟨h, Or.inl rfl⟩)
  refine not_sq_dvd_card_tits hp hp2 h3 h5 ?_
  rw [← hT, ← hc]
  exact (Subgroup.card_dvd_of_le hin).trans
    (Subgroup.card_dvd_of_surjective (MonoidHom.rangeRestrict_surjective _))

end Model

end CFSG.LieType.SeitzGeneration
