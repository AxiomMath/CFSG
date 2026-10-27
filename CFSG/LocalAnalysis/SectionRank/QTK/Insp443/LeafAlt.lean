module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.AltOrbit
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.Alternating.Multipliers.Main
public import Certificates.Certificate725103
public import Certificates.Certificate725104

public section

namespace CFSG.SectionRank.QTK.Insp443.Alt

open CFSG.Quasithin

theorem prime_eq_of_dvd {p a b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 2 ^ a * 3 ^ b * 5 * 7) :
    p = 5 ∨ p = 7 := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)

theorem card_A8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem card_A9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem conclK_A8 {L V MK : Subgroup (alternatingGroup (Fin 8))}
    (h : KConfig (alternatingGroup (Fin 8)) L V MK) : ConclK (alternatingGroup (Fin 8)) L V MK :=
  conclK_of_altProp (altProp_of_chk Certificates.certificate725103) (by norm_num)
    (fun _ hp hp5 hd => prime_eq_of_dvd (a := 6) (b := 2) hp hp5 (by rw [card_A8] at hd; exact hd))
    (by rw [card_A8]; norm_num) (by rw [card_A8]; norm_num) h

theorem conclK_A9 {L V MK : Subgroup (alternatingGroup (Fin 9))}
    (h : KConfig (alternatingGroup (Fin 9)) L V MK) : ConclK (alternatingGroup (Fin 9)) L V MK :=
  conclK_of_altProp (altProp_of_chk Certificates.certificate725104) le_rfl
    (fun _ hp hp5 hd => prime_eq_of_dvd (a := 6) (b := 4) hp hp5 (by rw [card_A9] at hd; exact hd))
    (by rw [card_A9]; norm_num) (by rw [card_A9]; norm_num) h

theorem forK_A8 :
    ForK (fun S _ => Nonempty (S ≃* alternatingGroup (Fin 8))) :=
  forK_of_kConfig
    (dvd_of_eq (CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num)))
    (fun _ _ _ h => conclK_A8 h)

theorem forK_A9 :
    ForK (fun S _ => Nonempty (S ≃* alternatingGroup (Fin 9))) :=
  forK_of_kConfig
    (dvd_of_eq (CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num)))
    (fun _ _ _ h => conclK_A9 h)

theorem for_A8 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : For (fun S _ => Nonempty (S ≃* alternatingGroup (Fin 8))) :=
  For.of_forK h37 h38 h39 forK_A8

theorem for_A9 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : For (fun S _ => Nonempty (S ≃* alternatingGroup (Fin 9))) :=
  For.of_forK h37 h38 h39 forK_A9

end CFSG.SectionRank.QTK.Insp443.Alt

end
