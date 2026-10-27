module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Sp6Seven
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Char2Rank3
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUnique
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
public import Certificates.Certificate725107

public section

namespace CFSG.SectionRank.QTK.Insp443.Sp6

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.KGC31 CFSG.Sporadic.Th CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Co3 CFSG.RankThree.PerfectCover


theorem exists_x7_of_cert : ∃ x : co3X36, Rep 36 x7T (x : Perm (Fin 36)) ∧ orderOf x = 7 :=
  exists_x7 Certificates.certificate725105

theorem conclK_seven_of_cert {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK) {x : co3X36}
    (hxT : Rep 36 x7T (x : Perm (Fin 36))) (hx : orderOf x = 7) {y t : co3X36} (hy : y ∈ L)
    (hyx : y ∈ Subgroup.zpowers x) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) :
    ConclK co3X36 L V MK :=
  conclK_seven Certificates.certificate725105 Certificates.certificate725107 h hxT hx
    hy hyx ht hyt

theorem conclK_sp6 {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK) :
    ConclK co3X36 L V MK := by
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨p, hp, hp5, y, hy, hyk, t, ht, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  have hpd : p ∣ Nat.card co3X36 := by
    by_contra hpd
    apply hyt
    rw [eq_one_of_pow_of_not_dvd hp hpd hyk, one_mul, inv_one, mul_one]
  have hcard := card_co3X36
  rw [hcard] at hpd
  rcases Alt.prime_eq_of_dvd (a := 9) (b := 4) hp hp5 (by norm_num; exact hpd) with rfl | rfl
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x, hxT, hx⟩ := exists_x5_of_cert
    obtain ⟨σ, m, -, t₁, ht₁, hxL, hxt⟩ :=
      Alt.exists_conj_of_sylow hx (by rw [hcard]; norm_num) hy hyk ht hyt
    exact ConclK.of_map_mulEquiv σ h.elemAbelian h.le_normalizer
      (conclK_five_of_cert (h.map_mulEquiv σ) hxT hx hxL (Subgroup.npow_mem_zpowers x m) ht₁ hxt)
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨x, hxT, hx⟩ := exists_x7_of_cert
    obtain ⟨σ, m, -, t₁, ht₁, hxL, hxt⟩ :=
      Alt.exists_conj_of_sylow hx (by rw [hcard]; norm_num) hy hyk ht hyt
    exact ConclK.of_map_mulEquiv σ h.elemAbelian h.le_normalizer
      (conclK_seven_of_cert (h.map_mulEquiv σ) hxT hx hxL (Subgroup.npow_mem_zpowers x m) ht₁
        hxt)


theorem card_hopfMultiplier_co3X36 : Nat.card (hopfMultiplier ↥co3X36) = 2 := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.EvenSmallLie.SympSix.multiplier_PSp_three_two_one ↥co3X36
    (Or.inl ⟨by decide, co3X36_classicalModel⟩)
  rw [← Nat.card_congr (hopfMultiplierEquivGriess ↥co3X36).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]

theorem forK_Sp6 : ForK (fun S _ => StatedClassicalModel S .PSp 3 2 1) := by
  refine ForK.mono (fun S _ hS => ?_) (forK_of_kConfig (X := ↥co3X36)
    (dvd_of_eq card_hopfMultiplier_co3X36) fun _ _ _ h => conclK_sp6 h)
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec21.nonempty_mulEquiv_H6_of_stated hS
  exact ⟨e.trans co3Sp6Equiv⟩

theorem for_Sp6 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => StatedClassicalModel S .PSp 3 2 1) :=
  For.of_forK h37 h38 h39 forK_Sp6

theorem for_itemChar2Rank3_of_L52 (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hL5 : For (fun S _ => StatedClassicalModel S .PSL 5 2 1)) : For ItemChar2Rank3 :=
  for_itemChar2Rank3_of h37 h38 h39 hL5 (for_Sp6 h37 h38 h39)

end CFSG.SectionRank.QTK.Insp443.Sp6

end
