module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutType
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Sylow
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClAltSix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

section A6

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti
open CFSG.RankThree.PartTwo

theorem typeOrd_isA6 : TypeOrd S8.isA6 360 := fun {X} _ hX => by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4.nonempty_alt6_of_catalogIs_isA6 hX
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem lieSOutOrdW_a6 : LieSOutOrdW 360 where
  three_dvd := by norm_num
  not_dvd_216 := by norm_num
  not_dvd_12096 := by norm_num
  ne_17971200 := by norm_num
  ne_triD4 := fun Q hQ => by
    rcases (by omega : Q = 2 ∨ Q = 3 ∨ 4 ≤ Q) with rfl | rfl | h4
    · norm_num
    · norm_num
    · exact ne_of_lt (lt_of_lt_of_le (by norm_num) (lieSOut_triD4_order_ge h4))
  ne_g2 := fun Q hQ => by
    rcases (by omega : Q = 4 ∨ 5 ≤ Q) with rfl | h5
    · norm_num
    · exact ne_of_lt (lt_of_lt_of_le (by norm_num) (lieSOut_g2_order_ge h5))
  ne_sl3 := KFacts.KS14.forall_of_forall_lt (B := 8) (by norm_num) (by norm_num)
    (by decide +kernel)
  ne_su3 := KFacts.KS14.forall_of_forall_lt (B := 8) (by norm_num) (by norm_num)
    (by decide +kernel)

section Cert


theorem not_lieModel_two_of_isA6 {X : Type} [Group X] (hX : catalogIs X S8.isA6)
    {t : StatedLieTag} {n g : ℕ} (hm : Blueprint.LieModel X t n 2 g) : False := by
  have h1 := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hm
  rw [typeOrd_isA6 hX] at h1
  exact CFSG.StandardType.ClNonsplit.evenLieOrder_ne_three_sixty_of_admissible
    (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hm) h1.symm

theorem lieSOutTypeW_a6 : LieSOutTypeW S8.isA6 2 1 360 where
  card_eq := typeOrd_isA6
  det := fun {X} _ hX _ _ _ hm => (not_lieModel_two_of_isA6 hX hm).elim
  ord := lieSOutOrdW_a6
  at360 := fun _ => ⟨rfl, rfl⟩

end Cert

end A6

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
