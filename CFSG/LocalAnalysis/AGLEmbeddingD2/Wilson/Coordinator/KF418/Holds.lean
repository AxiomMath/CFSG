module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.KF418Excl

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.AGLEmbeddingD2.Wilson.Proving (KF418Excl kF418Excl_of_card)

theorem kF418Excl_carrier_of_card {s : TauCeti.SporadicName} {N : ℕ}
    (hN : Nat.card (NativeSporadic.Carrier s) = N) (hN0 : N ≠ 0)
    (h : ¬ 3 ^ 4 ∣ N ∨ ¬ 7 ∣ N) : KF418Excl (NativeSporadic.Carrier s) := by
  have : Finite (NativeSporadic.Carrier s) := Nat.finite_of_card_ne_zero (hN ▸ hN0)
  exact kF418Excl_of_card (hN ▸ h)


theorem kF418Excl_carrier {s : TauCeti.SporadicName}
    (hs : s ∈ Sec4.sporadics46 ∨ s ∈ Sec4.sporadicCovers46) :
    KF418Excl (NativeSporadic.Carrier s) := by
  simp only [Sec4.sporadics46, Sec4.sporadicCovers46, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.Schreier.m11_card (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.Schreier.m12_card (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.Schreier.m22_card (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.Schreier.m23_card (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.Schreier.m24_card (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.J1.card_J1 (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.J2.card_J2 (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.J3.card_J3 (by norm_num) (Or.inr (by norm_num))
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.J4.card_J4 (by norm_num) (by norm_num)
  · exact CFSG.AGLEmbeddingD2.Wilson.Proving.kF418Excl_mcl
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.HS.card_HS (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.He.fam_he_order.1 (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.Ru.card_Ru (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.Schreier.m22_card (by norm_num) (by norm_num)
  · exact kF418Excl_carrier_of_card CFSG.Sporadic.J3.card_J3 (by norm_num) (Or.inr (by norm_num))
  · exact CFSG.AGLEmbeddingD2.Wilson.Proving.kF418Excl_mcl
  · exact CFSG.AGLEmbeddingD2.Wilson.Proving.kF418Excl_on

theorem kF418Excl_quot_of_list46FourFive {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hl : Sec4.IsList46Four X ∨ Sec4.IsList46Five X) : KF418Excl (X ⧸ Subgroup.center X) := by
  rcases quotCenter_model_of_list46FourFive hq hl with ⟨n, -, hn, ⟨e⟩⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact CFSG.AGLEmbeddingD2.Wilson.Proving.KF418Excl.of_mulEquiv e
      (CFSG.AGLEmbeddingD2.Wilson.Proving.kF418Excl_alternatingGroup hn)
  · exact CFSG.AGLEmbeddingD2.Wilson.Proving.KF418Excl.of_mulEquiv e (kF418Excl_carrier hs)

theorem kF418ModelAltSpor_holds : KF418ModelAltSpor :=
  kF418ModelAltSpor_of_excl fun _ _ _ hq hl => kF418Excl_quot_of_list46FourFive hq hl

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
