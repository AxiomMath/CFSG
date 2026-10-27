module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4G2D4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4L4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4L5U5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4Sp4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4U4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3L33
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3M11
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3M12
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3PSp43
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3U33
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3D4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5
public import CFSG.ClassicalInvolution.Q3.TA3LeafTwistedG2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.GH74.KGroups CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.CatFactsSmall

theorem NoDatum4.toR {r : ℕ} {F : Type} [Group F] (h : NoDatum4 F) : NoDatum4R r F :=
  fun G _ _ N _ e hC h4 R S t hd _ => h G N e hC h4 R S t hd

theorem noDatum4R_of_noQ16 {r : ℕ} (hr : 4 ≤ r) {F : Type} [Group F]
    (h : ∃ (A : Type) (_ : Group A), EmbedsAut F A ∧ NoQ16 A) : NoDatum4R r F := by
  intro G _ _ N _ ⟨eN⟩ hC _ R S t _ hq
  obtain ⟨A, _, hE, hA⟩ := h
  obtain ⟨f, hf⟩ := hE G N ⟨eN⟩ hC
  obtain ⟨e⟩ := hq
  let ι : QuaternionGroup (2 ^ (r - 2)) →* G :=
    R.subtype.comp ((S : Subgroup R).subtype.comp e.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.symm.injective)
  obtain ⟨x, y, hxy⟩ := exists_q16Pair_of_injective hr ι hι
  exact hA (f x) (f y) (hxy.map f hf)

theorem noDatum4R_of_lie_good {r : ℕ} (hr : 4 ≤ r) {tag : StatedLieTag} {n p f : ℕ} {F : Type}
    [Group F] [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a) (hm : LieModel F tag n p f)
    (hgood : ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup ↥(genFittingFStar Y)],
      (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → LieModel ↥(genFittingFStar Y) tag n p f →
      ∀ {R : Subgroup Y} {S : Sylow 2 R} {t : Y}, TightDatum R S t → GoodThreeElement R t) :
    NoDatum4R r F := by
  intro G _ _ N _ ⟨e⟩ hC _ R S t hd hq
  haveI : IsSimpleGroup ↥N := e.isSimpleGroup
  have hnabN : ∃ a b : ↥N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hF : genFittingFStar G = N := genFittingFStar_eq_of_normal_simple N hnabN hC
  let e' : ↥(genFittingFStar G) ≃* F := (MulEquiv.subgroupCongr hF).trans e
  haveI : IsSimpleGroup ↥(genFittingFStar G) := e'.isSimpleGroup
  have hnab' : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e'.symm a, e'.symm b, fun h => hab (by simpa using congrArg e' h)⟩
  exact not_goodThreeElement_of_four_le hr hd hq
    (hgood G hnab' (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e'.symm hm) hd)

section Vac


theorem noDatumOtherR_holds (r : ℕ) : NoDatumOtherR r := by
  intro hr F _ _ hnab hOF
  rcases hOF with (h | h | h | h | h | h | h | h | h | h | h | h) | hex
  · obtain ⟨p, f, hp, hp2, hf, hm⟩ := h
    by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
      exact noDatum4R_of_lie_good hr hnab hm fun Y _ _ _ hnab' hm' R S t hd =>
        good_g23 hnab' hm' hd
    · exact (noDatum4_g2Ne3 F ⟨p, f, hp, hp2, hf, h3, hm⟩).toR
  · obtain ⟨p, f, hp, hp2, hf, hm⟩ := h
    by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
      exact noDatum4R_of_lie_good hr hnab hm fun Y _ _ _ hnab' hm' R S t hd =>
        good_d43 hnab' hm' hd
    · exact (noDatum4_d4Ne3 F ⟨p, f, hp, hp2, hf, h3, hm⟩).toR
  · obtain ⟨p, f, hp, hp2, hf, hm⟩ := h
    by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
      refine noDatum4R_of_noQ16 hr ?_
      obtain ⟨e⟩ := PSp43.equiv_of_lieModel hm
      obtain ⟨M, -, hA⟩ := PSp43.exists_model e
      exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact psp43_noQ16⟩
    · exact (noDatum4_psp4Ne3 F ⟨p, f, hp, hp2, hf, h3, hm⟩).toR
  · exact (NoDatum4.of_nobq (noDatum_smallTwistedG2 F h)).toR
  · obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := h
    by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
      exact (noDatum4_l43 F hm).toR
    · exact (noDatum4_l4Ne3 F ⟨p, f, hp, hp2, hf, hc, h3, hm⟩).toR
  · obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := h
    by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
      exact (noDatum4_u43 F hm).toR
    · exact (noDatum4_u4Ne3 F ⟨p, f, hp, hp2, hf, hc, h3, hm⟩).toR
  · obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := h
    by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
      exact noDatum4R_of_lie_good hr hnab hm fun Y _ _ _ hnab' hm' R S t hd =>
        good_l53 hnab' hm' hd
    · exact (noDatum4_l5Ne3 F ⟨p, f, hp, hp2, hf, hc, h3, hm⟩).toR
  · exact (noDatum4_u5 F h).toR
  · refine noDatum4R_of_noQ16 hr ?_
    obtain ⟨e⟩ := h
    exact ⟨↥autModel, inferInstance,
      embedsAut_of_exactModel GH74.Generic.S45.EvSpor.m12_smallAutModel (e.trans m12EquivD),
      m12_noQ16⟩
  · refine noDatum4R_of_noQ16 hr ?_
    obtain ⟨M, -, hA⟩ := M11.autModel h
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact m11_noQ16⟩
  · refine noDatum4R_of_noQ16 hr ?_
    obtain ⟨e⟩ := L33.equiv_of_lieModel h
    obtain ⟨M, -, hA⟩ := L33.autModel e
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact l33_noQ16⟩
  · refine noDatum4R_of_noQ16 hr ?_
    obtain ⟨e⟩ := U33.equiv_of_lieModel h
    obtain ⟨M, -, hA⟩ := U33.autModel e
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact u33_noQ16⟩
  · exact (NoDatum4.of_nobq
      ((Nobq.smallNoDatum_of_dvd Nobq.card_outer_Ly_dvd_two).noDatum F hex)).toR

end Vac

end CFSG.CGT.PushingUpLit.SolKNA.R4
