module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.CGT.Higman76.Quotient
import CFSG.CGT.Higman76.SylowD8
import CFSG.CharacterTheory.Wreathed.InvolutionInducedCharactersSupport
import CFSG.CharacterTheory.Semidihedral.ParameterFiveGeneration
import CFSG.Walter.W67.W1Prop24B
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.Higman76

open Subgroup CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

section ASeven


private theorem quotient_conj_a7 (O : Subgroup G) [O.Normal]
    (hOodd : Odd (Nat.card O)) {a b : G}
    (ha : orderOf a = 2) (hzord : orderOf (a * b) = 2)
    (e7 : Nonempty (G ⧸ O ≃* alternatingGroup (Fin 7))) :
    IsConj ((QuotientGroup.mk' O) a) ((QuotientGroup.mk' O) (a * b)) := by
  classical
  let f : G →* G ⧸ O := QuotientGroup.mk' O
  have hfa : orderOf (f a) = 2 :=
    CFSG.Wreathed.InvolutionInducedCharacters.orderOf_mk_eq_two O hOodd ha
  have hfz : orderOf (f (a * b)) = 2 :=
    CFSG.Wreathed.InvolutionInducedCharacters.orderOf_mk_eq_two O hOodd hzord
  obtain ⟨e7⟩ := e7
  have hI7a : BenderSuzuki.PFAppendixIII.IsInvolution (e7 (f a)) :=
    CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two
      (by rw [MulEquiv.orderOf_eq, hfa])
  have hI7z : BenderSuzuki.PFAppendixIII.IsInvolution (e7 (f (a * b))) :=
    CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two
      (by rw [MulEquiv.orderOf_eq, hfz])
  obtain ⟨g, hg⟩ :=
    CFSG.GorensteinWalter.aSeven_involutions_conjugate (e7 (f a)) (e7 (f (a * b))) hI7a hI7z
  refine isConj_iff.mpr ⟨e7.symm g, ?_⟩
  apply e7.injective
  simpa [f] using hg

private theorem not_a7_quotient {a b : G}
    (ha : orderOf a = 2) (hzord : orderOf (a * b) = 2)
    (hzconj : ¬ IsConj a (a * b))
    (e7 : Nonempty (G ⧸ CFSG.pPrimeCore 2 G ≃* alternatingGroup (Fin 7))) : False := by
  classical
  let O : Subgroup G := CFSG.pPrimeCore 2 G
  haveI hOn : O.Normal := CFSG.pPrimeCore_normal
  have hOodd : Odd (Nat.card O) := by
    dsimp [O]
    exact CFSG.Walter.W67.odd_card_pPrimeCore G
  have ha_inv : BenderSuzuki.PFAppendixIII.IsInvolution a :=
    CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two ha
  have hz_inv : BenderSuzuki.PFAppendixIII.IsInvolution (a * b) :=
    CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two hzord
  have hQconj : IsConj ((QuotientGroup.mk' O) a) ((QuotientGroup.mk' O) (a * b)) :=
    quotient_conj_a7 O hOodd ha hzord e7
  exact hzconj (isConj_of_quotient_isConj (O := O) hOodd ha_inv hz_inv hQconj)

end ASeven

section Certified


theorem higman (S : Sylow 2 G) {a : G} (ha : orderOf a = 2)
    (haS : a ∈ S) (hgen : Subgroup.normalClosure {a} = ⊤)
    (h2 : {x | x ∈ S ∧ IsConj a x}.ncard = 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) ∧
      Nonempty (G ⧸ CFSG.pPrimeCore 2 G ≃* CFSG.GorensteinWalter.PGL2 K) := by
  classical
  obtain ⟨b, hne_ba, hbS, hab, hb, hcl⟩ := exists_conj_pair S ha haS h2
  have hne : a ≠ b := hne_ba.symm
  have ha2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two ha).symm
  have hb2 : b * b = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two hb).symm
  have ha1 : a ≠ 1 := by intro h; rw [h] at ha; simp at ha
  have hb1 : b ≠ 1 := by intro h; rw [h] at hb; simp at hb
  have hcomm : a * b = b * a := mul_comm_of_conj_pair S hb haS hbS hne hcl
  obtain ⟨-, -, hzconj, hzord⟩ := mul_not_conj S ha hb haS hbS hne hcomm hcl
  obtain ⟨eS⟩ := sylow_dihedral S ha haS hgen h2
  have hScard : Nat.card (S : Subgroup G) = 8 := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have hcardV : Nat.card (fourGroup a b) = 4 := fourGroup_card ha2 hb2 hcomm ha1 hb1 hne
  have hD : CFSG.GorensteinWalter.HasDihedralSylowTwo G := by
    intro T
    exact ⟨2, by norm_num, ⟨(Sylow.equiv S T).symm.trans eS⟩⟩
  have hDG : CFSG.GorensteinWalter.IsDGroup G :=
    CFSG.GorensteinWalter.gorensteinWalter G hD
  rcases hDG with ⟨_, hQ⟩ | ⟨_, e7⟩ | ⟨_, K, hKpp, L, hLn, hLidx, hLmodel⟩
  · exact (not_isPGroup_quotient S haS hScard hcardV hcl hgen hQ).elim
  · exact (not_a7_quotient ha hzord hzconj e7).elim
  · rcases hLmodel with hLmodel | hLmodel
    · obtain ⟨eP⟩ := hLmodel
      exact (not_psl2_quotient ha hzord hzconj hgen K hKpp L hLn hLidx eP).elim
    · obtain ⟨eP⟩ := hLmodel
      exact pgl2_branch S ha hgen hScard K hKpp L hLn hLidx eP

end Certified

end CFSG.CGT.Higman76
