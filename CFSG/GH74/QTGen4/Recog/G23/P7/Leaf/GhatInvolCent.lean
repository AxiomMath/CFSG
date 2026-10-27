module

public import CFSG.GH74.QTGen4.Recog.G23.P7.LeafWrappers
public import CFSG.GH74.QTGen4.Recog.G23.NativeLetters
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.CharacterTheory.Blocks.NormOne
public import CFSG.CharacterTheory.SteinbergBSExceptionalCharacterTools
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.GH74.QTGen4.Recog.G23.P7.TriData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem ghatInvol_card_centralizer_map {A B : Type} [Group A] [Group B] (φ : A ≃* B) (s : A) :
    Nat.card (Subgroup.centralizer ({φ s} : Set B)) =
      Nat.card (Subgroup.centralizer ({s} : Set A)) := by
  have hmap : (Subgroup.centralizer ({s} : Set A)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ s} : Set B) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : g * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      change φ g * φ s = φ s * φ g
      rw [← map_mul, ← map_mul, hg']
    · intro hz
      rw [Subgroup.mem_centralizer_singleton_iff] at hz
      refine ⟨φ.symm z, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz
  rw [← hmap]
  exact Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective

theorem ghatInvol_orderOf_map (y : Ghat) (hy : orderOf y = 2) :
    orderOf (adjointEquivR3 y) = 2 := by
  obtain ⟨h1, h2⟩ := orderOf_eq_prime_iff.mp hy
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, h1, map_one]
  · intro h3
    exact h2 (adjointEquivR3.injective (h3.trans (map_one adjointEquivR3).symm))

section Certified


theorem ghatInvol_card_tH : Nat.card (Subgroup.centralizer ({tH} : Set H3)) = 576 := by
  have hcardH : Nat.card H3 = 4245696 := card_R3
  have hfin : Finite H3 := Nat.finite_of_card_ne_zero (by rw [hcardH]; norm_num)
  have h1 : Nat.card X0H ≤ Nat.card (Subgroup.centralizer ({tH} : Set H3)) :=
    Subgroup.card_le_of_le X0H_le_centralizer
  have h2 := card_centralizer_mul_le (t := tH) orbitElt orbitElt_injective orbitElt_conj
  rw [card_X0H] at h1
  rw [hcardH] at h2
  omega

theorem ghatInvol_conj_R3 {s : H3} (hs : orderOf s = 2) : ∃ g : H3, s = g * tH * g⁻¹ :=
  exists_conj_of_sylow (t := tH) card_R3 card_S2H (fun u hu hu2 => exists_conj_of_mem_S2H u hu hu2) hs

theorem leafGhatInvolCent : LeafGhatInvolCent := by
  intro y hy
  obtain ⟨g, hg⟩ := ghatInvol_conj_R3 (ghatInvol_orderOf_map y hy)
  have hconj := @ghatInvol_card_centralizer_map H3 H3 inferInstance inferInstance (MulAut.conj g) tH
  rw [MulAut.conj_apply] at hconj
  have hgC : Nat.card (Subgroup.centralizer ({adjointEquivR3 y} : Set H3)) = 576 := by
    rw [hg, hconj, ghatInvol_card_tH]
  exact (@ghatInvol_card_centralizer_map Ghat H3 inferInstance inferInstance adjointEquivR3 y).symm.trans
    hgC

end Certified

end CFSG.GH74.QTGen4.Recog.G23.P7
