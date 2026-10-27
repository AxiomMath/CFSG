module

public import CFSG.CGT.PushingUpLit.T2K.FiveFour
public import CFSG.CGT.PushingUpLit.T2K.FiveA
public import CFSG.CGT.PushingUpLit.T2K.FourSevenB

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open CFSG.Assembly.RankThreeEven (projSL projSp)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Sec4 (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) : Prop where
  hyp : T2Hyp G L M n
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  sylowG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  noG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4
  noL3 : ¬ Nonempty (G ≃* projSL 3 (GaloisField 2 n))
  noSp4 : ¬ Nonempty (G ≃* projSp 2 (GaloisField 2 n))
  S_elem : CFSG.Open.IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))
  N_T : Subgroup.normalizer (T : Set G) ≤ M
  N_J : Subgroup.normalizer (thompsonJ T : Set G) ≤ M

@[expose] def Print55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ), Sec4 G L M T n →
    T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → ∀ N R : Subgroup G, Sit54 G M T N R → False

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}

theorem sec4 (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple) (hE5 : Aschbacher78One)
    (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25) (hCamp : Print47Campbell)
    (hFinal : Print47Final) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hnG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4)
    (hnL3 : ¬ Nonempty (G ≃* projSL 3 (GaloisField 2 n)))
    (hnSp4 : ¬ Nonempty (G ≃* projSp 2 (GaloisField 2 n))) : Sec4 G L M T n := by
  obtain ⟨-, hS, -⟩ := h.four_four hE1 hE8 h25 hT
  have h47 := h.four_seven hE1 hT hE8 h25 hE5 hnG4 hCamp hFinal
  exact ⟨h, hT, isSylowOf_top hT h47, hnG4, hnL3, hnSp4, hS, h.four_six hE1 hE5 hT hnG4, h47⟩

theorem five_one (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hE2 : SolomonAlternatingBlockK) (hE5 : Aschbacher78One) (hE8 : SolomonTimmesfeldTight)
    (h25 : Asc76Lemma25) (hCamp : Print47Campbell) (hFinal : Print47Final)
    (h53 : Print53) (h55 : Print55) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hnG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4)
    (hnL3 : ¬ Nonempty (G ≃* projSL 3 (GaloisField 2 n)))
    (hnSp4 : ¬ Nonempty (G ≃* projSp 2 (GaloisField 2 n))) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hs := h.sec4 hE1 hE5 hE8 h25 hCamp hFinal hT hnG4 hnL3 hnSp4
  by_contra hne
  obtain ⟨N, hN, hTN, hNM⟩ := h.five_three hE1 hE2 hE5 h53 hT hs.sylowG hnG4
  obtain ⟨R, hR⟩ := h.sit54 hE1 hT hs.sylowG hs.N_J hne hN hTN hNM
  exact h55 G L M T n hs hne N R hR

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
