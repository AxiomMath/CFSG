module

public import CFSG.ClassicalInvolution.Q3.TL3T5
public import CFSG.ClassicalInvolution.Q3.TL3C11

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


@[expose] def TightIndepLeaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      (∀ M N : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        TC.ThinAt (CoreAssembly.conjClass (tightCore R)) M N) →
      ∀ M ∈ CoreAssembly.conjClass (tightCore R),
        TC.Thin.Indep (CoreAssembly.conjClass (tightCore R)) M

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightLargeHyp.card_core (hL : TightLargeHyp n Y R S t) (hO : TightOddCent t) :
    Nat.card ↥(tightCore R) = 8 := by
  have h2R : IsPGroup 2 R := hL.datum.isPGroup_of_oddCent hO
  rw [tightCore_eq_self_of_isPGroup h2R]
  have htop : (S : Subgroup R) = ⊤ := (S.is_maximal' (h2R.to_subgroup ⊤) le_top).symm
  have e : Nat.card ↥(S : Subgroup R) = Nat.card (QuaternionGroup 2) :=
    Nat.card_congr hL.cls.1.some.toEquiv
  rw [htop, Subgroup.card_top] at e
  rw [e, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem TightLargeHyp.thinStd (hL : TightLargeHyp n Y R S t) (hO : TightOddCent t)
    (hconn : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hsep : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) :
    TC.Thin.ThinStd (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  have hd := hL.datum
  have hcard := hL.card_core hO
  refine ⟨hd.hypOmegaGen, hd.isPGroup_member hO, ?_, ?_, hd.aEmpty,
    CoreAssembly.mem_conjClass_self _, fun J hJ => hJ, ?_, hconn, hsep⟩
  · intro J hJ
    obtain ⟨g, rfl⟩ := hJ
    show Nat.card ↥(conjSub g (tightCore R)) = 8
    exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hcard
  · intro J hJ u hu
    exact (hd.normalizer_eq_centralizer_member hJ hu).ge
  · rw [iSup_conjClass_eq]
    exact hL.cls.2.1

theorem tightThinLeaf_of_indep (h : TightIndepLeaf n) : TightThinLeaf n := by
  intro Y _ _ R S t hL hO hconn hsep hall
  have hS := hL.thinStd hO hconn hsep
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨J₀, hJ₀⟩ := hL.datum.nonempty_omegaNbr_of_not_dEdgeless hL.edge
  obtain ⟨P, hP⟩ := exists_isMaxOrb (A := TC.nbrAdj (CoreAssembly.conjClass (tightCore R)))
    (⟨hK, hJ₀⟩ : TC.nbrAdj _ (tightCore R) J₀)
  obtain ⟨⟨J, hKJ, hJP⟩, -⟩ := id hP
  have hmax : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J :=
    ⟨hKJ, by rw [hJP]; exact hP⟩
  exact hS.false_of_indep hall (h Y R S t hL hO hconn hsep hall) hmax

theorem tightLargeLiftS_of_leaves' (hodd : ∀ n, TightOddLeaf n) (hconn : ∀ n, TightConnLeaf n)
    (hsep : ∀ n, TightSepLeaf n) (hind : ∀ n, TightIndepLeaf n) (hE3 : ∀ n, TightE3Leaf n) :
    ∀ n, TightLargeLiftS n :=
  tightLargeLiftS_of_leaves hodd hconn hsep (fun n => tightThinLeaf_of_indep (hind n)) hE3

end Cit3

end CFSG.ClassicalInvolution.Q3
