module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecConj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecEdge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

section Targets

@[expose] def TwinEdgeExitOddFree (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → tightCore R = R →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ u : Y, IsUniqueInvolution J u → u ≠ t →
        ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
          (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
          (Sb : Sylow 2 ↥(tightCore (secR R u))),
          (TightEx (SecQ R u) (tightCore (secR R u)) Sb
              (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) ∨
            TwinE4 (SecQ R u)) →
          TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
              (⟨⟨t, htu⟩, ht⟩ : secH R u)) ∨
            SecOddFree R u (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
              (⟨⟨t, htu⟩, ht⟩ : secH R u))

@[expose] def TwinSecAOddFree (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → tightCore R = R →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ u : Y, IsUniqueInvolution J u → u ≠ t →
        ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
          (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
          AEmpty (CoreAssembly.conjClass (tightCore (secR R u))) (tightCore (secR R u)) ∨
            TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
              (⟨⟨t, htu⟩, ht⟩ : secH R u)) ∨
            SecOddFree R u (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
              (⟨⟨t, htu⟩, ht⟩ : secH R u))

theorem twinSecAOddFree_of_secA {n : ℕ} (h : TwinSecA n) : TwinSecAOddFree n :=
  fun Y _ _ R S t hh hRc J hJ u hu hut htu ht =>
    (h Y R S t hh hRc J hJ u hu hut htu ht).elim Or.inl (fun h2 => Or.inr (Or.inl h2))

end Targets

section Edge

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {n : ℕ}

theorem classicalOrQuietOrOddFree_of_edge_twin (hex : TwinEdgeExitOddFree n)
    (hA : TwinSecAOddFree n) (h : TwinCoreHyp n Y R S t) (hRc : tightCore R = R)
    (hZ : Subgroup.center Y = ⊥) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (hut : u ≠ t)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) :
    TL4.ClassicalOrQuiet u t htu ∨ MovedOddFreeAt u t htu := by
  obtain ⟨hu2, -, hBR⟩ := edge_involution h.datum hRc h.hyp hJ hu hut
  exact classicalOrQuietOrOddFree_of_cent h hRc hZ hu2 hu.ne_one hBR htu
    (fun ht Sb hexit => hex Y R S t h hRc J hJ u hu hut htu ht Sb hexit)
    (fun ht => hA Y R S t h hRc J hJ u hu hut htu ht)

theorem autOddFreeOn_of_edges_oddFree (hex : TwinEdgeExitOddFree n) (hA : TwinSecAOddFree n)
    (h : TwinCoreHyp n Y R S t) (hRc : tightCore R = R) (hZ : Subgroup.center Y = ⊥) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M,
      ∀ zM zN : Y, IsUniqueInvolution M zM → IsUniqueInvolution N zN → zM ≠ zN →
        ∀ hcomm : zM ∈ Subgroup.centralizer ({zN} : Set Y),
        ∀ L : Subgroup (OddQuot zN), CFSG.IsComponent L →
          oddQuotMk zN ⟨zM, hcomm⟩ ∈ Subgroup.normalizer (L : Set (OddQuot zN)) →
          (∃ y ∈ L, oddQuotMk zN ⟨zM, hcomm⟩ * y ≠ y * oddQuotMk zN ⟨zM, hcomm⟩) →
          Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk zN ⟨zM, hcomm⟩)) := by
  rintro M ⟨g, hg⟩ N hN zM zN hzM hzN hne hcomm L hL hLN hm
  have hMg : conjSub g (tightCore R) = M := hg
  obtain ⟨S', hh'⟩ := twinCoreHyp_conj h g
  have hzM' : IsUniqueInvolution M (g * t * g⁻¹) := by
    rw [← hMg]
    exact (Q8Datum.isUniqueInvolution_core h.datum).conj g
  have hz : zM = g * t * g⁻¹ := hzM'.eq hzM |>.symm
  subst hz
  have hfam' : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hRc' : tightCore (conjSub g R) = conjSub g R := by
    rw [← conjSub_tightCore, hRc]
  have hN' : N ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam', ← conjSub_tightCore, hMg]
    exact hN
  have hcq := classicalOrQuietOrOddFree_of_edge_twin hex hA hh' hRc' hZ hN' hzN (Ne.symm hne) hcomm
  have hBelow : CIT3Below (Nat.card Y) := h.card ▸ h.below
  rcases hcq with hcq | hcq
  · exact TL4.autOddFreeOn_of_classicalOrQuiet hBelow hZ hzN.ne_one hcq L hL hLN hm
  · exact hcq.2 L hL hLN hm

theorem oddCent_eq_bot_of_twinCore_oddFree (hex : TwinEdgeExitOddFree n)
    (hA : TwinSecAOddFree n) (h : TwinCoreHyp n Y R S t) (hRc : tightCore R = R)
    (hZ : Subgroup.center Y = ⊥)
    (hconn : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hα : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M,
      ∀ zM zN : Y, IsUniqueInvolution M zM → IsUniqueInvolution N zN → zM ≠ zN →
        alphaOf (Subgroup.closure ({zM, zN} : Set Y)) = ⊥) :
    oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
  oddCent_eq_bot_of_alpha h.hyp h.oddFree (Q8Datum.isUniqueInvolution_core h.datum) hconn hα
    (autOddFreeOn_of_edges_oddFree hex hA h hRc hZ)

end Edge

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
