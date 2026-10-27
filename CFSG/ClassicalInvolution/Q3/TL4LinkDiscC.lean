module

public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscB2
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC1
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

namespace LinkDisc

section Frame


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_edge_of_frame (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hOm : OmegaAutOddFreeR) (hL : TightLargeHypR 3 n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hα : LinkAlphaBad R t)
    (hall : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J)
    {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hMJ : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J)
    (hB2 : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
        secImg (CoreAssembly.conjClass (tightCore R)) t L =
          secImg (CoreAssembly.conjClass (tightCore R)) t M)
    {u : Y} (hu : IsUniqueInvolution J u) {e : Y}
    (heK : e ∈ Subgroup.centralizer ((tightCore R : Subgroup Y) : Set Y))
    (heJ : e ∈ Subgroup.centralizer (J : Set Y)) (he2 : e * e = 1)
    (heE : e ∉ Subgroup.closure ({t, u} : Set Y)) : False := by
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htu : t ≠ u := fun h' => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (h' ▸ hu))
  have hH := hyp51_edgeFrame h4 h5 htw hE4 hOm hL hJ (hall J hJ) hM hMJ hu heK heJ he2 heE
  have hEB : Subgroup.closure ({u, t} : Set Y) ≤ Subgroup.closure ({t, u, e} : Set Y) :=
    Subgroup.closure_mono (Set.insert_subset_iff.mpr ⟨by simp, Set.singleton_subset_iff.mpr
      (by simp)⟩)
  have hodd := (lemma54_odd_and_eq hH hEB
    (T7A.isElemAbelian2_closure_pair hu.sq ht.sq hu.ne_one ht.ne_one htu.symm ctu.symm)).1
  have hconst := alphaOf_eq_of_edge hL hJ (hall J hJ) hM hMJ hB2 hu
  have hnorm := normal_alphaOf_of_edges hΩ hc ht hJ hconst
  have hbot : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ := by
    have hle : alphaOf (Subgroup.closure ({u, t} : Set Y)) ≤ classicalInvolutionOddCore Y :=
      le_sSup ⟨hnorm, hodd⟩
    rwa [hL.cls.2.2, le_bot_iff] at hle
  obtain ⟨J', hJ', u', hu', hne⟩ := hα
  apply hne
  rw [Set.pair_comm, hconst J' hJ' u' hu', hbot]

@[expose] def TightLinkEdgeRigidR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t →
      (∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J) →
      classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t) ≠ ⊥ →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J →
        ∀ u : Y, IsUniqueInvolution J u →
        (∀ e ∈ Subgroup.centralizer ((tightCore R : Subgroup Y) : Set Y) ⊓
            Subgroup.centralizer (J : Set Y),
          e * e = 1 → e ∈ Subgroup.closure ({t, u} : Set Y)) →
          ¬ ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
            secImg (CoreAssembly.conjClass (tightCore R)) t L =
                secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
              secImg (CoreAssembly.conjClass (tightCore R)) t L =
                secImg (CoreAssembly.conjClass (tightCore R)) t M

theorem tightLinkEdgeOddR_of (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hOm : OmegaAutOddFreeR) (hR : TightLinkEdgeRigidR 3 n) : TightLinkEdgeOddR 3 n := by
  intro Y _ _ R S t hL hc hT hα hall hO J hJ M hM hMJ hB2
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hJ.1
  by_cases hrig : ∀ e ∈ Subgroup.centralizer ((tightCore R : Subgroup Y) : Set Y) ⊓
      Subgroup.centralizer (J : Set Y), e * e = 1 → e ∈ Subgroup.closure ({t, u} : Set Y)
  · exact hR Y R S t hL hc hT hα hall hO J hJ M hM hMJ u hu hrig hB2
  · push Not at hrig
    obtain ⟨e, he, he2, heE⟩ := hrig
    exact false_of_edge_of_frame h4 h5 htw hE4 hOm hL hc hα hall hJ hM hMJ hB2 hu
      (Subgroup.mem_inf.mp he).1 (Subgroup.mem_inf.mp he).2 he2 heE

end Frame

end LinkDisc

end CFSG.ClassicalInvolution.Q3.TL4
