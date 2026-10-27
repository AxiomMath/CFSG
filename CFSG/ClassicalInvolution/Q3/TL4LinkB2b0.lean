module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC1
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4F
public import CFSG.ClassicalInvolution.Q3.TL4StepNoTri
public import CFSG.ClassicalInvolution.Q3.TL4VtxMainB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

section Frame


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hyp51_edgeFrame_of_sylow (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hOm : OmegaAutOddFreeR) (hL : TightLargeHypR 3 n Y R S t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hbad : NoGNbr R t J)
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hMJ : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u : Y}
    (hu : IsUniqueInvolution J u) {P T : Subgroup Y} (hP : IsSylow2In P (tightCore R))
    (hT : IsSylow2In T J) (hPT : Commutes P T) {e : Y}
    (heP : e ∈ Subgroup.centralizer (P : Set Y)) (heT : e ∈ Subgroup.centralizer (T : Set Y))
    (he2 : e * e = 1) (heE : e ∉ Subgroup.closure ({t, u} : Set Y)) :
    Hyp51 (Subgroup.closure ({t, u, e} : Set Y)) := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := h.hyp
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htP : t ∈ P := T3.mem_of_isPGroup ht hP.1 hP.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hP)
    omega)
  have huT : u ∈ T := T3.mem_of_isPGroup hu hT.1 hT.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ.1 hT)
    omega)
  have cte : t * e = e * t := Subgroup.mem_centralizer_iff.mp heP t htP
  have cue : u * e = e * u := Subgroup.mem_centralizer_iff.mp heT u huT
  have htu : t ≠ u := fun h' => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (h' ▸ hu))
  have he1 : e ≠ 1 := fun h' => heE (h' ▸ Subgroup.one_mem _)
  have hBe : IsElemAbelian 2 (Subgroup.closure ({t, u, e} : Set Y)) :=
    T8T.isElemAbelian_closure_three ht.sq hu.sq he2 ctu cte cue
  have hB8 : Nat.card ↥(Subgroup.closure ({t, u, e} : Set Y)) = 8 :=
    T8T.natCard_closure_three ht.sq hu.sq he2 ctu cte cue ht.ne_one hu.ne_one htu he1 heE
  have hBelow : CIT3Below (Nat.card Y) := by
    rw [hL.card]
    exact hL.below
  have htB : t ∈ Subgroup.closure ({t, u, e} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({t, u, e} : Set Y) := Subgroup.subset_closure (by simp)
  have heB : e ∈ Subgroup.closure ({t, u, e} : Set Y) := Subgroup.subset_closure (by simp)
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hEB : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.closure ({t, u, e} : Set Y) := by
    rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw <;> rw [hw]
    · exact htB
    · exact huB
  have hcent : ∀ x : Y, x * t = t * x → x * u = u * x → x * e = e * x →
      ∀ c ∈ Subgroup.closure ({t, u, e} : Set Y), x * c = c * x := by
    intro x hxt hxu hxe c hc
    have hle : Subgroup.closure ({t, u, e} : Set Y) ≤ Subgroup.centralizer ({x} : Set Y) := by
      rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw <;> rw [hw]
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxe.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm
  refine ⟨hBe, hB8, fun c hcB hc1 => ?_⟩
  rcases mem_closure_three_cases he2 cte cue hcB with hcE | ⟨e', he', hce⟩
  ·
    have hE := hyp51At_of_noGNbr h4 htw hOm hL hJ hbad hM hMJ hu hBe htB huB
    rcases TypeCSetup.mem_closure_pair ht.sq hu.sq ctu hcE with h1 | h1 | h1 | h1
    · exact absurd h1 hc1
    · rw [h1]
      exact hE.1
    · rw [h1]
      exact hE.2.1
    · rw [h1]
      exact hE.2.2
  subst hce
  have hne : ∀ x ∈ Subgroup.closure ({t, u} : Set Y), x ≠ e' * e := by
    intro x hx hxc
    apply heE
    have h1 : e'⁻¹ * x ∈ Subgroup.closure ({t, u} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ he') hx
    rwa [hxc, inv_mul_cancel_left] at h1
  have hcB' : e' * e ∈ Subgroup.closure ({t, u, e} : Set Y) := Subgroup.mul_mem _ (hEB he') heB
  have hgen : Subgroup.closure ({t, u, e} : Set Y) =
      Subgroup.closure ({t, u, e' * e} : Set Y) := by
    have htC : t ∈ Subgroup.closure ({t, u, e' * e} : Set Y) := Subgroup.subset_closure (by simp)
    have huC : u ∈ Subgroup.closure ({t, u, e' * e} : Set Y) := Subgroup.subset_closure (by simp)
    have hcC : e' * e ∈ Subgroup.closure ({t, u, e' * e} : Set Y) :=
      Subgroup.subset_closure (by simp)
    have hE' : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.closure ({t, u, e' * e} : Set Y) := by
      rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw <;> rw [hw]
      · exact htC
      · exact huC
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw <;> rw [hw]
      · exact htC
      · exact huC
      · have h1 : e'⁻¹ * (e' * e) ∈ Subgroup.closure ({t, u, e' * e} : Set Y) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (hE' he')) hcC
        rwa [inv_mul_cancel_left] at h1
    · rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw <;> rw [hw]
      · exact htB
      · exact huB
      · exact hcB'
  have hct : e' * e * t = t * (e' * e) := (hcent t rfl ctu cte _ hcB').symm
  have hcu : e' * e * u = u * (e' * e) := (hcent u ctu.symm rfl cue _ hcB').symm
  have hMa : XMem (CoreAssembly.conjClass (tightCore R)) (e' * e) (tightCore R) := by
    refine ⟨hK, h.tight _ hK t ht (Subgroup.mem_centralizer_singleton_iff.mpr hct), P, hP,
      fun x hx => hcent x ?_ (hPT x hx u huT) (Subgroup.mem_centralizer_iff.mp heP x hx) _
        hcB'⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht
        (Subgroup.le_normalizer (hP.1 hx)))
  have hTN : T ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) := fun x hx =>
    h.tight _ hK t ht (Subgroup.mem_centralizer_singleton_iff.mpr (hPT t htP x hx).symm)
  have hTc : ∀ x ∈ T, x * (e' * e) = e' * e * x := fun x hx => hcent x
    (Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hTN hx)))
    (Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution hu
        (Subgroup.le_normalizer (hT.1 hx))))
    (Subgroup.mem_centralizer_iff.mp heT x hx) _ hcB'
  have hMb : XMem (CoreAssembly.conjClass (tightCore R)) (e' * e) J :=
    ⟨hJ.1, h.tight _ hJ.1 u hu (Subgroup.mem_centralizer_singleton_iff.mpr hcu), T, hT, hTc⟩
  have htwS := PhilipHall.Frame.Thm1RTwinLiftSetEBelow.toSet htw
  exact hyp51At_of_vtxPair h4 h5 htwS hE4 hBelow hL.center hL.card.le h hBe hgen hc1
    ht.ne_one (hne t htE) hu.ne_one (hne u huE) htu (hne (t * u) (Subgroup.mul_mem _ htE huE))
    hMa hMb ht hu hT (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hTc x hx)) hTN

theorem false_of_edge_of_frame_of_sylow (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
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
    {u : Y} (hu : IsUniqueInvolution J u) {P T : Subgroup Y} (hP : IsSylow2In P (tightCore R))
    (hT : IsSylow2In T J) (hPT : Commutes P T) {e : Y}
    (heP : e ∈ Subgroup.centralizer (P : Set Y)) (heT : e ∈ Subgroup.centralizer (T : Set Y))
    (he2 : e * e = 1) (heE : e ∉ Subgroup.closure ({t, u} : Set Y)) : False := by
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htu : t ≠ u := fun h' => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (h' ▸ hu))
  have hH := hyp51_edgeFrame_of_sylow h4 h5 htw hE4 hOm hL hJ (hall J hJ) hM hMJ hu hP hT hPT
    heP heT he2 heE
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

end Frame

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
