module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescentSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge.Fam
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def omegaACore (Ω : Set (Subgroup G)) (C : Subgroup G) : Set (Subgroup G) :=
  {L | ∃ J ∈ Ω, (∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ C) ∧ L = tightCore (J ⊓ C)}

@[expose] def omegaAFam (Ω : Set (Subgroup G)) (C : Subgroup G) : Set (Subgroup ↥C) :=
  restrictFamily (omegaACore Ω C) C

theorem conjInvariant_omegaAFam (hΩ : HypOmegaGen Ω) (C : Subgroup G) :
    ConjInvariant (omegaAFam Ω C) := by
  rintro n _ ⟨L, ⟨J, hJ, ⟨P, hP, hPC⟩, rfl⟩, hLC, rfl⟩
  have hnC : (n : G) ∈ C := n.2
  have hCn : conjSub (n : G) C = C := conjSub_eq_self_of_mem hnC
  have hinf : conjSub (n : G) (J ⊓ C) = conjSub (n : G) J ⊓ C := by
    ext y
    simp only [mem_conjSub_iff, Subgroup.mem_inf]
    have : ∀ y : G, (n : G)⁻¹ * y * (n : G) ∈ C ↔ y ∈ C := fun y => by
      constructor
      · intro h
        have := C.mul_mem (C.mul_mem hnC h) (C.inv_mem hnC)
        simpa [mul_assoc] using this
      · intro h
        exact C.mul_mem (C.mul_mem (C.inv_mem hnC) h) hnC
    rw [this y]
  refine ⟨conjSub (n : G) (tightCore (J ⊓ C)), ⟨conjSub (n : G) J, hΩ.conjInvariant _ J hJ,
    ⟨conjSub (n : G) P, Sec6Gen.isSylow2In_conjSub hP _, ?_⟩, ?_⟩, ?_,
    conjSub_subgroupOf C n _⟩
  · have := conjSub_mono (n := (n : G)) hPC
    rwa [hCn] at this
  · rw [conjSub_tightCore, hinf]
  · have := conjSub_mono (n := (n : G)) hLC
    rwa [hCn] at this

theorem hypOmegaGen_omegaAFam (hΩ : HypOmegaGen Ω) (C : Subgroup G) :
    HypOmegaGen (omegaAFam Ω C) :=
  ((TwinADescent.clauses_of_cores hΩ C (fun M hM => hM)).restrict C).hypOmegaGen (conjInvariant_omegaAFam hΩ C)

theorem typeRHyp_omegaAFam (h : TypeRHyp Ω) (C : Subgroup G) : TypeRHyp (omegaAFam Ω C) where
  hyp := hypOmegaGen_omegaAFam h.hyp C
  twoGroup := by
    rintro _ ⟨L, ⟨J, hJ, ⟨P, hP, hPC⟩, rfl⟩, hLC, rfl⟩
    have hLJ : tightCore (J ⊓ C) ≤ J := (tightCore_le _).trans inf_le_left
    have hL2 : IsPGroup 2 (↥(tightCore (J ⊓ C)) ⧸ classicalInvolutionOddCore ↥(tightCore (J ⊓ C))) := by
      set L : Subgroup G := tightCore (J ⊓ C) with hL
      let ι : ↥L →* ↥J := Subgroup.inclusion hLJ
      set N' : Subgroup ↥L := (classicalInvolutionOddCore ↥J).comap ι with hN'
      haveI : N'.Normal := Subgroup.Normal.comap inferInstance ι
      have hinj : Function.Injective ι := Subgroup.inclusion_injective hLJ
      have hodd : Odd (Nat.card N') := by
        have h1 : Nat.card ↥N' = Nat.card ↥(N'.map ι) :=
          (Nat.card_congr (N'.equivMapOfInjective ι hinj).toEquiv)
        have h2 : N'.map ι ≤ classicalInvolutionOddCore ↥J := Subgroup.map_comap_le _ _
        have h3 : Nat.card ↥(N'.map ι) ∣ Nat.card ↥(classicalInvolutionOddCore ↥J) :=
          Subgroup.card_dvd_of_le h2
        rw [h1]
        exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥J) h3
      have hle : N' ≤ classicalInvolutionOddCore ↥L := le_sSup ⟨inferInstance, hodd⟩
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨k, hk⟩ := h.twoGroup J hJ (QuotientGroup.mk (ι g))
        refine ⟨k, ?_⟩
        have h1 : (ι g) ^ (2 ^ k) ∈ classicalInvolutionOddCore ↥J := by
          rw [← QuotientGroup.eq_one_iff]
          simpa using hk
        have h2 : g ^ (2 ^ k) ∈ N' := by
          show ι (g ^ (2 ^ k)) ∈ classicalInvolutionOddCore ↥J
          simpa using h1
        have h3 := hle h2
        simpa using (QuotientGroup.eq_one_iff _).mpr h3
    let φ : ↥((tightCore (J ⊓ C)).subgroupOf C) ≃* ↥(tightCore (J ⊓ C)) :=
      Subgroup.subgroupOfEquivOfLe hLC
    exact hL2.of_equiv (QuotientGroup.congr _ _ φ.symm
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ.symm))
  sylow := by
    rintro _ ⟨L, ⟨J, hJ, ⟨P₀, hP₀, hP₀C⟩, rfl⟩, hLC, rfl⟩ P hP
    obtain ⟨-, -, -, hP₀L, -⟩ := member_data h.hyp hJ hP₀ hP₀C
    have hP' : IsSylow2In (P.map C.subtype) (tightCore (J ⊓ C)) := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hLC] at this
    obtain ⟨x, -, hx⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP₀L hP'
    obtain ⟨e⟩ := h.sylow J hJ P₀ hP₀
    let e1 : ↥P ≃* ↥(P.map C.subtype) := P.equivMapOfInjective C.subtype C.subtype_injective
    let e2 : ↥P₀ ≃* ↥(conjSub x P₀) :=
      P₀.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
    exact ⟨(e1.trans (MulEquiv.subgroupCongr hx.symm)).trans (e2.symm.trans e)⟩

end Fam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
