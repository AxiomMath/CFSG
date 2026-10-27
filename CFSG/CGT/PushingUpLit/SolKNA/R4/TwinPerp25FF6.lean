module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF3

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin (TwinT4Hyp)

section FamF


variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {b : Y} {K : Subgroup Y} {t : Y}

variable (b K) in
@[expose] def famF (X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :
    Set (Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) :=
  quotFamily (restrictFamily (fFam b K) X) (classicalInvolutionOddCore ↥X)

theorem imgX_mem_famF {c : Y} (hc : c ∈ Subgroup.centralizer ({b} : Set Y))
    {X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (hX : (coreAt b (conjSub c K)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ≤ X) :
    imgX b X (conjSub c K) ∈ famF b K X :=
  ⟨_, ⟨_, ⟨coreAt b (conjSub c K), ⟨c, hc, rfl⟩, TwinADescent.coreAt_le_centralizer b _, rfl⟩,
    hX, rfl⟩, rfl⟩

theorem exists_of_mem_famF {X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    {M : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)} (hM : M ∈ famF b K X) :
    ∃ c ∈ Subgroup.centralizer ({b} : Set Y),
      (coreAt b (conjSub c K)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ≤ X ∧
        M = imgX b X (conjSub c K) := by
  obtain ⟨_, ⟨_, ⟨_, ⟨c, hc, rfl⟩, -, rfl⟩, hX, rfl⟩, rfl⟩ := hM
  exact ⟨c, hc, hX, rfl⟩

theorem famF_hyp (h : FBase Ω b K t) (X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :
    HypOmegaGen (famF b K X) :=
  TwinEdge.hypOmegaGen_quotFamily_odd (hypOmegaGen_restrict h.hypOmegaGen_fFam X)
    (CFSG.ComponentClassification.OddCore.odd_card ↥X)

theorem famF_twoGroup (h : FBase Ω b K t)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :
    ∀ J ∈ famF b K X, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J) := by
  intro J hJ
  obtain ⟨c, hc, hMX, rfl⟩ := exists_of_mem_famF hJ
  have h1 : IsPGroup 2 (↥(coreAt b (conjSub c K)) ⧸
      classicalInvolutionOddCore ↥(coreAt b (conjSub c K))) :=
    TwinEdge.isPGroup_two_quotient_of_le (TwinADescent.coreAt_le_left b _)
      (h2 _ (h.memberData hc).1)
  have h2C := isPGroup_two_quotient_subgroupOf (coreAt b (conjSub c K))
    (Subgroup.centralizer ({b} : Set Y)) h1
  have h2X := isPGroup_two_quotient_subgroupOf
    ((coreAt b (conjSub c K)).subgroupOf (Subgroup.centralizer ({b} : Set Y))) X h2C
  exact TwinDisc.isPGroup_two_quotient_map (CFSG.ComponentClassification.OddCore.odd_card ↥X) h2X

theorem restrictF_quat (h : FBase Ω b K t) {k : ℕ}
    (hq : ∃ Q : Subgroup Y, IsSylow2In Q (coreAt b K) ∧ Nonempty (↥Q ≃* QuaternionGroup k))
    (X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :
    ∀ L ∈ restrictFamily (fFam b K) X, ∃ P : Subgroup ↥X, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup k) := by
  rintro _ ⟨L₀, hL₀, hMX, rfl⟩
  obtain ⟨L₁, ⟨c, hc, rfl⟩, hL₁C, rfl⟩ := hL₀
  obtain ⟨Q, hQ, ⟨e⟩⟩ := hq
  have hPs : IsSylow2In (conjSub c Q) (coreAt b (conjSub c K)) := by
    have := hQ.conj c
    rwa [TwinADescent.conjSub_coreAt hc K] at this
  have hPc : conjSub c Q ≤ Subgroup.centralizer ({b} : Set Y) :=
    hPs.1.trans (TwinADescent.coreAt_le_centralizer b _)
  have hs1 : IsSylow2In ((conjSub c Q).subgroupOf (Subgroup.centralizer ({b} : Set Y)))
      ((coreAt b (conjSub c K)).subgroupOf (Subgroup.centralizer ({b} : Set Y))) :=
    hPs.subgroupOf hL₁C
  have hs2 := hs1.subgroupOf hMX
  refine ⟨_, hs2, ⟨?_⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe (hs1.1.trans hMX)).trans
    ((Subgroup.subgroupOfEquivOfLe hPc).trans
      ((Subgroup.equivMapOfInjective Q (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).symm.trans e))

theorem famF_quat (h : FBase Ω b K t) {k : ℕ}
    (hq : ∃ Q : Subgroup Y, IsSylow2In Q (coreAt b K) ∧ Nonempty (↥Q ≃* QuaternionGroup k))
    (X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :
    ∀ J ∈ famF b K X, ∀ P : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X),
      IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup k) := by
  intro J hJ
  apply TwinDisc.forall_sylow_iso_of_exists
  exact quatSylow_quot_odd (CFSG.ComponentClassification.OddCore.odd_card ↥X)
    (restrictF_quat h hq X) J hJ

theorem famF_aEmpty (h : FBase Ω b K t) (hA : ∀ M ∈ fFam b K, AEmpty (fFam b K) M)
    (X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :
    ∀ M ∈ famF b K X, AEmpty (famF b K X) M := by
  have hΛ := h.hypOmegaGen_fFam
  have hΛX := hypOmegaGen_restrict hΛ X
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  refine TwinADescent2.aEmpty_quotFamily_gen hΛX
    (TwinEdge.hypOmegaGen_quotFamily_odd hΛX hodd) hodd ?_
  rintro _ ⟨L₀, hL₀, hL₀X, rfl⟩
  exact Thm4Twin.aEmpty_restrict hΛ (subset_refl _) hL₀X (hA L₀ hL₀)

theorem twinT4Hyp_famF (h : FBase Ω b K t)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) {r' : ℕ}
    (hq : ∃ Q : Subgroup Y, IsSylow2In Q (coreAt b K) ∧
      Nonempty (↥Q ≃* QuaternionGroup (2 ^ (r' - 2))))
    (hA : ∀ M ∈ fFam b K, AEmpty (fFam b K) M)
    (X : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :
    TwinT4Hyp r' (↥X ⧸ classicalInvolutionOddCore ↥X) (famF b K X) :=
  ⟨famF_hyp h X, famF_twoGroup h h2 X, famF_quat h hq X, famF_aEmpty h hA X,
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥X⟩

end FamF

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
