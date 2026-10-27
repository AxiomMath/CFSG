module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.LJ
import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.FactsGen
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf18CaseIB
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf21M20
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf23AViolA
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3OddStand
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {G : Type} [Group G] [Finite G]

structure Std (Ω : Set (Subgroup G)) (K J : Subgroup G) (z j : G) : Prop where
  hΩ : TypeRHyp Ω
  hO : classicalInvolutionOddCore G = ⊥
  hK : K ∈ Ω
  hz : IsUniqueInvolution K z
  hzO : TightInO2 z
  hv : AViol Ω K J z j
  hall : aStar Ω K = Ω
  hgen : omegaGen Ω = ⊤

namespace Std

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {z j : G} (h : Std Ω K J z j)
include h

theorem exists_conj {M : Subgroup G} (hM : M ∈ Ω) {m : G} (hm : IsUniqueInvolution M m) :
    ∃ g : G, g * z * g⁻¹ = m :=
  (WR1.exists_conj_of_mem_aStar h.hΩ.hyp h.hK h.hz (h.hall.symm ▸ hM)).2 m hm

theorem inO2 {M : Subgroup G} (hM : M ∈ Ω) {m : G} (hm : IsUniqueInvolution M m) :
    TightInO2 m := by
  obtain ⟨g, rfl⟩ := h.exists_conj hM hm
  obtain ⟨P, hPn, hP2, hzP⟩ := h.hzO
  exact ⟨P, hPn, hP2, hPn.conj_mem z hzP g⟩

theorem isPGroup {M : Subgroup G} (hM : M ∈ Ω) : IsPGroup 2 M := by
  obtain ⟨m, hm⟩ := Sec6Gen.exists_uniqueInvolution h.hΩ.hyp hM
  obtain ⟨P, hPn, hP2, hmP⟩ := h.inO2 hM hm
  exact PhilipHall.Frame.isPGroup_of_oddCent h.hΩ.hyp hM hm
    (TC.oddCoreImg_centralizer_eq_bot h.hO hPn hP2 hmP) (h.hΩ.twoGroup M hM)

theorem nonempty_quat {M : Subgroup G} (hM : M ∈ Ω) : Nonempty (↥M ≃* QuaternionGroup 2) :=
  h.hΩ.sylow M hM M (isSylow2In_self' (h.isPGroup hM))

theorem card_eq_eight {M : Subgroup G} (hM : M ∈ Ω) : Nat.card M = 8 := by
  obtain ⟨e⟩ := h.nonempty_quat hM
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem mem_RSet {M : Subgroup G} (hM : M ∈ Ω) : M ∈ RSet Ω :=
  TL4.mem_RSet_self hM (h.isPGroup hM)

theorem commutes {M N : Subgroup G} (hM : M ∈ Ω) (hN : N ∈ Ω) (hne : M ≠ N)
    (hNM : N ≤ Subgroup.normalizer (M : Set G)) : Commutes M N :=
  TL4.commutes_of_le_normalizer h.hΩ.hyp (h.mem_RSet hM) (h.mem_RSet hN) (h.isPGroup hM)
    (h.isPGroup hN) hne hNM

theorem mem_omegaNbr_iff {L P : Subgroup G} (hP : P ∈ Ω) :
    P ∈ omegaNbr Ω L ↔ P ≠ L ∧ P ≤ Subgroup.normalizer (L : Set G) := by
  constructor
  · rintro ⟨-, hPL, R, hR, hRP, hRN⟩
    have hRs := Sec6Gen.isSylow2In_of_mem_RSet_of_le h.hΩ.hyp hP hR hRP
    have hPR : P = R := hRs.eq_of_le (h.isPGroup hP) le_rfl hRs.1
    exact ⟨hPL, hPR ▸ hRN⟩
  · rintro ⟨hPL, hPN⟩
    exact ⟨hP, hPL, P, h.mem_RSet hP, le_rfl, hPN⟩

theorem le_normalizer_of_twin {L P L' : Subgroup G} (hL : L ∈ Ω) (hP : P ∈ Ω) (hPL : P ≠ L)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hPV : P ∉ twinSet Ω L)
    (hL' : L' ∈ twinSet Ω L) : P ≤ Subgroup.normalizer (L' : Set G) := by
  obtain ⟨hL'Ω, w, hwL, hwL'⟩ := hL'
  have hc := h.commutes hL hP hPL.symm hPN
  have hPc : P ≤ Subgroup.centralizer ({w} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc w hwL.mem x hx).symm
  have hL'P : L' ≠ P := by
    rintro rfl
    exact hPV ⟨hP, w, hwL, hwL'⟩
  exact Sec6Gen.le_normalizer_of_le_centralizer h.hΩ.hyp hL'Ω hP hL'P hwL' le_rfl
    (h.isPGroup hP) (by rw [h.card_eq_eight hP]; norm_num) hPc

theorem mem_twinSet_of_le_normalizer {L P : Subgroup G} (hL : L ∈ Ω) (hP : P ∈ Ω) (hne : P ≠ L)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) : P ∈ twinSet Ω L := by
  by_contra hPV
  have hPS : P ∈ omegaOfSet Ω (twinSet Ω L) := by
    refine ⟨hP, fun L' hL' => (h.mem_omegaNbr_iff hP).mpr ⟨?_, ?_⟩⟩
    · rintro rfl
      exact hPV hL'
    · exact h.le_normalizer_of_twin hL hP hne hPN hPV hL'
  have hV : ∀ M ∈ Ω, omegaOfSet Ω (twinSet Ω K) = omegaOfSet Ω (twinSet Ω M) := by
    intro M hM
    rw [← h.hall] at hM
    exact (aStar_subset_vStar h.hΩ h.hO h.hK h.hz h.hzO hM).2
  rw [← hV L hL, hV P hP] at hPS
  obtain ⟨p, hp⟩ := Sec6Gen.exists_uniqueInvolution h.hΩ.hyp hP
  exact (hPS.2 P ⟨hP, p, hp, hp⟩).2.1 rfl

theorem le_centralizer_of_sylow (S : Sylow 2 G) (hKS : K ≤ (S : Subgroup G)) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hKs : conjSub s K ∈ Ω := h.hΩ.hyp.conjInvariant s K h.hK
  have hKsS : conjSub s K ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := s) hKS
    rwa [conjSub_eq_self_of_mem hs] at this
  have hszs : s * z * s⁻¹ = z := by
    by_cases heq : conjSub s K = K
    · exact h.hz.conj_eq heq
    · have hc := Q3CP.l67Gen G Ω h.hΩ.hyp S K (h.mem_RSet h.hK) (conjSub s K) (h.mem_RSet hKs)
        hKS hKsS (Ne.symm heq)
      have hN : conjSub s K ≤ Subgroup.normalizer (K : Set G) :=
        AscL62.le_normalizer_of_commutes hc.symm
      obtain ⟨-, w, hwK, hwKs⟩ := h.mem_twinSet_of_le_normalizer h.hK hKs heq hN
      exact ((h.hz.conj s).eq hwKs).trans (h.hz.eq hwK).symm
  calc s * z = s * z * s⁻¹ * s := by group
    _ = z * s := by rw [hszs]

theorem conj_comm (g : G) : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
  obtain ⟨S, hKS⟩ := (h.isPGroup h.hK).exists_le_sylow
  obtain ⟨P, hPn, hP2, hzP⟩ := h.hzO
  have hPS : P ≤ (S : Subgroup G) := hP2.le_sylow_of_normal S
  have hgz : g * z * g⁻¹ ∈ (S : Subgroup G) := hPS (hPn.conj_mem z hzP g)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_of_sylow S hKS hgz))

theorem conj_comm' (g g' : G) :
    (g * z * g⁻¹) * (g' * z * g'⁻¹) = (g' * z * g'⁻¹) * (g * z * g⁻¹) := by
  have h1 := h.conj_comm (g'⁻¹ * g)
  calc (g * z * g⁻¹) * (g' * z * g'⁻¹)
      = g' * (((g'⁻¹ * g) * z * (g'⁻¹ * g)⁻¹) * z) * g'⁻¹ := by group
    _ = g' * (z * ((g'⁻¹ * g) * z * (g'⁻¹ * g)⁻¹)) * g'⁻¹ := by rw [h1]
    _ = (g' * z * g'⁻¹) * (g * z * g⁻¹) := by group

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
