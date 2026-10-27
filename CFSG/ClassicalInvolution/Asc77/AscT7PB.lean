module

public import CFSG.ClassicalInvolution.Asc77.AscT7PA
public import CFSG.ClassicalInvolution.Asc77.AscT7RG

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
  CFSG.ClassicalInvolution.Disconnected

namespace T7P

section Conn

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def SectionDConnected (Ω : Set (Subgroup G)) (c : G) : Prop :=
  Disconnected.DConnected (quotFamily (restrictFamily (sectionFamily Ω (Subgroup.zpowers c))
    (sectionHull Ω (Subgroup.zpowers c)))
    (classicalInvolutionOddCore ↥(sectionHull Ω (Subgroup.zpowers c))))

theorem exists_conj_tqMembers_of_dconn (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {c : G} (hc2 : c * c = 1) {B : Subgroup G}
    (hB : B ∈ tqMembers Ω c) (hconn : SectionDConnected Ω c) :
    ∀ M ∈ tqMembers Ω c, ∃ n ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)),
      ∃ J' ∈ tqMembers Ω c, J' ∈ dComp Ω B ∧ M = conjSub n J' := by
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  have hcent : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton']
  have hBm : B ∈ sectionMembers Ω (Subgroup.zpowers c) := by
    rw [sectionMembers_zpowers]; exact hB
  intro M hM
  have hMs : M ∈ sectionMembers Ω (Subgroup.zpowers c) := by
    rw [sectionMembers_zpowers]; exact hM
  obtain ⟨n, hn, J', hJ', hJ'd, rfl⟩ :=
    exists_conj_mem_dComp_of_dconn hp hq hΩ hcA hBm hconn hMs
  refine ⟨(n : G), ?_, J', ?_, hJ'd, rfl⟩
  · have hnO : (n : G) ∈ oddCoreOf (sectionHull Ω (Subgroup.zpowers c)) := ⟨n, hn, rfl⟩
    have hnC := oddCoreOf_sectionHull_le hΩ (Subgroup.zpowers c) hnO
    rw [hcent] at hnC
    exact hnC
  · rw [sectionMembers_zpowers] at hJ'
    exact hJ'

end Conn

section UFrame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

set_option linter.unusedSectionVars false


theorem Hyp21.rLayer_u_le_sigmaGen_of_dconn (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) (hconn : SectionDConnected Ω u) :
    rLayer Ω u ≤ sigmaGen Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one h.hu2
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := exists_mem_tqMembers_u hp hq hΩ hK hz h.std.hK' h.std.hne h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨M, hMΩ, hRM⟩ := exists_isSylow2In_of_mem_RSet hR
  have hMt : M ∈ tqMembers Ω u :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hMΩ, R, hRM, hRc⟩
  obtain ⟨n, hn, J', -, hJ'd, hM⟩ :=
    exists_conj_tqMembers_of_dconn hp hq hΩ h.hu2 hJ₀t hconn M hMt
  have hnz : n * z = z * n := h.oddCore_centralizer_u_comm hα hn
  have hnz' : n⁻¹ * z = z * n⁻¹ := by
    have h1 := congrArg (fun y => n⁻¹ * y * n⁻¹) hnz
    simpa [mul_assoc] using h1.symm
  have hg : conjSub n K ∈ dComp Ω K := h.conjSub_mem_dComp_of_comm hnz
  have hg' : conjSub n⁻¹ K ∈ dComp Ω K := h.conjSub_mem_dComp_of_comm hnz'
  have hσ := T7A.conjSub_sigmaGen_eq hΩ.conjInvariant hK hg hg'
  have hJ'K : J' ∈ dComp Ω K := hJ₀d.trans hJ'd
  have hJ'le : J' ≤ sigmaGen Ω K := le_iSup₂_of_le J' hJ'K le_rfl
  have h2 := conjSub_mono (n := n) hJ'le
  rw [hσ, ← hM] at h2
  exact hRM.1.trans h2

end UFrame

end T7P

end CFSG.ClassicalInvolution.Asc77
