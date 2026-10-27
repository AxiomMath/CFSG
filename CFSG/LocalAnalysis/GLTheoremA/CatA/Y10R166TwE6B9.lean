module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B8

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix
open CFSG.HardMathSupport.Lang.E6Descent
open scoped commutatorElement

section Certs


variable {Ω : Type} [Field Ω] [CharP Ω 2]

namespace TwE6B

private theorem commutator_self_le {G : Type*} [Group G] (S : Subgroup G) : ⁅S, S⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem twE6Block_isSubnormal {Fr : Ω →+* Ω} {ω : Ωˣ} {n : ℕ} {K : Type} [Field K]
    [Algebra K Ω] [IsAlgClosure K Ω] (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n) (hω : orderOf ω = 3) :
    CFSG.Open.IsSubnormal (twE6Block Fr)
      (twE6C Fr ⊓ Subgroup.centralizer
        ({eBar (Ω := Ω) ω, fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω))) := by
  set H : Subgroup (ModGL Tag.E6 Ω) :=
    twE6C Fr ⊓ Subgroup.centralizer ({eBar (Ω := Ω) ω, fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω))
    with hH
  set M : Subgroup (ModGL Tag.E6 Ω) := toralRootGroup Tag.E6 Ω (eBarTuple ω) with hM
  set X : Subgroup (ModGL Tag.E6 Ω) := toralCentralizer Tag.E6 Ω (eBarTuple ω) with hX
  have hMX : M ≤ X := toralRootGroup_le (eBarTuple ω)
  have hMnX : (M.subgroupOf X).Normal :=
    (Chevalley_toral_centralizer_root_generated_quotient Tag.E6 Ω (eBarTuple ω)).2.1
  have hHR : H ≤ TwistedDiag.thetaFixed Fr := fun x hx =>
    commutator_self_le _ (mem_twE6C.1 hx.1)
  have hHX : H ≤ X := by
    intro x hx
    rw [hX]
    show x ∈ adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer {rootDiagUnit Tag.E6 (eBarTuple ω)}
    refine ⟨(TwistedDiag.mem_thetaFixed Fr).1 (hHR hx) |>.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hx.2 (eBar (Ω := Ω) ω) (by simp)).symm
  have hLMC : twE6Block Fr ≤ twE6C Fr := twE6Block_le_C (Ω := Ω) hFr hK hn hod
  have hLcen : twE6Block Fr ≤ Subgroup.centralizer
      ({eBar (Ω := Ω) ω, fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) :=
    twE6Block_le_centralizer_pair
  have hLM : twE6Block Fr ≤ M := by
    refine (twE6Block_le_subsystem Fr).trans ?_
    rw [hM, toralRootGroup, subsystemGroup_eq_rootSpan]
    exact (rootSpan_mono (parabolicRoots_support56_subset_kernelRoots (ω := ω))).trans le_sup_right
  have hLMH : twE6Block Fr ≤ M ⊓ H := le_inf hLM (le_inf hLMC hLcen)
  have hLnormal : ((twE6Block Fr).subgroupOf (M ⊓ H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLMH]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgR : g ∈ TwistedDiag.thetaFixed Fr := hHR hg.2
    have hGN := Subgroup.mem_normalizer_iff.1
      (toralRootGroup_le_normalizer_subsystemGroup56 (ω := ω) hω hg.1) x
    constructor
    · intro hx
      rw [mem_twE6Block] at hx ⊢
      refine ⟨hGN.1 hx.1, ?_⟩
      show g * x * g⁻¹ ∈ TwistedDiag.thetaFixed Fr
      exact mul_mem (mul_mem hgR hx.2) (inv_mem hgR)
    · intro hx
      rw [mem_twE6Block] at hx ⊢
      refine ⟨hGN.2 hx.1, ?_⟩
      have h := mul_mem (mul_mem (inv_mem hgR) hx.2) hgR
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at h
  have hMHnormal : ((M ⊓ H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro g hg
    have hNM : g ∈ Subgroup.normalizer (M : Set (ModGL Tag.E6 Ω)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMX).1 hMnX (hHX hg)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hGN := Subgroup.mem_normalizer_iff.1 hNM x
    constructor
    · rintro ⟨hxM, hxH⟩
      refine ⟨hGN.1 hxM, ?_⟩
      show g * x * g⁻¹ ∈ H
      exact mul_mem (mul_mem hg hxH) (inv_mem hg)
    · rintro ⟨hxM, hxH⟩
      refine ⟨hGN.2 hxM, ?_⟩
      have h := mul_mem (mul_mem (inv_mem hg) hxH) hg
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at h
  exact CFSG.Open.IsSubnormal.step hLMH hLnormal
    (CFSG.Open.IsSubnormal.step inf_le_right hMHnormal (CFSG.Open.IsSubnormal.refl H))

theorem e3_in_C_packaged {K : Type} [Field K] [Algebra K Ω] [IsAlgClosure K Ω] {n : ℕ}
    {Fr : Ω →+* Ω} {ω : Ωˣ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n)
    (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3) :
    eBar (Ω := Ω) ω ∈ twE6C Fr ∧ fBar (Ω := Ω) ω ∈ twE6C Fr ∧
      orderOf (eBar (Ω := Ω) ω) = 3 ∧ orderOf (fBar (Ω := Ω) ω) = 3 ∧
      Commute (eBar (Ω := Ω) ω) (fBar (Ω := Ω) ω) ∧
      Nat.card (Subgroup.closure
        ({eBar (Ω := Ω) ω, fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω))) = 9 ∧
      twE6Block Fr ≤ twE6C Fr ∧
      twE6Block Fr ≤ Subgroup.centralizer ({eBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) ∧
      twE6Block Fr ≤ Subgroup.centralizer ({fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) ∧
      twE6Block Fr ≤ Subgroup.centralizer
        ({eBar (Ω := Ω) ω, fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) ∧
      CFSG.Open.IsSubnormal (twE6Block Fr)
        (twE6C Fr ⊓ Subgroup.centralizer
          ({eBar (Ω := Ω) ω, fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω))) ∧
      CFSG.Open.IsQuasisimple ↥(twE6Block Fr) ∧
      3 ∣ Nat.card (↥(twE6Block Fr) ⧸ Subgroup.center ↥(twE6Block Fr)) := by
  have hq := twE6_block_isQuasisimple (Ω := Ω) hFr hK hn hod
  exact ⟨eBar_mem_C hFr hK hn hod hω3, fBar_mem_C hFr hK hn hod hω3,
    orderOf_eBar hω3 hω, orderOf_fBar hω3 hω, commute_eBar_fBar,
    card_closure_eBar_fBar hω3 hω,
    twE6Block_le_C (Ω := Ω) hFr hK hn hod,
    twE6Block_le_centralizer_eBar, twE6Block_le_centralizer_fBar,
    twE6Block_le_centralizer_pair,
    twE6Block_isSubnormal (Ω := Ω) hFr hK hn hod hω, hq.1, hq.2⟩

end TwE6B

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
