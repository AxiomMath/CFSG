module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FBruhat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2ConjStmt

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.Timmesfeld.ExceptionalOrders
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.TCX.Tri

set_option linter.unusedSectionVars false

@[expose] def TwE6ThreeA2ConjAt
    (K : Type) [Field K] (σ : K ≃+* K) : Prop :=
  ∀ x ∈ twistedE6RootGroup K σ, ∀ y ∈ twistedE6RootGroup K σ, x ^ 3 = 1 → y ^ 3 = 1 →
    Module.finrank K
        (LinearMap.ker ((x : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 →
    Module.finrank K
        (LinearMap.ker ((y : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 →
      ∃ g ∈ twistedE6RootGroup K σ, g * x * g⁻¹ = y

theorem twE6ThreeA2ConjAt_of_stmt
    (h : TwE6ThreeA2ConjStmt) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hch : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1)
    (hq : q ≠ 2) : TwE6ThreeA2ConjAt K σ :=
  h K σ q hch hσ hK h3 hq

section Outer


theorem twExists_inndiag_notMem_root {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (h3 : 3 ∣ q + 1) :
    ∃ d ∈ twistedE6InndiagGL K σ, d ∉ twistedE6RootGroup K σ := by
  classical
  obtain ⟨u, hu⟩ := exists_twKappa_ne_one σ hK hσ h3
  refine ⟨rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u),
    le_sup_right (a := twistedE6RootGroup K σ) ⟨u, rfl⟩, fun hd => hu ?_⟩
  have hdΓ := graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hd
  have hadj : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      adjointGroup TwistTag.E6.tag K :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom hdΓ
  have hH := CFSG.LocalAnalysis.GLTheoremA.YS04E6F.rootDiagUnit_mem_torusGroup_of_mem _ hadj
  have hT : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      graphFixedRootTorus TwistTag.E6 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hH, hdΓ⟩, hd⟩
  rw [graphFixedRootTorus_eq_compatTorus σ.surjective] at hT
  obtain ⟨c, hc, hcd⟩ := (mem_compatTorus (t := TwistTag.E6) σ.toRingHom).1 hT
  rw [torusCoordHom_eq_rootDiagUnit (τ := TwistTag.E6.tag) (K := K) c] at hcd
  have hcb := CFSG.LieType.Chevalley.rootDiagUnit_injective hcd
  exact twKappa_twIm σ ⟨c, hc, hcb⟩

theorem twExists_inndiag_comm_notMem_root {K : Type} [Field K] {σ : K ≃+* K}
    (hconj : TwE6ThreeA2ConjAt K σ) {h₀ : ModGL TwistTag.E6.tag K}
    (hh₀ : h₀ ∈ twistedE6RootGroup K σ) (hh₀3 : h₀ ^ 3 = 1)
    (hdim : Module.finrank K
      (LinearMap.ker ((h₀ : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24)
    {d : ModGL TwistTag.E6.tag K} (hd : d ∈ twistedE6InndiagGL K σ)
    (hdC : d ∉ twistedE6RootGroup K σ) :
    ∃ ĝ ∈ twistedE6InndiagGL K σ, ĝ ∉ twistedE6RootGroup K σ ∧ ĝ * h₀ = h₀ * ĝ := by
  have hN : d * h₀ * d⁻¹ ∈ twistedE6RootGroup K σ :=
    (Subgroup.mem_normalizer_iff.1 (twistedE6InndiagGL_le_normalizer K σ hd) h₀).1 hh₀
  have h1 : (d * h₀ * d⁻¹) ^ 3 = 1 := by rw [conj_pow, hh₀3, mul_one, mul_inv_cancel]
  have h2 : Module.finrank K (LinearMap.ker (((d * h₀ * d⁻¹ : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 := by
    rw [finrank_ker_conj_sub_one d h₀, hdim]
  obtain ⟨g, hg, hgx⟩ := hconj _ hN h₀ hh₀ h1 hh₀3 h2 hdim
  refine ⟨g * d, mul_mem ((le_sup_left : twistedE6RootGroup K σ ≤ twistedE6InndiagGL K σ) hg) hd,
    fun hgd => hdC ?_, ?_⟩
  · simpa using mul_mem (inv_mem hg) hgd
  · calc g * d * h₀ = (g * (d * h₀ * d⁻¹) * g⁻¹) * (g * d) := by group
      _ = h₀ * (g * d) := by rw [hgx]

end Outer

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
