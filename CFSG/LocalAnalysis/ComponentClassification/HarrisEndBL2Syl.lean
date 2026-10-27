module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Qc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Norm4
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowCheck
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Model
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisTransport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSubfield
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBFusion4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Norm3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGroups
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415H
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415V
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma415Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelAction
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

theorem EndB.comm_of_sq {G : Type*} [Group G] {H : Subgroup G} (h : ∀ a ∈ H, a * a = 1)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  have h1 := h _ (mul_mem ha hb)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = b * a := by rw [mul_inv_rev, hai, hbi]

namespace Setting46e

theorem card_U_le_four_mul (hKC : AutPSL2CentralizerInput)
    (hs : Setting46e t L p f S w z V i j) :
    Nat.card ↥(V ⊓ centralizer ({β₀} : Set X)) ≤ 4 * Nat.card T₀ := by
  classical
  have hβ2 : (β₀) ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hβzc : (β₀) * z = z * (β₀) :=
    (mem_centralizer_singleton_iff.mp (K_le_centralizer_beta i j hs.lemma45.z_mem.2)).symm
  have hzV := hs.z_mem_center_V
  have hfib : ∀ a ∈ V ⊓ centralizer ({β₀} : Set X), ∀ a' ∈ V ⊓ centralizer ({β₀} : Set X),
      a * t * a⁻¹ = a' * t * a'⁻¹ → a⁻¹ * a' ∈ T₀ := by
    intro a ha a' ha' heq
    have hkV : a⁻¹ * a' ∈ V := mul_mem (inv_mem ha.1) ha'.1
    have hkβ : a⁻¹ * a' ∈ centralizer ({β₀} : Set X) := mul_mem (inv_mem ha.2) ha'.2
    have htk : t ∈ centralizer ({a⁻¹ * a'} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc t * (a⁻¹ * a') = a⁻¹ * (a * t * a⁻¹) * a' := by group
        _ = a⁻¹ * (a' * t * a'⁻¹) * a' := by rw [heq]
        _ = a⁻¹ * a' * t := by group
    have hzk : z ∈ centralizer ({a⁻¹ * a'} : Set X) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzV.2) _ hkV).symm
    have hβk : β₀ ∈ centralizer ({a⁻¹ * a'} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hkβ).symm
    have huk : w ^ (orderOf w / 2) ∈ centralizer ({a⁻¹ * a'} : Set X) := by
      have hu : w ^ (orderOf w / 2) = (β₀) * (z ^ j)⁻¹ * (t ^ i)⁻¹ := by group
      rw [hu]
      exact mul_mem (mul_mem hβk (inv_mem (pow_mem hzk j))) (inv_mem (pow_mem htk i))
    have hXk : X₈ ≤ centralizer ({a⁻¹ * a'} : Set X) := (closure_le _).mpr (by
      rintro x (rfl | rfl | rfl)
      · exact htk
      · exact huk
      · exact hzk)
    rw [← hs.setup.inf_centralizer_X_eq hKC hs.sylow_V hs.le_V]
    exact ⟨hkV, mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (hXk hx)⟩
  have hval : ∀ v ∈ V ⊓ centralizer ({β₀} : Set X),
      v * t * v⁻¹ ∈ ({t, t * β₀, t * z, t * (β₀ * z)} : Finset X) := by
    intro v hv
    have h1 := hs.setup.conj_t_mem_of_mem_U hs.sylow_V hs.beta hv
    have e : v * t * v⁻¹ = t * (t⁻¹ * (v * t * v⁻¹)) := by group
    rcases mem_closure_pair hβ2 hz2 hβzc h1 with h | h | h | h <;> rw [e, h] <;> simp
  have h := L415.card_le_of_fiber (A := V ⊓ centralizer ({β₀} : Set X)) (K := T₀)
    (fun v => v * t * v⁻¹) hfib ({t, t * β₀, t * z, t * (β₀ * z)} : Finset X) hval
  have h1 := Subgroup.card_le_of_le
    (inf_le_right : (V ⊓ centralizer ({β₀} : Set X)) ⊓ T₀ ≤ T₀)
  have h2 : ({t, t * β₀, t * z, t * (β₀ * z)} : Finset X).card ≤ 4 := Finset.card_le_four
  calc Nat.card ↥(V ⊓ centralizer ({β₀} : Set X)) ≤ Nat.card T₀ * 4 :=
        h.trans (Nat.mul_le_mul h1 h2)
    _ = 4 * Nat.card T₀ := mul_comm _ _

end Setting46e

end CFSG.ComponentClassification.HarrisLit
