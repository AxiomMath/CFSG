module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511N
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GH74.E2.CaseIINoComp
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Back112Kfacts
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH2
public import CFSG.GH74.GLS.C3.Layer1.Thm1FmemberF
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3A7
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Pump
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.IVK.Proofs2.Sec3Fac
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511J
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511M
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.McL
public import CFSG.Walter.J1
public import CFSG.Walter.W67.Section5.Lemma57
public import Certificates.Certificate3953
public import Certificates.Certificate5007
public import Certificates.Certificate5022
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem conj_t_eq_z {s : G} (hss : s * s ∈ S) (hz : z = s⁻¹ * t * s) : s * t * s⁻¹ = z := by
  have h1 := h.zS _ hss
  calc s * t * s⁻¹ = (s * s) * z * (s * s)⁻¹ := by rw [hz]; group
    _ = z := by rw [h1, mul_inv_cancel_right]

include ε in
theorem R_le_H (hD : Foote5AutData 𝕊 Lin) {s : G} (hsN : s ∈ normalizer (S : Set G))
    (hss : s * s ∈ S) (hRs : S ⊓ L ⊓ conjugate (S ⊓ L) s = ⊥) (hz : z = s⁻¹ * t * s) {r : G}
    (hr : r ∈ conjugate (S ⊓ L) s) (hr2 : r * r = 1) (hrlin : actG L ε r ∉ Lin) :
    S ⊓ L ≤ (Q ⊔ zpowers r) ⊔ (conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) := by
  intro ρ hρ
  have hrS : r ∈ S := conjugate_le_of_mem_normalizer hsN inf_le_left hr
  have hrR : ∀ ρ ∈ S ⊓ L, r * ρ = ρ * r := fun ρ hρ =>
    h.commute_of_inf_conjugate_eq_bot hsN hRs hρ hr
  set b := s⁻¹ * ρ * s with hb
  have hbRs : b ∈ conjugate (S ⊓ L) s := by
    rw [mem_conjugate_iff, hb, show s * (s⁻¹ * ρ * s) * s⁻¹ = ρ by group]
    exact hρ
  have hbS : b ∈ S := conjugate_le_of_mem_normalizer hsN inf_le_left hbRs
  have hbR : ∀ ρ' ∈ S ⊓ L, b * ρ' = ρ' * b := fun ρ' hρ' =>
    h.commute_of_inf_conjugate_eq_bot hsN hRs hρ' hbRs
  have hρb : ρ = s * b * s⁻¹ := by rw [hb]; group
  have hzt := h.conj_t_eq_z hss hz
  have hQ' : ∀ q ∈ Q, s * q * s⁻¹ ∈ conjugate Q s⁻¹ := fun q hq => by
    rw [mem_conjugate_iff, inv_inv, show s⁻¹ * (s * q * s⁻¹) * s = q by group]
    exact hq
  set H := (Q ⊔ zpowers r) ⊔ (conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) with hHdef
  have hzH : z ∈ H := mem_sup_left (mem_sup_left h.zQ)
  have hr'H : s * r * s⁻¹ ∈ H := mem_sup_right (mem_sup_right (mem_zpowers _))
  have hqH : ∀ q ∈ Q, s * q * s⁻¹ ∈ H := fun q hq => mem_sup_right (mem_sup_left (hQ' q hq))
  rw [hρb]
  rcases h.mem_Q_mul_of_centralizes_R ε hD hrS hr2 hrlin hrR hbS hbR with h1 | h1 | h1 | h1
  · exact hqH b h1
  · rw [show s * b * s⁻¹ = (s * (b * t) * s⁻¹) * (s * t * s⁻¹)⁻¹ by group, hzt]
    exact mul_mem (hqH _ h1) (inv_mem hzH)
  · rw [show s * b * s⁻¹ = (s * (b * r) * s⁻¹) * (s * r * s⁻¹)⁻¹ by group]
    exact mul_mem (hqH _ h1) (inv_mem hr'H)
  · rw [show s * b * s⁻¹ = (s * (b * r * t) * s⁻¹) * (s * t * s⁻¹)⁻¹ * (s * r * s⁻¹)⁻¹ by
      group, hzt]
    exact mul_mem (mul_mem (hqH _ h1) (inv_mem hzH)) (inv_mem hr'H)

theorem mem_H_of_not_lin (hD : Foote5AutData 𝕊 Lin) {s : G} (hsN : s ∈ normalizer (S : Set G))
    (hss : s * s ∈ S) (hRs : S ⊓ L ⊓ conjugate (S ⊓ L) s = ⊥) (hz : z = s⁻¹ * t * s) {r : G}
    (hr : r ∈ conjugate (S ⊓ L) s) (hr2 : r * r = 1) (hrlin : actG L ε r ∉ Lin) {e : G}
    (heS : e ∈ S) (he2 : e * e = 1) (helin : actG L ε e ∉ Lin) :
    e ∈ (Q ⊔ zpowers r) ⊔ (conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) := by
  have hrS : r ∈ S := conjugate_le_of_mem_normalizer hsN inf_le_left hr
  have hrR : ∀ ρ ∈ S ⊓ L, r * ρ = ρ * r := fun ρ hρ =>
    h.commute_of_inf_conjugate_eq_bot hsN hRs hρ hr
  have heN := h.S_le heS
  have hrN := h.S_le hrS
  have hsq : actG L ε e * actG L ε e = 1 := by rw [← actG_mul ε heN heN, he2, actG_one]
  obtain ⟨ρ₀', hρ₀', -, hact⟩ := hD.field_inner (h.Rbar ε) _ helin hsq (h.actG_map_Rbar ε heS)
  obtain ⟨ρ₁', hρ₁R, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ₀'
  set ρ₁ : G := (ρ₁' : G) with hρ₁
  have hρ₁L : ρ₁ ∈ L := ρ₁'.2
  have hρ₁N := h.S_le (mem_inf.mp hρ₁R).1
  have hrfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε r ρ = ρ :=
    (h.actG_fix_iff ε hrS).mpr hrR
  set y := e * r * ρ₁⁻¹ with hy
  have hyS : y ∈ S := mul_mem (mul_mem heS hrS) (inv_mem (mem_inf.mp hρ₁R).1)
  have hyfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε y ρ = ρ := by
    intro ρ hρ
    have hψ : psi L ε ρ₁' ∈ (h.Rbar ε : Subgroup 𝕊) := hρ₀'
    have hmem : (psi L ε ρ₁')⁻¹ * ρ * psi L ε ρ₁' ∈ (h.Rbar ε : Subgroup 𝕊) :=
      mul_mem (mul_mem (inv_mem hψ) hρ) hψ
    rw [hy, actG_mul ε (mul_mem heN hrN) (inv_mem hρ₁N), actG_mul ε heN hrN,
      actG_inv ε hρ₁N, actG_of_mem_self ε hρ₁L]
    simp only [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [show (⟨ρ₁, hρ₁L⟩ : L) = ρ₁' from rfl, map_inv]
    rw [hrfix _ hmem, hact _ hmem]
    group
  have hyR := (h.actG_fix_iff ε hyS).mp hyfix
  have hzt : z ∈ (Q ⊔ zpowers r) ⊔ (conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) :=
    mem_sup_left (mem_sup_left h.zQ)
  have htH : t ∈ (Q ⊔ zpowers r) ⊔ (conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) := by
    refine mem_sup_right (mem_sup_left ?_)
    rw [mem_conjugate_iff, inv_inv, ← hz]
    exact h.zQ
  have hrH : r ∈ (Q ⊔ zpowers r) ⊔ (conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) :=
    mem_sup_left (mem_sup_right (mem_zpowers r))
  have hρ₁H := h.R_le_H ε hD hsN hss hRs hz hr hr2 hrlin hρ₁R
  have he : e = y * ρ₁ * r⁻¹ := by rw [hy]; group
  rw [he]
  refine mul_mem (mul_mem ?_ hρ₁H) (inv_mem hrH)
  have hqH : ∀ q ∈ Q, q ∈ (Q ⊔ zpowers r) ⊔ (conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) :=
    fun q hq => mem_sup_left (mem_sup_left hq)
  rcases h.mem_Q_mul_of_centralizes_R ε hD hrS hr2 hrlin hrR hyS hyR with h1 | h1 | h1 | h1
  · exact hqH y h1
  · rw [show y = (y * t) * t⁻¹ by group]
    exact mul_mem (hqH _ h1) (inv_mem htH)
  · rw [show y = (y * r) * r⁻¹ by group]
    exact mul_mem (hqH _ h1) (inv_mem hrH)
  · rw [show y = (y * r * t) * t⁻¹ * r⁻¹ by group]
    exact mul_mem (mul_mem (hqH _ h1) (inv_mem htH)) (inv_mem hrH)

end Sec5

end CFSG.ComponentClassification.Foote5
