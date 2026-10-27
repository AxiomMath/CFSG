module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {Y : Type} [Group Y] [Finite Y]

theorem rank23_data (hR : Rank23At Y) {K B : Subgroup Y} (h : KHyp 3 K B)
    (hlist : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isList94) :
    Subgroup.center (PQuot 3 K) = ⊥ ∧ Subgroup.center ↥K = ⊥ ∧
      ∀ E T : Subgroup Y, E ≤ K → IsElemAbelian 3 E → T ≤ K → IsPGroup 2 T → T ≠ ⊥ →
        E ≤ Subgroup.normalizer (T : Set Y) → Nat.card E ≤ 27 := by
  classical
  have hcomp : GLAPComponent 3 K K := glaPComponent_self_p h.qs h.core
  have hcatP : catalogIs (PSimple 3 K) S9.isList94 :=
    ys03_catalogIs_of_mulEquiv (pSimpleEquiv h.core).symm hlist
  obtain ⟨hZP, -, hrank⟩ := hR K K hcomp hcatP
  have e1 : PQuot 3 K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq h.core).trans QuotientGroup.quotientBot
  have hZ : Subgroup.center ↥K = ⊥ := by
    rw [← Subgroup.map_center_eq e1, hZP, Subgroup.map_bot]
  refine ⟨hZP, hZ, fun E T hEK hE hTK hT2 hTne hET => ?_⟩
  have hTO : ¬ T ≤ GLAPPrimeCoreOf 3 K := by
    rw [glaPPrimeCoreOf_eq_bot_p h.core]
    exact fun hle => hTne (le_bot_iff.1 hle)
  exact (hrank E T hEK hE hTK hT2 hTO hET).1

theorem hin_of_cube_inner {K B : Subgroup Y} (h : KHyp 3 K B)
    (hout : ∀ α : MulAut (PQuot 3 K), α ^ 3 = 1 → α ∈ inner (PQuot 3 K)) :
    ∀ b ∈ B, ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹ := by
  intro b hb
  have hbN : b⁻¹ ∈ Subgroup.normalizer (K : Set Y) :=
    Subgroup.normalizer_eq_top_iff.2 h.normal ▸ Subgroup.mem_top _
  have hb3 : (b⁻¹) ^ 3 = 1 := by
    rw [inv_pow, h.elem.2 b hb, inv_one]
  have hind : InducesInnerMod 3 K b⁻¹ :=
    inducesInnerMod_of_inner hbN (hout _ (barAut_pow_three K b⁻¹ hbN hb3))
  obtain ⟨l, hlK, hl⟩ := hind
  refine ⟨l⁻¹, K.inv_mem hlK, fun x hx => ?_⟩
  have := hl x hx
  rw [glaPPrimeCoreOf_eq_bot_p h.core, Subgroup.mem_bot] at this
  have h2 : b * x * b⁻¹ = l⁻¹ * x * l := by
    have h3 : (l⁻¹ * x * l)⁻¹ * (b⁻¹⁻¹ * x * b⁻¹) = 1 := by simpa using this
    have h4 : b⁻¹⁻¹ * x * b⁻¹ = l⁻¹ * x * l := by
      have := inv_mul_eq_one.1 h3
      exact this.symm
    simpa using h4
  simpa using h2

noncomputable def mulEquivQuotCenter {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) :
    K ≃* K ⧸ Subgroup.center K :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

theorem forall_cube_inner_of_catalog {K B : Subgroup Y} (h : KHyp 3 K B)
    (hZP : Subgroup.center (PQuot 3 K) = ⊥) {P : TauCeti.CFSGIndex → Prop}
    (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) P)
    (hOut : ∀ (S : Type) [Group S], catalogIs S P → ¬ 3 ∣ Nat.card (Outer S)) :
    ∀ α : MulAut (PQuot 3 K), α ^ 3 = 1 → α ∈ inner (PQuot 3 K) := by
  have hcatP : catalogIs (PSimple 3 K) P :=
    ys03_catalogIs_of_mulEquiv (pSimpleEquiv h.core).symm hcat
  have eZ : PSimple 3 K ≃* PQuot 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hZP).trans QuotientGroup.quotientBot
  have hcatQ : catalogIs (PQuot 3 K) P := ys03_catalogIs_of_mulEquiv eZ hcatP
  exact fun α hα => forall_cube_inner_of_card_outer (hOut _ hcatQ) α hα

end CFSG.LocalAnalysis.GLTheoremA
