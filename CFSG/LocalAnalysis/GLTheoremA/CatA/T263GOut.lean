module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def T263NoTri : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → catalogIs (↥S ⧸ Subgroup.center ↥S) isD4any →
    GLAIsBmax 3 B →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    ∀ c ∈ B, NonInnDiag 3 c S → FieldOn 3 c S ∨ IsTD4 3 S

section Certs


theorem t263Out_of_noTri (hNT : T263NoTri) : T263Out := by
  intro p hp hp2 Ω _ _ S B hSn hSq hSp hSc hSB hB hT
  classical
  have hBel : CFSG.Open.IsElemAbelian p B := hB.1
  have eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hq : CFSG.Open.IsQuasisimple (PQuot p S) := hSq.of_mulEquiv eS
  have e₆ : PSimple p S ≃* ↥S ⧸ Subgroup.center ↥S :=
    QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)
  have hchev : IsChevSimple 2 (PSimple p S) := by
    unfold IsChevSimple at hSc ⊢
    rcases hSc with h | h
    · exact Or.inl ((catalogIs_congr e₆).2 h)
    · exact Or.inr ((catalogIs_congr e₆).2 h)
  have hcomp : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  have hAN : B ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact le_top
  have hexp : ∀ a ∈ B, a ^ p = 1 := fun a ha => hBel.2 a ha
  have hdich : T263Dich p S B := by
    intro c hc hnon
    have hcN : c ∈ Subgroup.normalizer (S : Set Ω) := hnon.1
    rcases i91_holds Ω p hp hp2 S S c hcomp hchev hcN (hexp c hc) hnon with hF | ⟨hp3, hD4 | hTD4⟩
    · exact Or.inl hF
    · subst hp3
      rcases hNT Ω S B hSn hSq hSp hSc ((catalogIs_congr e₆).1 hD4) hB hT c hc hnon with hF | hTD4
      · exact Or.inl hF
      · exact Or.inr ⟨rfl, hTD4⟩
    · exact Or.inr ⟨hp3, hTD4⟩
  obtain ⟨B₀, hB₀B, hB₀inn, hB₀idx, hB₀max⟩ := T156.t156_split hp hp2 hq hchev hAN hexp hdich
  refine ⟨B₀, ⟨hB₀B, hB₀inn, hB₀idx, hB₀max, ?_⟩, hdich⟩
  intro c hc
  apply hB₀max c hc.1
  refine MI.inner_innDiag_any hcomp hchev (hAN hc.1) ?_
  refine ⟨1, one_mem _, fun y hy => ?_⟩
  have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.1 hc.2 y hy).symm
  have : c⁻¹ * y * c = y := by rw [mul_assoc, ← hcy]; group
  rw [this]
  simp only [inv_one, one_mul, mul_one, inv_mul_cancel]
  exact one_mem _

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263

end
