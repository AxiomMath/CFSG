module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinGen
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinV
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinNC
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinCtx
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Rows

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

section Models

variable {p e : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem one_le_of_five_le_pow {q : ℕ} (hq : 5 ≤ p ^ q) : 1 ≤ q := by
  rcases Nat.eq_zero_or_pos q with rfl | h
  · simp at hq
  · exact h

theorem forall_large_of_ctx {P : StatedLieTag → LieUniversal → Prop}
    (h : ∀ (t : StatedLieTag) {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
      {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)},
      SpinCtx t Q D → P t ⟨spinGroup Q, D⟩)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (tY : StatedLieTag) (nY : ℕ) (hrow : TwinRow.large tY nY) :
    P tY (modelUniv tY nY p e Fact.out) := by
  have hp : p.Prime := Fact.out
  have he : 1 ≤ e := one_le_of_five_le_pow hq
  rcases hrow with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  ·
    have hn3 : 3 ≤ nY := by omega
    have hadm : StatedLieAdmissible .POmegaPlus nY p e := ⟨hp, he, by omega⟩
    have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus nY (GaloisField p e)),
        plusDatum nY (GaloisField p e) hn3⟩ → P .POmegaPlus M := by
      intro M hM
      subst hM
      exact h _ (spinCtx_plus hp2 hq hn hn3 hadm)
    exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3)
  ·
    have hadm : StatedLieAdmissible .POmegaMinus nY p e := ⟨hp, he, by omega⟩
    show P .POmegaMinus ⟨spinGroup (quadMinus nY (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2), Twisted.minusDatum nY (minusCoeffs_irr p e)⟩
    exact h _ (spinCtx_minus hp2 hq hn hadm)
  ·
    have hadm : StatedLieAdmissible .POmegaOdd nY p e := ⟨hp, he, by omega, hp2⟩
    show P .POmegaOdd ⟨spinGroup (quadOdd nY (GaloisField p e)), oddDatum nY (GaloisField p e)⟩
    exact h _ (spinCtx_odd hp2 hq hn hadm)

theorem twinMFGenerationOn_of_ctx {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type}
    [Fintype ι] {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}
    (c : SpinCtx t Q D) : TwinMFGenerationOn t ⟨spinGroup Q, D⟩ := by
  have := c.perfect
  classical
  exact twinMFGenerationOn_of_spin c.hodd c.h5 c.hQ c.hrange c.hZ (by have := c.hV; omega) c.hproj
    D c.hcorr c.hperf c.hnc

theorem twinMFCentralizingOn_of_ctx {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type}
    [Fintype ι] {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}
    (c : SpinCtx t Q D) : TwinMFCentralizingOn t ⟨spinGroup Q, D⟩ := by
  have := c.perfect
  classical
  exact twinMFCentralizingOn_of_spin c.hodd c.h5 c.hQ c.hrange c.hZ c.hV c.hproj D c.hcorr
    c.hperf c.hnc

theorem twinMFCommutantOn_of_ctx {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type}
    [Fintype ι] {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}
    (c : SpinCtx t Q D) : TwinMFCommutantOn t ⟨spinGroup Q, D⟩ := by
  have := c.perfect
  classical
  exact twinMFCommutantOn_of_spin c.hodd c.hQ c.hrange c.hZ c.hV c.hproj D c.hcorr c.hsurj
    c.hperf c.hnc

theorem twinMFGeneration_large (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (tY : StatedLieTag) (nY : ℕ)
    (hrow : TwinRow.large tY nY) : TwinMFGeneration p e tY nY :=
  twinMFGeneration_of_on (forall_large_of_ctx
    (P := fun t M => TwinMFGenerationOn t M)
    (fun _ _ => twinMFGenerationOn_of_ctx) hp2 hq tY nY hrow)

theorem twinMFCentralizing_large (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (tY : StatedLieTag) (nY : ℕ)
    (hrow : TwinRow.large tY nY) : TwinMFCentralizing p e tY nY :=
  twinMFCentralizing_of_on (forall_large_of_ctx
    (P := fun t M => TwinMFCentralizingOn t M)
    (fun _ _ => twinMFCentralizingOn_of_ctx) hp2 hq tY nY hrow)

theorem twinMFCommutant_large (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (tY : StatedLieTag) (nY : ℕ)
    (hrow : TwinRow.large tY nY) : TwinMFCommutant p e tY nY :=
  twinMFCommutant_of_on (forall_large_of_ctx
    (P := fun t M => TwinMFCommutantOn t M)
    (fun _ _ => twinMFCommutantOn_of_ctx) hp2 hq tY nY hrow)

end Models

end CFSG.ClassicalInvolution.RouteD.TwinY
