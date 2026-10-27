module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three3
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block
public import CFSG.RankThree.Lattice.SteinbergBIRoots
public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley

section Certs


@[expose] def e8A2Roots : Set (Fin Tag.E8.rank → ℤ) :=
  {α | α = Pi.single (0 : Fin Tag.E8.rank) 1 ∨
    α = -Pi.single (0 : Fin Tag.E8.rank) 1 ∨
    α = ![0, 1, 1, 2, 2, 2, 1, 1] ∨ α = -![0, 1, 1, 2, 2, 2, 1, 1] ∨
    α = ![-1, -1, -1, -2, -2, -2, -1, -1] ∨
    α = -![-1, -1, -1, -2, -2, -2, -1, -1]}

private lemma zmod_intCast_ne_zero_of_lt {p k : ℕ} (hk : 0 < k)
    (hkp : k < p) : ((k : ℤ) : ZMod p) ≠ 0 := by
  intro hz
  have hd : (p : ℤ) ∣ (k : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (k : ℤ) p).1 hz
  have hle : (p : ℤ) ≤ (k : ℤ) := Int.le_of_dvd (by exact_mod_cast hk) hd
  omega

theorem e8_eq_zero_of_charVal_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0)
    {A D : ℤ} (hAD : A * A - A * D + D * D ∈ ({0, 1, 3, 4} : Finset ℤ))
    (h : (A : ZMod p) + (ε : ZMod p) * q * (D : ZMod p) = 0) : A = 0 ∧ D = 0 := by
  have hcast : ((A * A - A * D + D * D : ℤ) : ZMod p) = 0 := by
    rw [← e8T3_norm_identity hε hq A D, h, zero_mul]
  have hpne : p ≠ 4 := by intro h4; rw [h4] at hp; norm_num at hp
  have hp4 : 4 < p := lt_of_le_of_ne (Nat.succ_le_of_lt hp3) (Ne.symm hpne)
  have hk1 : ((1 : ℤ) : ZMod p) ≠ 0 :=
    zmod_intCast_ne_zero_of_lt (by norm_num) (lt_trans (by norm_num) hp3)
  have hk3 : ((3 : ℤ) : ZMod p) ≠ 0 := zmod_intCast_ne_zero_of_lt (by norm_num) hp3
  have hk4 : ((4 : ℤ) : ZMod p) ≠ 0 := zmod_intCast_ne_zero_of_lt (by norm_num) hp4
  have hnorm : A * A - A * D + D * D = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hAD
    rcases hAD with h0 | h1 | h3 | h4
    · exact h0
    · exact absurd (h1 ▸ hcast) hk1
    · exact absurd (h3 ▸ hcast) hk3
    · exact absurd (h4 ▸ hcast) hk4
  have h4eq : 4 * (A * A - A * D + D * D) = (2 * A - D) ^ 2 + 3 * D ^ 2 := by ring
  have hD : D = 0 := by nlinarith [sq_nonneg (2 * A - D), sq_nonneg D]
  have hA : A = 0 := by nlinarith
  exact ⟨hA, hD⟩

theorem rootKernel_e8T3XColumn {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    rootKernel (e8T3XColumn ε q) = e8T3XKernel := by
  ext α
  rw [mem_rootKernel]
  constructor
  · rintro ⟨hα, h0⟩
    have hnorm := e8T3XA_norm_mem (List.ofFn α) (isRoot_iff_mem_artifactRoots.1 hα)
    rw [toVec_ofFn] at hnorm
    have hnorm' : e8T3XA α * e8T3XA α - e8T3XA α * e8T3XD α + e8T3XD α * e8T3XD α ∈
        ({0, 1, 3} : Finset ℤ) := hnorm
    have hAD : e8T3XA α * e8T3XA α - e8T3XA α * e8T3XD α + e8T3XD α * e8T3XD α ∈
        ({0, 1, 3, 4} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hnorm' ⊢
      tauto
    have hzero : (e8T3XA α : ZMod p) + (ε : ZMod p) * q * (e8T3XD α : ZMod p) = 0 := by
      rw [← charVal_e8T3XColumn α]; exact h0
    obtain ⟨hA, hD⟩ := e8_eq_zero_of_charVal_zero hp hp3 hε hq hAD hzero
    have hA' : α 3 - 2 * α 4 + α 5 = 0 := by simpa [e8T3XA] using hA
    have hD' : -α 4 + α 5 = 0 := by simpa [e8T3XD] using hD
    refine ⟨hα, ?_, ?_⟩ <;> omega
  · rintro ⟨hα, h1, h2⟩
    refine ⟨hα, ?_⟩
    rw [charVal_e8T3XColumn]
    have hA : e8T3XA α = 0 := by show α 3 - 2 * α 4 + α 5 = 0; omega
    have hD : e8T3XD α = 0 := by show -α 4 + α 5 = 0; omega
    rw [hA, hD]; simp

theorem rootKernel_e8T3ZColumn {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    rootKernel (e8T3ZColumn ε q) = e8T3ZKernel := by
  ext α
  rw [mem_rootKernel]
  constructor
  · rintro ⟨hα, h0⟩
    have hnorm := e8T3ZA_norm_mem (List.ofFn α) (isRoot_iff_mem_artifactRoots.1 hα)
    rw [toVec_ofFn] at hnorm
    have hzero : (e8T3ZA α : ZMod p) + (ε : ZMod p) * q * (e8T3ZD α : ZMod p) = 0 := by
      rw [← charVal_e8T3ZColumn α]; exact h0
    obtain ⟨hA, hD⟩ := e8_eq_zero_of_charVal_zero hp hp3 hε hq hnorm hzero
    exact ⟨hα, hA, hD⟩
  · rintro ⟨hα, h1, h2⟩
    refine ⟨hα, ?_⟩
    rw [charVal_e8T3ZColumn]
    have hA : e8T3ZA α = 0 := by show α 2 - 2 * α 4 + α 5 + α 6 = 0; omega
    have hD : e8T3ZD α = 0 := by show -α 4 + α 6 + α 7 = 0; omega
    rw [hA, hD]; simp

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
