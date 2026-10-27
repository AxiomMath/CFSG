module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4SlpPrefixData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Fix11
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A CFSG.Quasithin.J4M2
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def slpRegs (prog : List Instr) : ℕ → J := runProg (initRegs a b) prog

@[expose] def slpRegsN (n : ℕ) (prog : List Instr) : Array Pair :=
  runProgN O (initRegsN O n An Bn) prog

theorem regsRep_prog {prog : List Instr} {n : ℕ}
    (h : prog.all (Instr.lt n) = true) : RegsRep Sp φ n (slpRegs prog) (slpRegsN n prog) :=
  regsRep_runProg prog h (regsRep_initRegs (rep_a matFacts) (rep_b matFacts))

theorem rep_slpRegs {prog : List Instr} {n : ℕ}
    (h : prog.all (Instr.lt n) = true) {r : ℕ} (hr : r < n) :
    Rep Sp φ (slpRegs prog r) (slpRegsN n prog)[r]! :=
  (regsRep_prog h).2 r hr

theorem ne_of_neOK {X Y : Array ℕ} (hX : Sp.WF X) (hY : Sp.WF Y) (h : neOK X Y = true) :
    Sp.toMat X ≠ Sp.toMat Y := by
  unfold neOK at h
  rw [List.any_eq_true] at h
  obtain ⟨t, -, ht⟩ := h
  intro e
  have h1 := Sp.toVec_ne ht
  rw [Sp.toVec_vmul trivial hX, Sp.toVec_vmul trivial hY, e] at h1
  exact h1 rfl

theorem rep_cE_of
    (h : cEOK = true) : Rep Sp φ cE cEP := by
  unfold cEOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hMat : cMat = pairRows cEP := by
    refine Array.ext (by rw [h1]; simp [pairRows, cEP, h2]) fun i hi _ => ?_
    have hi' : i < 112 := by rwa [h1] at hi
    have e := V2.beq_iff.1 (h3 i hi')
    rw [getElem!_pos _ i (by omega)] at e
    have hg : i < cEr.size := by omega
    rw [getElem!_pos cEr i hg] at e
    simpa [pairRows, cEP] using e
  have hz : Sp.toMat cEr = φ cE := by
    have := Mx_cE matFacts
    rw [hMat, rowsMatrix_pairRows] at this
    exact this.symm
  have hwf : Sp.WF cEr := h2
  have hwf2 : Sp.WF (O.mul cEr cEr) := Sp.mul_wf hwf hwf
  have hcube : φ cE * (φ cE * φ cE) = 1 := by
    have e := Sp.toMat_eq (Sp.mul_wf hwf hwf2) Sp.one_wf h4
    rwa [Sp.toMat_mul hwf hwf2, Sp.toMat_mul hwf hwf, Sp.toMat_one, hz] at e
  have hinv : cE⁻¹ = cE * cE := by
    refine inv_eq_of_mul_eq_one_right (φ_injective ?_)
    rw [map_mul, map_mul, map_one]
    exact hcube
  refine ⟨hwf, hwf2, hz, ?_⟩
  rw [hinv, map_mul]
  change Sp.toMat (O.mul cEr cEr) = _
  rw [Sp.toMat_mul hwf hwf, hz]

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
