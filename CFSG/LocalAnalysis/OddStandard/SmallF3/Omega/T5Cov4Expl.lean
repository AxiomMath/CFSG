module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def NFrame.complexStructure {c : ZMod 3} (fr : NFrame Q (Fin 6) c) :
    OGroup Q :=
  fr.signChange {0, 2, 4} * fr.permOrth (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5)

theorem NFrame.complexStructure_mul_self {c : ZMod 3} (fr : NFrame Q (Fin 6) c) :
    fr.complexStructure * fr.complexStructure = piOrth Q := by
  unfold NFrame.complexStructure
  set π₀ : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 with hπ₀
  have hPP : fr.permOrth π₀ * fr.permOrth π₀ = 1 := by
    rw [← fr.permOrth_mul, show π₀ * π₀ = 1 by rw [hπ₀]; decide, fr.permOrth_one]
  have hmap : ({0, 2, 4} : Finset (Fin 6)).map π₀.toEmbedding = {1, 3, 5} := by
    rw [hπ₀]; decide
  have hsd : symmDiff ({0, 2, 4} : Finset (Fin 6)) {1, 3, 5} = Finset.univ := by decide
  calc fr.signChange {0, 2, 4} * fr.permOrth π₀ * (fr.signChange {0, 2, 4} * fr.permOrth π₀)
      = fr.signChange {0, 2, 4} * (fr.permOrth π₀ * fr.signChange {0, 2, 4}) *
          fr.permOrth π₀ := by group
    _ = fr.signChange {0, 2, 4} * (fr.signChange {1, 3, 5} * fr.permOrth π₀) *
          fr.permOrth π₀ := by rw [fr.permOrth_mul_signChange, hmap]
    _ = (fr.signChange {0, 2, 4} * fr.signChange {1, 3, 5}) *
          (fr.permOrth π₀ * fr.permOrth π₀) := by group
    _ = piOrth Q := by rw [hPP, mul_one, fr.signChange_mul, hsd, fr.signChange_univ]

open Equiv in
theorem covModelI4_complexStructure (hQ : Q.Nondegenerate) {c : ZMod 3}
    (fr : NFrame Q (Fin 6) c) : CovModelI4 hQ fr.complexStructure := by
  set π₀ : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 with hπ₀
  set στ : Equiv.Perm (Fin 6) := c[0, 2, 4] * c[1, 3, 5] with hστ
  have hp : fr.complexStructure = fr.signChange {0, 2, 4} * fr.permOrth π₀ := rfl
  set p := fr.complexStructure with hpdef
  have hDfix : ({0, 1, 2, 3} : Finset (Fin 6)).map π₀.toEmbedding = {0, 1, 2, 3} := by
    rw [hπ₀]; decide
  have hAfix : ({0, 2, 4} : Finset (Fin 6)).map στ.toEmbedding = {0, 2, 4} := by
    rw [hστ]; decide
  have hEmap : ({1, 3} : Finset (Fin 6)).map π₀.toEmbedding = {0, 2} := by
    rw [hπ₀]; decide
  have hcomm_τπ : στ * π₀ = π₀ * στ := by rw [hστ, hπ₀]; decide
  have hστ3 : στ ^ 3 = 1 := by rw [hστ]; decide
  have hστalt : στ ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, hστ]; decide
  have hDcomm : p * fr.signChange {0, 1, 2, 3} = fr.signChange {0, 1, 2, 3} * p := by
    rw [hp]
    calc fr.signChange {0, 2, 4} * fr.permOrth π₀ * fr.signChange {0, 1, 2, 3}
        = fr.signChange {0, 2, 4} * (fr.permOrth π₀ * fr.signChange {0, 1, 2, 3}) := by
          rw [mul_assoc]
      _ = fr.signChange {0, 2, 4} * (fr.signChange {0, 1, 2, 3} * fr.permOrth π₀) := by
          rw [fr.permOrth_comm_signChange hDfix]
      _ = fr.signChange {0, 2, 4} * fr.signChange {0, 1, 2, 3} * fr.permOrth π₀ := by
          rw [mul_assoc]
      _ = fr.signChange {0, 1, 2, 3} * fr.signChange {0, 2, 4} * fr.permOrth π₀ := by
          rw [fr.signChange_comm]
      _ = fr.signChange {0, 1, 2, 3} * (fr.signChange {0, 2, 4} * fr.permOrth π₀) := by
          rw [mul_assoc]
  have hτcomm : p * fr.permOrth στ = fr.permOrth στ * p := by
    rw [hp]
    calc fr.signChange {0, 2, 4} * fr.permOrth π₀ * fr.permOrth στ
        = fr.signChange {0, 2, 4} * fr.permOrth (π₀ * στ) := by
          rw [mul_assoc, fr.permOrth_mul π₀ στ]
      _ = fr.signChange {0, 2, 4} * fr.permOrth (στ * π₀) := by rw [hcomm_τπ]
      _ = fr.signChange {0, 2, 4} * (fr.permOrth στ * fr.permOrth π₀) := by
          rw [fr.permOrth_mul στ π₀]
      _ = (fr.signChange {0, 2, 4} * fr.permOrth στ) * fr.permOrth π₀ := by rw [mul_assoc]
      _ = (fr.permOrth στ * fr.signChange {0, 2, 4}) * fr.permOrth π₀ := by
          rw [← fr.permOrth_comm_signChange hAfix]
      _ = fr.permOrth στ * (fr.signChange {0, 2, 4} * fr.permOrth π₀) := by rw [mul_assoc]
  have hDH : fr.signChange {0, 1, 2, 3} ∈
      omegaGroup hQ ⊓ Subgroup.centralizer ({p} : Set (OGroup Q)) := by
    refine Subgroup.mem_inf.mpr ⟨fr.signChange_mem_omegaGroup hQ _ (by decide), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hDcomm
  have hτH : fr.permOrth στ ∈ omegaGroup hQ ⊓ Subgroup.centralizer ({p} : Set (OGroup Q)) := by
    refine Subgroup.mem_inf.mpr ⟨fr.permOrth_mem_omegaGroup hQ hστalt, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hτcomm
  have hDtwo : fr.signChange {0, 1, 2, 3} ∈
      twoRes (omegaGroup hQ ⊓ Subgroup.centralizer ({p} : Set (OGroup Q))) :=
    fr.signChange_mem_twoRes hστ3 hτH hDH (by rw [hστ]; decide)
  have hinv : invType (fr.signChange {0, 1, 2, 3}) = (4, 1) := by
    have h := fr.invType_signChange hQ {0, 1, 2, 3} (by decide)
    have hcard : ({0, 1, 2, 3} : Finset (Fin 6)).card = 4 := by decide
    rw [hcard] at h
    simpa using h
  have hE2 : fr.signChange {1, 3} * fr.signChange {1, 3} = 1 := fr.signChange_mul_self _
  have hEinv : (fr.signChange {1, 3})⁻¹ = fr.signChange {1, 3} := inv_eq_of_mul_eq_one_right hE2
  have hsd : symmDiff (symmDiff ({1, 3} : Finset (Fin 6)) {0, 2, 4}) {0, 2} =
      symmDiff ({0, 1, 2, 3} : Finset (Fin 6)) {0, 2, 4} := by decide
  have hconj : fr.signChange {1, 3} * p * (fr.signChange {1, 3})⁻¹ =
      fr.signChange {0, 1, 2, 3} * p := by
    rw [hEinv, hp]
    calc fr.signChange {1, 3} * (fr.signChange {0, 2, 4} * fr.permOrth π₀) *
          fr.signChange {1, 3}
        = fr.signChange {1, 3} * fr.signChange {0, 2, 4} *
          (fr.permOrth π₀ * fr.signChange {1, 3}) := by group
      _ = fr.signChange {1, 3} * fr.signChange {0, 2, 4} *
          (fr.signChange {0, 2} * fr.permOrth π₀) := by
          rw [fr.permOrth_mul_signChange, hEmap]
      _ = (fr.signChange {1, 3} * fr.signChange {0, 2, 4} * fr.signChange {0, 2}) *
          fr.permOrth π₀ := by group
      _ = fr.signChange (symmDiff (symmDiff {1, 3} {0, 2, 4}) {0, 2}) * fr.permOrth π₀ := by
          rw [fr.signChange_mul, fr.signChange_mul]
      _ = fr.signChange {0, 1, 2, 3} * fr.signChange {0, 2, 4} * fr.permOrth π₀ := by
          rw [hsd, ← fr.signChange_mul]
      _ = fr.signChange {0, 1, 2, 3} * (fr.signChange {0, 2, 4} * fr.permOrth π₀) := by group
  exact ⟨fr.signChange {0, 1, 2, 3}, hDtwo, fr.signChange_mul_self _, hinv,
    fr.signChange {1, 3}, fr.signChange_mem_omegaGroup hQ _ (by decide), hconj⟩

end CFSG.OddStandard.SmallF3.Omega
