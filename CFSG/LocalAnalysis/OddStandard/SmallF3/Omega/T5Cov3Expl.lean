module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Equiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem covModelI4_signChange_three (hQ : Q.Nondegenerate) {c : ZMod 3}
    (fr : NFrame Q (Fin 6) c) : CovModelI4 hQ (fr.signChange {0, 1, 2}) := by
  classical
  let H : Subgroup (OGroup Q) :=
    omegaGroup hQ ⊓ Subgroup.centralizer ({fr.signChange {0, 1, 2}} : Set (OGroup Q))
  have hmemH : ∀ {x : OGroup Q}, x ∈ omegaGroup hQ →
      x * fr.signChange {0, 1, 2} = fr.signChange {0, 1, 2} * x → x ∈ H := by
    intro x hx hxc
    exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxc⟩
  have hσ1_3 : (c[0, 1, 2] : Equiv.Perm (Fin 6)) ^ 3 = 1 := by decide
  have hσ1_fix : ({0, 1, 2} : Finset (Fin 6)).map
      (c[0, 1, 2] : Equiv.Perm (Fin 6)).toEmbedding = {0, 1, 2} := by decide
  have hσ1_t : symmDiff ({0, 1} : Finset (Fin 6))
      (({0, 1} : Finset (Fin 6)).map (c[0, 1, 2] : Equiv.Perm (Fin 6)).toEmbedding) =
      (({0, 1} : Finset (Fin 6)).map
        (c[0, 1, 2] : Equiv.Perm (Fin 6)).toEmbedding).map
        (c[0, 1, 2] : Equiv.Perm (Fin 6)).toEmbedding := by decide
  have hσ1_alt : (c[0, 1, 2] : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hσ2_3 : (c[3, 4, 5] : Equiv.Perm (Fin 6)) ^ 3 = 1 := by decide
  have hσ2_fix : ({0, 1, 2} : Finset (Fin 6)).map
      (c[3, 4, 5] : Equiv.Perm (Fin 6)).toEmbedding = {0, 1, 2} := by decide
  have hσ2_t : symmDiff ({3, 4} : Finset (Fin 6))
      (({3, 4} : Finset (Fin 6)).map (c[3, 4, 5] : Equiv.Perm (Fin 6)).toEmbedding) =
      (({3, 4} : Finset (Fin 6)).map
        (c[3, 4, 5] : Equiv.Perm (Fin 6)).toEmbedding).map
        (c[3, 4, 5] : Equiv.Perm (Fin 6)).toEmbedding := by decide
  have hσ2_alt : (c[3, 4, 5] : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hσρ_alt : (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hσρ_map : ({0, 1, 2} : Finset (Fin 6)).map
      (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4).toEmbedding = {2, 3, 4} := by decide
  have hmm : symmDiff ({0, 1, 3, 4} : Finset (Fin 6)) {0, 1, 2} = {2, 3, 4} := by decide
  have hmm2 : symmDiff ({0, 1} : Finset (Fin 6)) {3, 4} = {0, 1, 3, 4} := by decide
  have hcard4 : ({0, 1, 3, 4} : Finset (Fin 6)).card = 4 := by decide
  have hp1 : fr.permOrth (c[0, 1, 2] : Equiv.Perm (Fin 6)) ∈ H :=
    hmemH (fr.permOrth_mem_omegaGroup hQ hσ1_alt) (fr.permOrth_comm_signChange hσ1_fix)
  have hp2 : fr.permOrth (c[3, 4, 5] : Equiv.Perm (Fin 6)) ∈ H :=
    hmemH (fr.permOrth_mem_omegaGroup hQ hσ2_alt) (fr.permOrth_comm_signChange hσ2_fix)
  have ht01 : fr.signChange ({0, 1} : Finset (Fin 6)) ∈ H :=
    hmemH (fr.signChange_mem_omegaGroup hQ {0, 1} (by decide))
      (fr.signChange_comm {0, 1} {0, 1, 2})
  have ht34 : fr.signChange ({3, 4} : Finset (Fin 6)) ∈ H :=
    hmemH (fr.signChange_mem_omegaGroup hQ {3, 4} (by decide))
      (fr.signChange_comm {3, 4} {0, 1, 2})
  have ht01' : fr.signChange ({0, 1} : Finset (Fin 6)) ∈ twoRes H :=
    fr.signChange_mem_twoRes (H := H) hσ1_3 hp1 ht01 hσ1_t
  have ht34' : fr.signChange ({3, 4} : Finset (Fin 6)) ∈ twoRes H :=
    fr.signChange_mem_twoRes (H := H) hσ2_3 hp2 ht34 hσ2_t
  let w : OGroup Q := fr.signChange ({0, 1} : Finset (Fin 6)) * fr.signChange {3, 4}
  have hw_eq : w = fr.signChange ({0, 1, 3, 4} : Finset (Fin 6)) := by
    dsimp only [w]
    rw [fr.signChange_mul, hmm2]
  have hw_mem : w ∈ twoRes H := by
    have h : fr.signChange ({0, 1} : Finset (Fin 6)) * fr.signChange {3, 4} ∈ twoRes H :=
      (twoRes H).mul_mem ht01' ht34'
    rw [fr.signChange_mul, hmm2] at h
    rwa [hw_eq]
  have hw_sq : w * w = 1 := by
    rw [hw_eq, fr.signChange_mul_self]
  have hw_type : invType w = (4, 1) := by
    rw [hw_eq, fr.invType_signChange hQ ({0, 1, 3, 4} : Finset (Fin 6)) (by decide), hcard4]
    decide
  have hρ_conj : fr.permOrth (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4) *
      fr.signChange {0, 1, 2} *
      (fr.permOrth (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4))⁻¹ =
      w * fr.signChange {0, 1, 2} := by
    rw [fr.permOrth_conj_signChange (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4) {0, 1, 2},
      hσρ_map, hw_eq, fr.signChange_mul, hmm]
  unfold CovModelI4
  exact ⟨w, hw_mem, hw_sq, hw_type,
    fr.permOrth (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4),
    fr.permOrth_mem_omegaGroup hQ hσρ_alt, hρ_conj⟩

end CFSG.OddStandard.SmallF3.Omega
