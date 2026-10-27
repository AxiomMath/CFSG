module

public import CFSG.LieType.SpecialLinear.SLModel.CoverType.Hecke

public section

namespace CFSG.LieType.SpecialLinear.SLModel

open Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.SpecialLinear
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Universal.Unitary CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

theorem isCoverType_slModelRep (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) :
    IsCoverType (rankOne m F 2) (slModelRep (F := F) (k := k) ε) (bTop ε)
      (slChiEps m (algebraMap F k) ε)
      (Finset.univ.filter fun s : Fin m => bR0 ε s = ∅) := by
  classical
  refine ⟨bTop_mem_fixU ε, bTop_ne_zero (k := k) ε, ?_, ?_⟩
  · intro h hh
    exact slModelRep_torus (F := F) (k := k) ε h (by simpa using hh)
  · intro s
    constructor
    · intro hs
      rw [Finset.mem_filter] at hs
      obtain ⟨-, h0⟩ := hs
      refine ⟨?_, ?_⟩
      · intro u
        rw [show (rankOne m F 2).hh s u = hdiag m F s u from rfl, slChiEps_hdiag]
        have hd0 : bDigit ε s.succ = 0 := by
          rw [bDigit_eq_zero_iff]
          intro r hmem
          have hr : r ∈ bR0 ε s := by
            rw [bR0]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
          rw [h0] at hr
          simp at hr
        rw [hd0, pow_zero]
      · rw [coverId_datum_heckeT_eq]
        exact heckeT_bTop_eq_zero (k := k) hF ε s h0
    · intro hcon
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra h0
      by_cases hU : bR0 ε s = Finset.univ
      · have hT := heckeT_bTop_eq_self (k := k) hF ε s hU
        rw [← coverId_datum_heckeT_eq] at hT
        rw [hT] at hcon
        exact bTop_ne_zero (k := k) ε hcon.2
      · have hd : bDigit ε s.succ ≠ 0 := by
          intro hd0
          apply h0
          rw [bDigit_eq_zero_iff] at hd0
          ext r
          simp [bR0, hd0 r]
        have hdt : bDigit ε s.succ ≠ 2 ^ f - 1 := by
          intro hdtop
          apply hU
          rw [bDigit_eq_iff] at hdtop
          rw [bR0]
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simp [hdtop r]
        obtain ⟨u, hu⟩ :=
          slChiEps_hh_ne_one_of_bDigit_ne_zero (k := k) hF ε s hd hdt
        exact hu (hcon.1 u)

end

end CFSG.LieType.SpecialLinear.SLModel
