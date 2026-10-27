module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fk_fr_exists_nframe (hdim : Module.finrank (ZMod 3) V = 6) {c : ZMod 3} (hc : c ≠ 0)
    (v : Fin 6 → V) (hv : ∀ i, Q (v i) = c)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i) (v j) = 0) :
    ∃ fr : NFrame Q (Fin 6) c, ∀ i, fr.b i = v i := by
  have hli : LinearIndependent (ZMod 3) v := by
    refine LinearMap.linearIndependent_of_isOrthoᵢ (B := QuadraticMap.associated Q) ?_ ?_
    · rw [LinearMap.isOrthoᵢ_def]
      intro i j hij
      rw [QuadraticMap.associated_isOrtho]
      exact (QuadraticMap.isOrtho_polarBilin (Q := Q)).mp
        (by rw [QuadraticMap.polarBilin_apply_apply]; exact horth i j hij)
    · intro i
      rw [QuadraticMap.associated_eq_self_apply (S := ZMod 3), hv i]
      exact hc
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdim])
  have hB : ∀ i, B i = v i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact ⟨{ b := B, norm := fun i => by rw [hB i, hv i],
           orth := fun i j hij => by rw [hB i, hB j, horth i j hij] }, hB⟩

end CFSG.OddStandard.SmallF3.Omega
