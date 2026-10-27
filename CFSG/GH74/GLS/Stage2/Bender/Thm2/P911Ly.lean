module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Spor
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Ly

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (LyAllInner)

@[expose] def LyInvolOddCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .Ly → ∀ t : X, orderOf t = 2 →
    CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥

theorem no911_ly (hA : LyAllInner) (hB : LyInvolOddCore) {Y : Type} [Group Y] [Finite Y]
    (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h : NativeSporadic.IsSporadic Y .Ly) : No911 Y := by
  refine no911_of_oddCore hs hna fun X _ _ S _ hSY hC t ht => ?_
  obtain ⟨ψ⟩ := hSY
  obtain ⟨e⟩ := h
  have hSly : NativeSporadic.IsSporadic S .Ly := ⟨ψ.trans e⟩
  have hSX : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨s, hs'⟩ := hA S hSly (MulAut.conjNormal x)
    have hcomm : ∀ y : S, (x : X) * (y : X) * x⁻¹ = (s : X) * (y : X) * (s : X)⁻¹ := by
      intro y
      have := congrArg (fun φ : MulAut S => ((φ y : S) : X)) hs'
      simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using this
    have hmem : (s : X)⁻¹ * x ∈ centralizer (S : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hcomm ⟨y, hy⟩
      calc y * ((s : X)⁻¹ * x) = (s : X)⁻¹ * ((s : X) * y * (s : X)⁻¹) * x := by group
        _ = (s : X)⁻¹ * (x * y * x⁻¹) * x := by rw [← this]
        _ = (s : X)⁻¹ * x * y := by group
    rw [hC, Subgroup.mem_bot] at hmem
    have : x = s := by
      have h1 : (s : X)⁻¹ * x = 1 := hmem
      exact (inv_mul_eq_one.mp h1).symm
    rw [this]
    exact s.2
  let eX : X ≃* S := (Subgroup.topEquiv (G := X)).symm.trans (MulEquiv.subgroupCongr hSX.symm)
  exact hB X ⟨(eX.trans ψ).trans e⟩ t ht

theorem core911_mcly
    (hA : LyAllInner) (hB : LyInvolOddCore) : Core911McLy := by
  intro Y _ _ hs hna h
  rcases h with h | h
  · exact no911_mcl hs hna h
  · exact no911_ly hA hB hs hna h

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
