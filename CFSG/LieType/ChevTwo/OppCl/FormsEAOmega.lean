module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LieType.BorelTits.OrthogonalSingular

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

variable (F : Type) [Field F] [Finite F] [CharP F 2]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : QuadForm F (ι → F))

theorem ea_Omega_aux (hι : 5 ≤ Fintype.card ι) :
    EA0 Φ.polar (fun v => Φ.Q v = 0) (natRep (StatedOmega Φ.Q)) ∧
    EA1 Φ.polar (fun v => Φ.Q v = 0) (natRep (StatedOmega Φ.Q)) ∧
    ∀ (h : StatedOmega Φ.Q) (w : ι → F),
      Φ.Q (natRep (StatedOmega Φ.Q) h w - w) = 0 →
        Φ.polar.β w (natRep (StatedOmega Φ.Q) h w - w) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy hxy
    have hx' : Φ.Q x = 0 := hx
    have hy' : Φ.Q y = 0 := hy
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler' Φ hι hx' hxy
    have hAv' : ∀ v, Matrix.mulVec (A : Matrix ι ι F) v =
        v + Φ.polar.β x v • y - Φ.polar.β y v • x := by
      intro v
      rw [hAv v, Φ.eichler_apply, hy']
      module
    refine ⟨⟨A, hA⟩, fun v => ?_⟩
    rw [natRep_apply]
    exact hAv' v
  · intro x y hx hxy
    have hx' : Φ.Q x = 0 := hx
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler' Φ hι hx' hxy
    have hAv' : ∀ v, Matrix.mulVec (A : Matrix ι ι F) v =
        v + Φ.polar.β x v • (y + (-Φ.Q y) • x) - Φ.polar.β y v • x := by
      intro v
      rw [hAv v, Φ.eichler_apply]
      module
    refine ⟨-Φ.Q y, ⟨A, hA⟩, fun v => ?_⟩
    rw [natRep_apply]
    exact hAv' v
  · intro h w hw
    have hg : ∀ v, Φ.Q (natRep (StatedOmega Φ.Q) h v) = Φ.Q v := fun v => by
      rw [natRep_apply]
      exact orthGroup_preserves Φ.Q (statedOmega_le_orthGroup Φ.Q h.2) v
    have key := Φ.Q_sub_self (g := natRep (StatedOmega Φ.Q) h) hg w
    have h1 : Φ.polar.β (natRep (StatedOmega Φ.Q) h w - w) w = 0 := by
      linear_combination key - hw
    rw [Φ.polar_symm]
    exact h1

end CFSG.LieType.ChevTwo.OppCl
