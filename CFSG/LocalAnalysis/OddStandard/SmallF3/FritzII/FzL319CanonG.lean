module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Facts

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
  (D : Fz319Data t tau lam rho Z E W Q R T P)

namespace Fz319Data

theorem mu_W {g : G} (hg : g ∈ T) : g ∈ W ↔ ∃ x : FzElt, D.mu x = g ∧ fzInW D.cT x := by
  constructor
  · intro hgW
    rcases D.str.W_split g hgW with hgE | hgE
    · refine ⟨(D.φ ⟨g, D.pf.EP hgE⟩, 0), ?_, ?_⟩
      · simp [Fz319Data.mu]
      · exact ⟨(D.E_iff ⟨g, D.pf.EP hgE⟩).mp hgE, rfl, rfl⟩
    · refine ⟨(D.φ ⟨t * g, D.pf.EP hgE⟩, (1, 0, 0)), ?_, ?_⟩
      · have hcomm : t * g = g * t := D.str.W_comm t D.str.t_mem g hgW
        have ht2 : t * t = 1 := by rw [← pow_two]; exact D.str.t_sq
        have hgoal : (t * g) * t = g := by rw [hcomm, mul_assoc, ht2, mul_one]
        have hmu : D.mu (D.φ ⟨t * g, D.pf.EP hgE⟩, (1, 0, 0)) = (t * g) * t := by
          simp [Fz319Data.mu, ZMod.val_one]
        rw [hmu, hgoal]
      · exact ⟨(D.E_iff ⟨t * g, D.pf.EP hgE⟩).mp hgE, rfl, rfl⟩
  · rintro ⟨x, hx, hfx⟩
    rw [← hx]
    have hmemE : ((D.φ.symm x.1 : ↥P) : G) ∈ E :=
      (D.E_iff (D.φ.symm x.1)).mpr (by simpa using hfx.1)
    have hmu : D.mu x = ((D.φ.symm x.1 : ↥P) : G) * t ^ x.2.1.val := by
      simp [Fz319Data.mu, hfx.2.1, hfx.2.2]
    rw [hmu]
    exact W.mul_mem (D.str.EW hmemE) (W.pow_mem D.str.t_mem _)

end Fz319Data

end CFSG.OddStandard.SmallF3.FritzII
