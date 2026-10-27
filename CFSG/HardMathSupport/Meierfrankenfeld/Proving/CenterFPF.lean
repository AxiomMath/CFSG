module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving

theorem fpf_of_mem_center_of_isIrrOn {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) {z : MulAut W}
    (hzc : ∀ l ∈ L, z * l = l * z) (hz1 : z ≠ 1) : ∀ w : W, z w = w → w = 1 := by
  let C : Subgroup W :=
    { carrier := {w | z w = w}
      mul_mem' := fun {a b} ha hb => by
        change z (a * b) = a * b
        have ha' : z a = a := ha
        have hb' : z b = b := hb
        rw [map_mul, ha', hb']
      one_mem' := by
        change z 1 = 1
        exact map_one z
      inv_mem' := fun {a} ha => by
        change z a⁻¹ = a⁻¹
        have ha' : z a = a := ha
        rw [map_inv, ha'] }
  have hCL : ∀ g ∈ L, ∀ u ∈ C, g u ∈ C := by
    intro g hg u hu
    have hu' : z u = u := hu
    have h := congrArg (fun φ : MulAut W => φ u) (hzc g hg)
    simp only [MulAut.mul_apply] at h
    change z (g u) = g u
    rw [h, hu']
  unfold CFSG.QuasithinUnique.Setup.X1.IsIrrOn at hirr
  obtain ⟨-, hirr'⟩ := hirr
  intro w hw
  rcases hirr' C hCL with hbot | htop
  · have hwC : w ∈ C := hw
    rw [hbot] at hwC
    exact Subgroup.mem_bot.1 hwC
  · exfalso
    apply hz1
    refine MulEquiv.ext fun w => ?_
    have hwC : w ∈ C := by
      rw [htop]
      exact Subgroup.mem_top w
    exact hwC

end CFSG.HardMathSupport.Meierfrankenfeld.Proving
