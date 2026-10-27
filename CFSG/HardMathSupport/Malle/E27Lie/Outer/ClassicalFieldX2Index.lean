module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldX2Even

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Open TauCeti

theorem e27LieOuterAutAt_B_two_even :
    E27LieOuterAutAt (fun i => ∃ q, i = .B 2 q ∧ q.p = 2) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout hfixD - -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl, hp⟩ := hd
  obtain ⟨-, F, _, _, hF, ⟨θ⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  set ζ := MulAut.congr θ u with hζ
  have hζ3 : ζ ^ 3 = 1 := by rw [hζ, ← map_pow, hu3, map_one]
  have hinn : ζ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
    rintro ⟨k, hk⟩
    apply hout (θ.symm k)
    apply (MulAut.congr θ).injective
    rw [← hζ, ← hk]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_PSp_two_even (ℓ := q.p)
    (f := q.exponent) hp q.exponent_pos hF ζ hζ3 hinn
  obtain ⟨D', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr θ u hfix hperf h3
  exact hfixD D' hfix' hperf' h3'

end CFSG.HardMathSupport.Malle.E27Lie
