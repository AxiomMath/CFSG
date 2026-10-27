module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldC

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Open TauCeti

theorem e27LieOuterAutAt_C : E27LieOuterAutAt (fun i => ∃ r q, i = .C r q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout hfixD - -
  obtain ⟨i, hv⟩ := d
  obtain ⟨r, q, rfl⟩ := hd
  have hr : 3 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
    ((LieTypeIndex.valid_iff _).1 hv).1).1
  obtain ⟨-, F, _, _, hF, ⟨θ⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
  set ζ := MulAut.congr θ u with hζ
  have hζ3 : ζ ^ 3 = 1 := by rw [hζ, ← map_pow, hu3, map_one]
  have hinn : ζ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r F)) := by
    rintro ⟨k, hk⟩
    apply hout (θ.symm k)
    apply (MulAut.congr θ).injective
    rw [← hζ, ← hk]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_PSp hr (ℓ := q.p) (f := q.exponent)
    q.prime_p q.exponent_pos hF ζ hζ3 hinn
  obtain ⟨D', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr θ u hfix hperf h3
  exact hfixD D' hfix' hperf' h3'

theorem e27LieOuterAutAt_B_even_three :
    E27LieOuterAutAt (fun i => ∃ r q, i = .B r q ∧ q.p = 2 ∧ 3 ≤ r) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout hfixD - -
  obtain ⟨i, hv⟩ := d
  obtain ⟨r, q, rfl, hp, hr⟩ := hd
  obtain ⟨-, F, _, _, hF, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr e
  set ζ := MulAut.congr θ u with hζ
  have hζ3 : ζ ^ 3 = 1 := by rw [hζ, ← map_pow, hu3, map_one]
  have hinn : ζ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r F)) := by
    rintro ⟨k, hk⟩
    apply hout (θ.symm k)
    apply (MulAut.congr θ).injective
    rw [← hζ, ← hk]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_PSp hr (ℓ := q.p) (f := q.exponent)
    q.prime_p q.exponent_pos hF ζ hζ3 hinn
  obtain ⟨D', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr θ u hfix hperf h3
  exact hfixD D' hfix' hperf' h3'

end CFSG.HardMathSupport.Malle.E27Lie
