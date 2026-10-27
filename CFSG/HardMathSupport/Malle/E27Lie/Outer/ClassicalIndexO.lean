module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldOB2
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldOOdd
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldOPlus
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldOMinus
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Open TauCeti CFSG.RankThree.PartTwo.Census

theorem not_inner_of_ne_conj {K : Type} [Group K] {u : MulAut K}
    (hout : ∀ k : K, u ≠ MulAut.conj k) :
    u ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K := by
  rintro ⟨k, hk⟩
  exact hout k (by rw [← hk])

theorem e27LieOuterAutAt_B_two_odd :
    E27LieOuterAutAt (fun i => ∃ q, i = .B 2 q ∧ q.p ≠ 2) := by
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
  obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_PSp_odd le_rfl (ℓ := q.p)
    (f := q.exponent) q.prime_p hp q.exponent_pos hF ζ hζ3 hinn
  obtain ⟨D', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr θ u hfix hperf h3
  exact hfixD D' hfix' hperf' h3'

theorem e27LieOuterAutAt_B_three_odd :
    E27LieOuterAutAt (fun i => ∃ r q, i = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout hfixD - -
  obtain ⟨i, hv⟩ := d
  obtain ⟨r, q, rfl, hp, hr⟩ := hd
  have hcl := statedClassicalModel_typeB_odd r q hv hp hr e
  obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_POmegaOdd hcl u hu3
    (not_inner_of_ne_conj hout)
  exact hfixD D hfix hperf h3

theorem e27LieOuterAutAt_B_odd : E27LieOuterAutAt (fun i => ∃ r q, i = .B r q ∧ q.p ≠ 2) := by
  intro K _ _ d hd
  obtain ⟨r, q, hdr, hp⟩ := hd
  have hv := d.2
  rw [hdr] at hv
  have hr : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
    ((LieTypeIndex.valid_iff _).1 hv).1).1
  rcases (show r = 2 ∨ 3 ≤ r by omega) with h2 | h3
  · exact e27LieOuterAutAt_B_two_odd K d ⟨q, h2 ▸ hdr, hp⟩
  · exact e27LieOuterAutAt_B_three_odd K d ⟨r, q, hdr, hp, h3⟩

theorem e27LieOuterAutAt_D : E27LieOuterAutAt (fun i => ∃ r q, i = .D r q ∧ 5 ≤ r) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout hfixD - -
  obtain ⟨i, hv⟩ := d
  obtain ⟨r, q, rfl, hr⟩ := hd
  have hcl := statedClassicalModel_typeD r q hv e
  obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_POmegaPlus hr hcl u hu3
    (not_inner_of_ne_conj hout)
  exact hfixD D hfix hperf h3

theorem e27LieOuterAutAt_twistedD : E27LieOuterAutAt (fun i => ∃ r q, i = .twistedD r q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout hfixD - -
  obtain ⟨i, hv⟩ := d
  obtain ⟨r, q, rfl⟩ := hd
  have hcl := statedClassicalModel_typeTwistedD r q hv e
  obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_POmegaMinus hcl u hu3
    (not_inner_of_ne_conj hout)
  exact hfixD D hfix hperf h3

end CFSG.HardMathSupport.Malle.E27Lie
