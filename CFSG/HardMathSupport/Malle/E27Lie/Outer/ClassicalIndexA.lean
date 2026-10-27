module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldA
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldA2
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagA
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SPLLieLGlue
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldLinear

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Open TauCeti CFSG.LocalAnalysis.ComponentInitial

@[expose] def LinearDiagSlice : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (ζ : MulAut (LinearFlag.projectiveSL 3 F)),
    ζ ^ 3 = 1 → ζ ∈ LinearFlag.linearAutGroup 3 F →
    (∀ k : LinearFlag.projectiveSL 3 F, ζ ≠ MulAut.conj k) →
    (∀ D : Subgroup (LinearFlag.projectiveSL 3 F), (∀ x ∈ D, ζ x = x) → ⁅D, D⁆ = D →
      ¬ 3 ∣ Nat.card D) →
    (∀ Q : Subgroup (LinearFlag.projectiveSL 3 F), (∀ x ∈ Q, ζ x = x) → IsPGroup 3 Q →
      Nat.card Q ≤ 9) →
    (∃ T : Subgroup (LinearFlag.projectiveSL 3 F), (∀ x ∈ T, ζ x = x) ∧ IsElemAbelian 3 T ∧
      Nat.card T = 9) →
    3 ^ 5 ∣ Nat.card (MulAut (LinearFlag.projectiveSL 3 F)) → False

theorem e27LieOuterAutAt_A_of_diag (hdiag : LinearDiagSlice) :
    E27LieOuterAutAt (fun i => ∃ r q, i = .A r q ∧ 2 ≤ r) := by
  rintro K _ _ d hd ⟨e⟩ hAut u hu3 hout hfixD hQ hT
  obtain ⟨i, hv⟩ := d
  obtain ⟨r, q, rfl, hr⟩ := hd
  obtain ⟨-, F, _, _, hF, ⟨θ⟩⟩ :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.statedClassicalModel_typeA' hv e
  let e' : K ≃* LinearFlag.projectiveSL (r + 1) F :=
    θ.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj (r + 1) F).symm
  have hn : 3 ≤ r + 1 := by omega
  set ζ := MulAut.congr e' u with hζ
  have hζ3 : ζ ^ 3 = 1 := by rw [hζ, ← map_pow, hu3, map_one]
  have hsemi : ζ ∈ LinearFlag.semilinearAutGroup (r + 1) F :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.mem_semilinearAutGroup_of_pow hn
      (by decide) hζ3
  have hout' : ∀ k : LinearFlag.projectiveSL (r + 1) F, ζ ≠ MulAut.conj k := by
    intro k hk
    apply hout (e'.symm k)
    apply (MulAut.congr e').injective
    rw [← hζ, hk]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  by_cases hlin : ζ ∈ LinearFlag.linearAutGroup (r + 1) F
  · by_cases h4 : 4 ≤ r + 1
    · obtain ⟨B, hB⟩ := LinearFlag.mem_linearAutGroup_iff.mp hlin
      obtain ⟨Q, hQfix, hQperf, hQ3⟩ := exists_fixed_perfect_three_of_diag h4 B (hB ▸ hζ3)
        (fun k hk => hout' k (hB ▸ hk))
      obtain ⟨Q', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr e' u
        (fun x hx => by
          have := hQfix x hx
          rwa [hB] at this) hQperf hQ3
      exact hfixD Q' hfix' hperf' h3'
    · obtain rfl : r = 2 := by omega
      exact hdiag F ζ hζ3 hlin hout' (noPerfect_of_congr e' u hfixD)
        (card_le_nine_of_congr e' u hQ) (exists_elemAbelian_of_congr e' u hT)
        ((Nat.card_congr (MulAut.congr e').toEquiv) ▸ hAut)
  · obtain ⟨D, hfix, hperf, h3⟩ := exists_fixed_perfect_three_of_semilinear hn
      (ℓ := q.p) (f := q.exponent) q.prime_p q.exponent_pos hF ζ hζ3 hsemi hlin
    obtain ⟨D', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr e' u hfix hperf h3
    exact hfixD D' hfix' hperf' h3'

theorem e27LieOuterAutAt_A_one : E27LieOuterAutAt (fun i => ∃ q, i = .A 1 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout hfixD hQ hT
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  obtain ⟨-, F, _, _, hF, ⟨θ⟩⟩ :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.statedClassicalModel_typeA' hv e
  let e' : K ≃* LinearFlag.projectiveSL (1 + 1) F :=
    θ.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj (1 + 1) F).symm
  set ζ := MulAut.congr e' u with hζ
  have hζ3 : ζ ^ 3 = 1 := by rw [hζ, ← map_pow, hu3, map_one]
  have hinn : ζ ∉ CFSG.RankThree.PartOne.Sec66T.innerAut (LinearFlag.projectiveSL (1 + 1) F) := by
    rintro ⟨k, hk⟩
    apply hout (e'.symm k)
    apply (MulAut.congr e').injective
    rw [← hζ, ← hk]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rcases psl_two_field_case (ℓ := q.p) (f := q.exponent) q.prime_p q.exponent_pos hF ζ hζ3
    hinn with ⟨D, hfix, hperf, h3⟩ | h24
  · obtain ⟨D', hfix', hperf', h3'⟩ := exists_fixed_perfect_of_congr e' u hfix hperf h3
    exact hfixD D' hfix' hperf' h3'
  · obtain ⟨T', hfix, -, hc9⟩ := exists_elemAbelian_of_congr e' u hT
    have hle : T' ≤ CFSG.RankThree.PartOne.Sec66T.fixSub ζ := fun x hx => hfix x hx
    have h9 : 9 ∣ 24 := hc9 ▸ (Subgroup.card_dvd_of_le hle).trans h24
    omega

theorem e27LieOuterAutAt_A_all_of_diag (hdiag : LinearDiagSlice) :
    E27LieOuterAutAt (fun i => ∃ r q, i = .A r q) := by
  rintro K _ _ d ⟨r, q, hr⟩ he
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .A r q := hr
  have h1 : 1 ≤ r := by
    have h := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    exact h.1
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact e27LieOuterAutAt_A_one K ⟨.A 1 q, hv⟩ ⟨q, rfl⟩ he
  · exact e27LieOuterAutAt_A_of_diag hdiag K ⟨.A r q, hv⟩ ⟨r, q, rfl, h⟩ he

end CFSG.HardMathSupport.Malle.E27Lie
