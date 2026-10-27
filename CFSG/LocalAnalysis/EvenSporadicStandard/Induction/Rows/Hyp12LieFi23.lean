module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSUFi23
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Hyp12Lie

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG Subgroup CFSG.LocalCores CFSG.Sporadic.FischerOddCore

section Fi23


theorem fi23_comp_centralizes_transposition {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Fi23) (a : S) (ha : orderOf a = 2)
    (B : Subgroup (Subgroup.centralizer ({a} : Set S))) (hB : IsComponent B)
    (hcard : Nat.card (B ⧸ Subgroup.center B) = 9196830720) :
    ∃ x : S, orderOf x = 2 ∧
      (∀ B' : Subgroup (Subgroup.centralizer ({x} : Set S)), IsComponent B' →
        Nat.card (B' ⧸ Subgroup.center B') = 64561751654400) ∧
      ∀ b ∈ B, (b : S) * x = x * (b : S) := by
  set f : S ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hx2 : f a ^ 2 = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hx1 : f a ≠ 1 := fun h => by
    rw [MulEquiv.map_eq_one_iff] at h
    rw [h, orderOf_one] at ha
    omega
  rcases CFSG.Sporadic.Fi23.involution_cover (f a) hx2 hx1 with h | h | h
  · exfalso
    have hne := @component_quotient_of_mulEquiv S CFSG.Sporadic.Fi23.J _ inferInstance f a
      (fun n => n ≠ 9196830720) (fun B' hB' =>
        @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
          (fun n => n ≠ 9196830720)
          (fun B'' hB'' => by
            show Nat.card (B'' ⧸ Subgroup.center B'') ≠ 9196830720
            rw [card_quotient_center_of_component_Cd hB'']
            norm_num) B' hB') B hB
    exact hne hcard
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    set x' : CFSG.Sporadic.Fi23.J := c * CFSG.Sporadic.Fi23.d * c⁻¹
    set y' : CFSG.Sporadic.Fi23.J := c * CFSG.Sporadic.Fi23.d1 * c⁻¹
    have hxy' : x' * y' = f a := by
      rw [← hc]
      simp only [x', y']
      group
    have hd := CFSG.Sporadic.Fi23.d_sq
    have hd1 : CFSG.Sporadic.Fi23.d1 * CFSG.Sporadic.Fi23.d1 = 1 := by
      rw [← sq]
      exact CFSG.Sporadic.Fi23.d1_sq
    have hcomm := CFSG.Sporadic.Fi23.d1_commute
    have hcxy' : x' * y' = y' * x' := by
      calc x' * y' = c * (CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d1) * c⁻¹ := by
            simp only [x', y']; group
        _ = c * (CFSG.Sporadic.Fi23.d1 * CFSG.Sporadic.Fi23.d) * c⁻¹ := by rw [hcomm]
        _ = y' * x' := by simp only [x', y']; group
    have hxx' : x' * x' = 1 := by
      calc x' * x' = c * (CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d) * c⁻¹ := by
            simp only [x']; group
        _ = 1 := by rw [hd]; group
    have hyy' : y' * y' = 1 := by
      calc y' * y' = c * (CFSG.Sporadic.Fi23.d1 * CFSG.Sporadic.Fi23.d1) * c⁻¹ := by
            simp only [y']; group
        _ = 1 := by rw [hd1]; group
    have hx1' : x' ≠ 1 := by
      intro h1
      apply CFSG.Sporadic.Fi23.d_ne_one
      calc CFSG.Sporadic.Fi23.d = c⁻¹ * x' * c := by simp only [x']; group
        _ = 1 := by rw [h1]; group
    have hne' : x' ≠ y' := by
      intro h1
      apply fi23_d_ne_d1
      calc CFSG.Sporadic.Fi23.d = c⁻¹ * x' * c := by simp only [x']; group
        _ = c⁻¹ * y' * c := by rw [h1]
        _ = CFSG.Sporadic.Fi23.d1 := by simp only [y']; group
    have hxy : f.symm x' * f.symm y' = a := by
      rw [← map_mul, hxy', MulEquiv.symm_apply_apply]
    have hxx : f.symm x' * f.symm x' = 1 := by
      rw [← map_mul, MulEquiv.symm_apply_eq, map_one]
      exact hxx'
    have hyy : f.symm y' * f.symm y' = 1 := by
      rw [← map_mul, MulEquiv.symm_apply_eq, map_one]
      exact hyy'
    have hcxy : f.symm x' * f.symm y' = f.symm y' * f.symm x' := by
      rw [← map_mul, ← map_mul, hcxy']
    have hne : f.symm x' ≠ f.symm y' := fun h1 => hne' (f.symm.injective h1)
    have huniq : ∀ g : S, g * (f.symm x' * f.symm y') = f.symm x' * f.symm y' * g →
        g * f.symm x' * g⁻¹ = f.symm x' ∨ g * f.symm x' * g⁻¹ = f.symm y' := by
      intro g hg
      rw [hxy] at hg
      have hfg : f g * f a = f a * f g := by rw [← map_mul, ← map_mul, hg]
      rcases CFSG.SeitzReduction.UnitaryPilot.fi23_conj_pair_unique hc (f g) hfg with h1 | h1
      · left
        apply f.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        exact h1
      · right
        apply f.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact h1
    have hBx : ∀ b ∈ B, (b : S) * f.symm x' = f.symm x' * (b : S) := by
      let φ : ↥(Subgroup.centralizer ({a} : Set S)) ≃*
          ↥(Subgroup.centralizer ({f.symm x' * f.symm y'} : Set S)) :=
        MulEquiv.subgroupCongr (by rw [hxy])
      have hB' := LocalCores.isComponent_map_mulEquiv φ hB
      intro b hb
      exact commute_of_perfect_pair hxx hyy hcxy hne huniq hB'.1.1 (b := φ b) ⟨b, hb, rfl⟩
    refine ⟨f.symm x', ?_, ?_, hBx⟩
    · exact orderOf_eq_prime (by rw [sq]; exact hxx) (fun h1 => hx1' (by
        simpa using congrArg f h1))
    · intro B' hB'
      exact @component_quotient_of_mulEquiv S CFSG.Sporadic.Fi23.J _ inferInstance f (f.symm x')
        (fun n => n = 64561751654400) (fun B'' hB'' =>
          @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance
            CFSG.Sporadic.Fi23.d _
            (isConj_iff.2 ⟨c, by rw [MulEquiv.apply_symm_apply]⟩)
            (fun n => n = 64561751654400)
            (fun B''' hB''' => card_quotient_center_of_component_Cd hB''') B'' hB'') B' hB'
  · exfalso
    exact @component_quotient_of_mulEquiv S CFSG.Sporadic.Fi23.J _ inferInstance f a
      (fun _ => False) (fun B' hB' =>
        @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
          (fun _ => False) (fun B'' hB'' => absurd hB'' (fi23_no_component_t2 B'')) B' hB') B hB

open CFSG.EvenSporadicStandard.Solomon78 in
theorem fi23_false_of_tight_u62 {S : Type} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Fi23) {L : Subgroup S} (hq : CFSG.IsQuasisimple ↥L)
    (hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 9196830720)
    (htight : ∀ r : S, orderOf r = 2 → r ∈ Subgroup.centralizer (L : Set S) →
      Subgroup.centralizer ({r} : Set S) ≤ Subgroup.normalizer (L : Set S))
    {z : S} (hz : orderOf z = 2) (hzL : z ∈ Subgroup.centralizer (L : Set S)) : False := by
  have hcomp : ∀ r : S, orderOf r = 2 → r ∈ Subgroup.centralizer (L : Set S) →
      L ≤ Subgroup.centralizer ({r} : Set S) ∧
        IsComponent (L.subgroupOf (Subgroup.centralizer ({r} : Set S))) := by
    intro r hr hrL
    have hLC : L ≤ Subgroup.centralizer ({r} : Set S) := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hrL l hl)
    exact ⟨hLC, (isCompIn_of_normal hLC hq
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2 (htight r hr hrL))).2⟩
  have hquot : ∀ {r : S} (hLC : L ≤ Subgroup.centralizer ({r} : Set S)),
      Nat.card (↥(L.subgroupOf (Subgroup.centralizer ({r} : Set S))) ⧸
        Subgroup.center ↥(L.subgroupOf (Subgroup.centralizer ({r} : Set S)))) =
        Nat.card (↥L ⧸ Subgroup.center ↥L) := fun {r} hLC => by
    let φ := Subgroup.subgroupOfEquivOfLe hLC
    exact Nat.card_congr (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).toEquiv
  obtain ⟨hLCz, hBz⟩ := hcomp z hz hzL
  obtain ⟨x, hx2, hxcls, hBx⟩ := fi23_comp_centralizes_transposition e z hz _ hBz
    ((hquot hLCz).trans hcard)
  have hxL : x ∈ Subgroup.centralizer (L : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hBx ⟨l, hLCz hl⟩ (Subgroup.mem_subgroupOf.2 hl)
  obtain ⟨hLCx, hBxc⟩ := hcomp x hx2 hxL
  have h1 := hxcls _ hBxc
  rw [hquot hLCx, hcard] at h1
  exact absurd h1 (by norm_num)

end Fi23

end CFSG.EvenSporadicStandard.Induction.Hyp12Lie
