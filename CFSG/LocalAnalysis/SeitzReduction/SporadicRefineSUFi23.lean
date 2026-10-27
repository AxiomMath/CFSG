module

public import CFSG.Sporadic.FischerOddCore.Fi23Block

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.UnitaryPilot

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG Subgroup CFSG.LocalCores CFSG.Sporadic.FischerOddCore

section Fi23


theorem fi23_involution_component_card_quotient {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Fi23) (a : S) (ha : orderOf a = 2)
    (B : Subgroup (Subgroup.centralizer ({a} : Set S))) (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 64561751654400 ∨
      Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  set f : S ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hx2 : f a ^ 2 = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hx1 : f a ≠ 1 := fun h => by
    rw [MulEquiv.map_eq_one_iff] at h
    rw [h, orderOf_one] at ha
    omega
  refine @component_quotient_of_mulEquiv S CFSG.Sporadic.Fi23.J _ inferInstance f a
    (fun n => n = 64561751654400 ∨ n = 9196830720) ?_ B hB
  intro B' hB'
  rcases CFSG.Sporadic.Fi23.involution_cover (f a) hx2 hx1 with h | h | h
  · exact @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
      (fun n => n = 64561751654400 ∨ n = 9196830720)
      (fun B'' hB'' => .inl (card_quotient_center_of_component_Cd hB'')) B' hB'
  · exact @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
      (fun n => n = 64561751654400 ∨ n = 9196830720)
      (fun B'' hB'' => .inr (card_quotient_center_of_component_dd1 hB'')) B' hB'
  · exact @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
      (fun n => n = 64561751654400 ∨ n = 9196830720)
      (fun B'' hB'' => absurd hB'' (fi23_no_component_t2 B'')) B' hB'

theorem fi23_conj_pair_unique {c w : CFSG.Sporadic.Fi23.J}
    (hc : c * (CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d1) * c⁻¹ = w) (g : CFSG.Sporadic.Fi23.J)
    (hg : g * w = w * g) :
    g * (c * CFSG.Sporadic.Fi23.d * c⁻¹) * g⁻¹ = c * CFSG.Sporadic.Fi23.d * c⁻¹ ∨
      g * (c * CFSG.Sporadic.Fi23.d * c⁻¹) * g⁻¹ = c * CFSG.Sporadic.Fi23.d1 * c⁻¹ := by
  set g' := c⁻¹ * g * c
  have hg' : g' * (CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d1) =
      CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d1 * g' := by
    have e1 : CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d1 = c⁻¹ * w * c := by rw [← hc]; group
    rw [e1]
    calc c⁻¹ * g * c * (c⁻¹ * w * c) = c⁻¹ * (g * w) * c := by group
      _ = c⁻¹ * (w * g) * c := by rw [hg]
      _ = c⁻¹ * w * c * (c⁻¹ * g * c) := by group
  have key : g * (c * CFSG.Sporadic.Fi23.d * c⁻¹) * g⁻¹ =
      c * (g' * CFSG.Sporadic.Fi23.d * g'⁻¹) * c⁻¹ := by
    simp only [g']
    group
  rcases fi23_pair_unique g' hg' with h | h
  · left
    rw [key, h]
  · right
    rw [key, h]

theorem fi23_involution_component_exists_pair {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Fi23) (a : S) (ha : orderOf a = 2)
    (B : Subgroup (Subgroup.centralizer ({a} : Set S))) (hB : IsComponent B)
    (hcard : Nat.card (B ⧸ Subgroup.center B) = 9196830720) :
    ∃ x y : S, x * x = 1 ∧ y * y = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x * y = y * x ∧ x * y = a ∧
      ∀ b ∈ B, (b : S) * x = x * (b : S) ∧ (b : S) * y = y * (b : S) := by
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
    refine ⟨f.symm x', f.symm y', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, MulEquiv.symm_apply_eq, map_one]
      calc x' * x' = c * (CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d) * c⁻¹ := by
            simp only [x']; group
        _ = 1 := by rw [hd]; group
    · rw [← map_mul, MulEquiv.symm_apply_eq, map_one]
      calc y' * y' = c * (CFSG.Sporadic.Fi23.d1 * CFSG.Sporadic.Fi23.d1) * c⁻¹ := by
            simp only [y']; group
        _ = 1 := by rw [hd1]; group
    · rw [Ne, MulEquiv.symm_apply_eq, map_one]
      intro h1
      apply CFSG.Sporadic.Fi23.d_ne_one
      calc CFSG.Sporadic.Fi23.d = c⁻¹ * x' * c := by simp only [x']; group
        _ = 1 := by rw [h1]; group
    · rw [Ne, MulEquiv.symm_apply_eq, map_one]
      intro h1
      have hd11 : CFSG.Sporadic.Fi23.d1 = 1 := by
        calc CFSG.Sporadic.Fi23.d1 = c⁻¹ * y' * c := by simp only [y']; group
          _ = 1 := by rw [h1]; group
      exact CFSG.Sporadic.Fi23.d_ne_one (isConj_one_left.1 (hd11 ▸ fi23_d1_mem))
    · intro h1
      apply fi23_d_ne_d1
      have h2 : x' = y' := f.symm.injective h1
      calc CFSG.Sporadic.Fi23.d = c⁻¹ * x' * c := by simp only [x']; group
        _ = c⁻¹ * y' * c := by rw [h2]
        _ = CFSG.Sporadic.Fi23.d1 := by simp only [y']; group
    · rw [← map_mul, ← map_mul, hcxy']
    · rw [← map_mul, hxy', MulEquiv.symm_apply_apply]
    ·
      have hxy : f.symm x' * f.symm y' = a := by rw [← map_mul, hxy', MulEquiv.symm_apply_apply]
      have hxx : f.symm x' * f.symm x' = 1 := by
        rw [← map_mul, MulEquiv.symm_apply_eq, map_one]
        calc x' * x' = c * (CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d) * c⁻¹ := by
              simp only [x']; group
          _ = 1 := by rw [hd]; group
      have hyy : f.symm y' * f.symm y' = 1 := by
        rw [← map_mul, MulEquiv.symm_apply_eq, map_one]
        calc y' * y' = c * (CFSG.Sporadic.Fi23.d1 * CFSG.Sporadic.Fi23.d1) * c⁻¹ := by
              simp only [y']; group
          _ = 1 := by rw [hd1]; group
      have hcxy : f.symm x' * f.symm y' = f.symm y' * f.symm x' := by
        rw [← map_mul, ← map_mul, hcxy']
      have hne : f.symm x' ≠ f.symm y' := by
        intro h1
        apply fi23_d_ne_d1
        have h2 : x' = y' := f.symm.injective h1
        calc CFSG.Sporadic.Fi23.d = c⁻¹ * x' * c := by simp only [x']; group
          _ = c⁻¹ * y' * c := by rw [h2]
          _ = CFSG.Sporadic.Fi23.d1 := by simp only [y']; group
      have huniq : ∀ g : S, g * (f.symm x' * f.symm y') = f.symm x' * f.symm y' * g →
          g * f.symm x' * g⁻¹ = f.symm x' ∨ g * f.symm x' * g⁻¹ = f.symm y' := by
        intro g hg
        rw [hxy] at hg
        have hfg : f g * f a = f a * f g := by rw [← map_mul, ← map_mul, hg]
        rcases fi23_conj_pair_unique hc (f g) hfg with h1 | h1
        · left
          apply f.injective
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
          exact h1
        · right
          apply f.injective
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
          exact h1
      let φ : ↥(Subgroup.centralizer ({a} : Set S)) ≃*
          ↥(Subgroup.centralizer ({f.symm x' * f.symm y'} : Set S)) :=
        MulEquiv.subgroupCongr (by rw [hxy])
      have hB' := LocalCores.isComponent_map_mulEquiv φ hB
      intro b hb
      have hbx : (b : S) * f.symm x' = f.symm x' * (b : S) :=
        commute_of_perfect_pair hxx hyy hcxy hne huniq hB'.1.1
          (b := φ b) ⟨b, hb, rfl⟩
      refine ⟨hbx, ?_⟩
      have hba : (b : S) * a = a * (b : S) := Subgroup.mem_centralizer_singleton_iff.1 b.2
      have hy : f.symm y' = f.symm x' * a := by
        rw [← hxy, ← mul_assoc, hxx, one_mul]
      rw [hy]
      calc (b : S) * (f.symm x' * a) = (b : S) * f.symm x' * a := by group
        _ = f.symm x' * (b : S) * a := by rw [hbx]
        _ = f.symm x' * ((b : S) * a) := by group
        _ = f.symm x' * (a * (b : S)) := by rw [hba]
        _ = f.symm x' * a * (b : S) := by group
  · exfalso
    exact @component_quotient_of_mulEquiv S CFSG.Sporadic.Fi23.J _ inferInstance f a
      (fun _ => False) (fun B' hB' =>
        @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
          (fun _ => False) (fun B'' hB'' => absurd hB'' (fi23_no_component_t2 B'')) B' hB') B hB

end Fi23

end CFSG.SeitzReduction.UnitaryPilot
