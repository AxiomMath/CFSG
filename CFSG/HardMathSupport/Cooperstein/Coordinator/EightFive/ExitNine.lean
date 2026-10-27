module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitQuot
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NineA9
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepFix

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

theorem exitNineFix : ExitNineFix := by
  intro V _ _ hV H ψ hψ hAlt A hA ω _ ι hι hex
  obtain ⟨hE1, hE2, -⟩ := hex
  have ha : ∀ x : ↥H, (ψ x).IsThreeCycle → (∀ i ∈ ({ω} : Finset (Fin 9)), ψ x i = i) →
      fixV (Subgroup.zpowers (x : MulAut V)) =
        fixV (altPre (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl)) := by
    intro x hx3 hxω
    have hω' : ψ x ω = ω := hxω ω (Finset.mem_singleton_self ω)
    have hxK : (x : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
      coe_mem_preSub.2 (mem_permSetStab_of_apply_eq hι hω')
    set k : ↥(preSub ψ (permSetStab (Set.range ι))) := ⟨x, hxK⟩ with hk
    have hinc : Subgroup.inclusion (le_rfl.trans preSub_le) k = x := Subtype.ext rfl
    have hx3' : (ψ (Subgroup.inclusion (le_rfl.trans preSub_le) k)).IsThreeCycle := by
      rw [hinc]
      exact hx3
    have hfix : ∀ y, y ∉ Set.range ι → ψ (Subgroup.inclusion (le_rfl.trans preSub_le) k) y = y := by
      intro y hy
      rw [hι, not_not] at hy
      rw [hinc, hy]
      exact hω'
    have h3 := isThreeCycle_restrictHom (hK := le_rfl) k hx3' hfix
    exact fixV_zpowers_eq_of_exotic hE1 hE2 h3
  have hcent : ∀ y : ↥H, (ψ y).IsThreeCycle → fixV (Subgroup.zpowers (y : MulAut V)) =
      fixV (altPre (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl)) :=
    fun y hy => fixV_zpowers_eq_of_fix hAlt {ω} (by simp) ha hy
  have hL := fixV_altPre_eq_of_forall (by norm_num) hψ hAlt hcent
  obtain ⟨W, _, _, G, φ, e, hW, hφ, hφA, h3, -, -, -, hoff⟩ :=
    exists_quot hV (by norm_num) hψ hAlt fun y hy => (hcent y hy).trans hL.symm
  obtain ⟨B, hBG, hB1, hBel, hBcard, -⟩ := hoff A hA
  exact absurd hBcard (not_le.2 (a9 hW hφ hφA h3 hBG hB1 hBel))

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
