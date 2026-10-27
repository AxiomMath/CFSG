module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitQuot
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitTenCore
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepPairEven

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

theorem exitTenEven : ExitTenEven := by
  intro V _ _ hV H ψ hψ hAlt A hA hAL p q hpq horb hmin ι hι hex
  obtain ⟨hE1, hE2, -⟩ := hex
  have ha : ∀ x : ↥H, (ψ x).IsThreeCycle → (∀ i ∈ ({p, q} : Finset (Fin 10)), ψ x i = i) →
      fixV (Subgroup.zpowers (x : MulAut V)) =
        fixV (altPre (restrictHom ψ ι
          (preSub ψ (alternatingGroup (Fin 10) ⊓ permSetStab (Set.range ι)))
          (preSub_mono inf_le_right))) := by
    intro x hx3 hxpq
    have hp : ψ x p = p := hxpq p (by simp)
    have hq : ψ x q = q := hxpq q (by simp)
    have hxK : (x : MulAut V) ∈
        preSub ψ (alternatingGroup (Fin 10) ⊓ permSetStab (Set.range ι)) :=
      coe_mem_preSub.2 ⟨hx3.mem_alternatingGroup, mem_permSetStab_of_pair hι (Or.inl ⟨hp, hq⟩)⟩
    set k : ↥(preSub ψ (alternatingGroup (Fin 10) ⊓ permSetStab (Set.range ι))) := ⟨x, hxK⟩
      with hk
    have hinc : Subgroup.inclusion ((preSub_mono inf_le_right).trans preSub_le) k = x :=
      Subtype.ext rfl
    have hx3' :
        (ψ (Subgroup.inclusion ((preSub_mono inf_le_right).trans preSub_le) k)).IsThreeCycle := by
      rw [hinc]
      exact hx3
    have hfix : ∀ y, y ∉ Set.range ι →
        ψ (Subgroup.inclusion ((preSub_mono inf_le_right).trans preSub_le) k) y = y := by
      intro y hy
      rw [hι, not_and_or, not_not, not_not] at hy
      rw [hinc]
      rcases hy with rfl | rfl
      · exact hp
      · exact hq
    have h3 := isThreeCycle_restrictHom (hK := preSub_mono inf_le_right) k hx3' hfix
    exact fixV_zpowers_eq_of_exotic hE1 hE2 h3
  have hcent : ∀ y : ↥H, (ψ y).IsThreeCycle → fixV (Subgroup.zpowers (y : MulAut V)) =
      fixV (altPre (restrictHom ψ ι
        (preSub ψ (alternatingGroup (Fin 10) ⊓ permSetStab (Set.range ι)))
        (preSub_mono inf_le_right))) :=
    fun y hy => fixV_zpowers_eq_of_fix hAlt {p, q} (by rw [Finset.card_pair hpq]; norm_num) ha hy
  have hL := fixV_altPre_eq_of_forall (by norm_num) hψ hAlt hcent
  obtain ⟨W, _, _, G, φ, e, hW, hφ, hφA, h3, -, hφe, -, hoff⟩ :=
    exists_quot hV (by norm_num) hψ hAlt fun y hy => (hcent y hy).trans hL.symm
  obtain ⟨B, hBG, -, hBel, hBcard, hBmem⟩ := hoff A hA
  refine absurd hBcard (not_le.2 (ten_core hW hφ hφA h3 hBG hBel hpq ?_ ?_ ?_))
  · intro b hb
    obtain ⟨a, haA, rfl⟩ := (hBmem b).1 hb
    rw [hφe]
    exact horb a haA
  · intro i
    obtain ⟨a, haA, hai⟩ := hmin i
    exact ⟨e a, (hBmem (e a)).2 ⟨a, haA, rfl⟩, by rw [hφe]; exact hai⟩
  · intro b hb
    obtain ⟨a, haA, rfl⟩ := (hBmem b).1 hb
    rw [hφe]
    intro h
    have h1 : ψ a ∈ alternatingGroup (Fin 10) := coe_mem_altPre_iff.1 (hAL haA)
    rw [h, mem_alternatingGroup, sign_swap hpq] at h1
    exact absurd h1 (by decide)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
