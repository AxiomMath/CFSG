module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE6Aux1

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


@[expose] def ht (ν : V6) : ℤ := ν 0 + ν 2 + ν 4 + ν 5

theorem ht_sub (ν γ : V6) : ht (ν - γ) = ht ν - ht γ := by
  simp only [ht, Pi.sub_apply]
  ring

theorem ht_posL : ∀ γ ∈ posL, ht γ = 1 := by decide +kernel

theorem ht_Mlist : ∀ ν ∈ Mlist, 0 ≤ ht ν ∧ ht ν ≤ 6 := by decide +kernel

theorem hw_facts : ∀ μ ∈ Mlist, μ ≠ hw1 → μ ≠ hw2 → ∃ γ ∈ posL, μ + γ ∈ Mlist := by
  decide +kernel

@[expose] def mu0 : V6 := ![0, 1, 1, 1, 1, 1]

theorem mu0_eq : hw1 + -e0 = mu0 := by decide +kernel

theorem hw2_e0 : hw2 + -e0 ∉ rootFinset Tag.E6 := by decide +kernel

theorem hw_mem : hw1 ∈ Mlist ∧ hw2 ∈ Mlist ∧ mu0 ∈ Mlist := by decide +kernel

theorem hw1_ne_hw2 : hw1 ≠ hw2 := by decide +kernel

theorem neg_e0_mem : -e0 ∈ gam0 := by decide +kernel

@[expose] def nbrs (ν : V6) : List V6 := (gam0.map (ν + ·)).filter (· ∈ Mlist)

@[expose] def reach : ℕ → V6 → List V6
  | 0, ν => [ν]
  | k + 1, ν => ((reach k ν) ++ (reach k ν).flatMap nbrs).dedup

theorem reach_good {P : V6 → Prop} (hP : ∀ x, P x → ∀ y ∈ nbrs x, P y) :
    ∀ (k : ℕ) (ν : V6), P ν → ∀ x ∈ reach k ν, P x
  | 0, ν, h, x, hx => by
    rw [reach, List.mem_singleton] at hx
    subst hx
    exact h
  | k + 1, ν, h, x, hx => by
    rw [reach, List.mem_dedup, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨y, hy, hxy⟩
    · exact reach_good hP k ν h x hx
    · exact hP y (reach_good hP k ν h y hy) x hxy

theorem component_reach : ∀ ν ∈ Mlist, ∀ ν' ∈ Mlist, ν' 3 = ν 3 → ν' ∈ reach 4 ν := by
  decide +kernel

section Core

variable {F : Type} [Field F] (Wb : Submodule F (V6 → F))

theorem exists_killed (hsupp : ∀ v ∈ Wb, ∀ ν, ν ∉ Mlist → v ν = 0)
    (hT : ∀ γ ∈ gam0, ∀ v ∈ Wb, opT γ v ∈ Wb) :
    ∀ m : ℕ, ∀ v ∈ Wb, v ≠ 0 → (∀ ν, v ν ≠ 0 → (7 : ℤ) ≤ ht ν + m) →
      ∃ v' ∈ Wb, v' ≠ 0 ∧ ∀ γ ∈ posL, opT γ v' = 0 := by
  intro m
  induction m with
  | zero =>
    intro v hv hv0 hh
    exfalso
    obtain ⟨ν, hν⟩ := Function.ne_iff.1 hv0
    rw [Pi.zero_apply] at hν
    have hM : ν ∈ Mlist := by
      by_contra h
      exact hν (hsupp v hv ν h)
    have h1 := (ht_Mlist ν hM).2
    have h2 := hh ν hν
    push_cast at h2
    omega
  | succ m ih =>
    intro v hv hv0 hh
    by_cases hall : ∀ γ ∈ posL, opT γ v = 0
    · exact ⟨v, hv, hv0, hall⟩
    · push Not at hall
      obtain ⟨γ, hγ, hne⟩ := hall
      refine ih (opT γ v) (hT γ (posL_sub γ hγ) v hv) hne fun ν hν => ?_
      rw [opT_apply] at hν
      have h1 : v (ν - γ) ≠ 0 := right_ne_zero_of_mul hν
      have h2 := hh (ν - γ) h1
      rw [ht_sub, ht_posL γ hγ] at h2
      push_cast at h2 ⊢
      omega

theorem killed_supp {v : V6 → F} (hvM : ∀ ν, ν ∉ Mlist → v ν = 0)
    (hk : ∀ γ ∈ posL, opT γ v = 0) : ∀ μ, μ ≠ hw1 → μ ≠ hw2 → v μ = 0 := by
  intro μ h1 h2
  by_cases hμ : μ ∈ Mlist
  · obtain ⟨γ, hγ, hμγ⟩ := hw_facts μ hμ h1 h2
    have hγg := gam0_facts γ (posL_sub γ hγ)
    have hμf := Mlist_facts μ hμ
    have h0 := congrFun (hk γ hγ) (μ + γ)
    rw [opT_apply, add_sub_cancel_right, Pi.zero_apply] at h0
    exact (mul_eq_zero.1 h0).resolve_left
      (aE_ne_zero hγg.1 hγg.2 hμf.1 hμf.2.1 (Mlist_facts _ hμγ).1)
  · exact hvM μ hμ

theorem exists_weight (hsupp : ∀ v ∈ Wb, ∀ ν, ν ∉ Mlist → v ν = 0)
    (hT : ∀ γ ∈ gam0, ∀ v ∈ Wb, opT γ v ∈ Wb) (hne : Wb ≠ ⊥) :
    ∃ μ ∈ Mlist, ∃ c : F, c ≠ 0 ∧ (Pi.single μ c : V6 → F) ∈ Wb := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff Wb).1 hne
  obtain ⟨v', hv', hv'0, hk⟩ := exists_killed Wb hsupp hT 7 v hv hv0 (fun ν hν => by
    have hM : ν ∈ Mlist := by
      by_contra h
      exact hν (hsupp v hv ν h)
    have := (ht_Mlist ν hM).1
    push_cast
    omega)
  have hs := killed_supp (hsupp v' hv') hk
  have hv'eq : v' = Pi.single hw1 (v' hw1) + Pi.single hw2 (v' hw2) := by
    funext ν
    by_cases h1 : ν = hw1
    · subst h1
      simp [Pi.single_apply, hw1_ne_hw2]
    · by_cases h2 : ν = hw2
      · subst h2
        simp [Pi.single_apply, Ne.symm hw1_ne_hw2]
      · simp [Pi.single_apply, h1, h2, hs ν h1 h2]
  by_cases h1 : v' hw1 = 0
  · refine ⟨hw2, hw_mem.2.1, v' hw2, ?_, ?_⟩
    · intro h2
      apply hv'0
      rw [hv'eq, h1, h2]
      simp
    · have e : v' = Pi.single hw2 (v' hw2) := by
        rw [hv'eq, h1]
        simp
      rw [← e]
      exact hv'
  · have hT' := hT (-e0) neg_e0_mem v' hv'
    rw [hv'eq, map_add, opT_single, opT_single, aE_eq_zero hw2_e0, mu0_eq] at hT'
    simp only [Int.cast_zero, zero_mul, Pi.single_zero, add_zero] at hT'
    refine ⟨mu0, hw_mem.2.2, _, mul_ne_zero ?_ h1, hT'⟩
    have hg := gam0_facts (-e0) neg_e0_mem
    have hh := Mlist_facts hw1 hw_mem.1
    exact aE_ne_zero hg.1 hg.2 hh.1 hh.2.1 (by rw [mu0_eq]; exact (Mlist_facts _ hw_mem.2.2).1)

theorem core (hsupp : ∀ v ∈ Wb, ∀ ν, ν ∉ Mlist → v ν = 0)
    (hT : ∀ γ ∈ gam0, ∀ v ∈ Wb, opT γ v ∈ Wb)
    (hΦ : ∀ μ ∈ Mlist, (Pi.single μ (1 : F) : V6 → F) ∈ Wb →
      (Pi.single (wE • μ) (1 : F) : V6 → F) ∈ Wb)
    (hne : Wb ≠ ⊥) : ∀ μ ∈ Mlist, (Pi.single μ (1 : F) : V6 → F) ∈ Wb := by
  have hscale : ∀ (ν : V6) (e : F), e ≠ 0 → (Pi.single ν e : V6 → F) ∈ Wb →
      ∀ c : F, (Pi.single ν c : V6 → F) ∈ Wb := by
    intro ν e he hm c
    have h := Wb.smul_mem (c * e⁻¹) hm
    rwa [← Pi.single_smul', smul_eq_mul, mul_assoc, inv_mul_cancel₀ he, mul_one] at h
  have hcomp : ∀ ν₀ ∈ Mlist, (∀ c : F, (Pi.single ν₀ c : V6 → F) ∈ Wb) →
      ∀ ν ∈ Mlist, ν 3 = ν₀ 3 → ∀ c : F, (Pi.single ν c : V6 → F) ∈ Wb := by
    intro ν₀ hν₀ hN ν hν h3 c
    have hP : ∀ x, (x ∈ Mlist ∧ ∀ c : F, (Pi.single x c : V6 → F) ∈ Wb) →
        ∀ y ∈ nbrs x, (y ∈ Mlist ∧ ∀ c : F, (Pi.single y c : V6 → F) ∈ Wb) := by
      rintro x ⟨hx, hxN⟩ y hy
      simp only [nbrs, List.mem_filter, List.mem_map, decide_eq_true_eq] at hy
      obtain ⟨⟨γ, hγ, rfl⟩, hyM⟩ := hy
      refine ⟨hyM, fun c => ?_⟩
      have hγf := gam0_facts γ hγ
      have hxf := Mlist_facts x hx
      have hne := aE_ne_zero (F := F) hγf.1 hγf.2 hxf.1 hxf.2.1 (Mlist_facts _ hyM).1
      have h := hT γ hγ _ (hxN ((aE γ x : F)⁻¹ * c))
      rwa [opT_single, mul_inv_cancel_left₀ hne] at h
    exact (reach_good hP 4 ν₀ ⟨hν₀, hN⟩ ν (component_reach ν₀ hν₀ ν hν h3)).2 c
  obtain ⟨μ, hμ, e, he, hmem⟩ := exists_weight Wb hsupp hT hne
  have hN := hscale μ e he hmem
  have hN' := hscale (wE • μ) 1 one_ne_zero (hΦ μ hμ (hN 1))
  obtain ⟨hwμ, hw3⟩ := wE_Mlist μ hμ
  intro ν hν
  by_cases h : ν 3 = μ 3
  · exact hcomp μ hμ hN ν hν h 1
  · have h' : ν 3 = (wE • μ) 3 := by
      have := Mlist_three ν hν
      have := Mlist_three μ hμ
      have := Mlist_three _ hwμ
      omega
    exact hcomp _ hwμ hN' ν hν h' 1

end Core

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux
