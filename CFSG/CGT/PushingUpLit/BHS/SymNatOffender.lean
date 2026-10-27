module

public import CFSG.CGT.PushingUpLit.BHS.SymNatWeight

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6

variable {n : ℕ}

theorem swap_mem_of_card_eq_prod {A : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h2 : ∀ q : OrbQ A, orbSize A q ≤ 2)
    (hcard : Nat.card A = ∏ q : OrbQ A, orbSize A q) {x y : Fin n} (hxy : x ≠ y)
    (hmem : ∃ a ∈ A, a x = y) : Equiv.swap x y ∈ A := by
  classical
  obtain ⟨a, haA, hax⟩ := hmem
  set q : OrbQ A := orbOf A x with hq
  have hy : orbOf A y = q := by rw [← hax]; exact orbOf_apply haA x
  have hbij : Function.Bijective (evRep A) := by
    refine (evRep_injective hc).bijective_of_nat_card_le ?_
    rw [Nat.card_pi, hcard]
    exact le_rfl
  set r : Fin n := orbRep A q with hrdef
  have hr : orbOf A r = q := orbOf_orbRep A q
  have hrxy : r = x ∨ r = y := eq_or_eq_of_orbSize_le_two (h2 q) rfl hy hr hxy
  obtain ⟨r', hr'ne, hr'q, hsw⟩ : ∃ r' : Fin n, r' ≠ r ∧ orbOf A r' = q ∧
      Equiv.swap x y = Equiv.swap r r' := by
    rcases hrxy with h | h
    · exact ⟨y, by rw [h]; exact hxy.symm, hy, by rw [h]⟩
    · exact ⟨x, by rw [h]; exact hxy, rfl, by rw [h]; exact Equiv.swap_comm _ _⟩
  let ζ : (p : OrbQ A) → {w : Fin n // orbOf A w = p} := fun p =>
    if h : p = q then ⟨r', h ▸ hr'q⟩ else ⟨orbRep A p, orbOf_orbRep A p⟩
  have hζq : ζ q = ⟨r', hr'q⟩ := by simp [ζ]
  have hζp : ∀ p : OrbQ A, p ≠ q → ζ p = ⟨orbRep A p, orbOf_orbRep A p⟩ := fun p hp => by
    simp [ζ, hp]
  obtain ⟨b, hb⟩ := hbij.2 ζ
  have hbq : (b : Equiv.Perm (Fin n)) r = r' := by
    have := congrArg Subtype.val (congrFun hb q)
    rw [hζq] at this
    exact this
  have hbp : ∀ p : OrbQ A, p ≠ q → (b : Equiv.Perm (Fin n)) (orbRep A p) = orbRep A p := by
    intro p hp
    have := congrArg Subtype.val (congrFun hb p)
    rw [hζp p hp] at this
    exact this
  have hbr' : (b : Equiv.Perm (Fin n)) r' = r := by
    have h1 : orbOf A ((b : Equiv.Perm (Fin n)) r') = q := by rw [orbOf_apply b.2, hr'q]
    rcases eq_or_eq_of_orbSize_le_two (h2 q) hr hr'q h1 hr'ne.symm with h | h
    · exact h
    · exfalso
      apply hr'ne
      have := (b : Equiv.Perm (Fin n)).injective (h.trans hbq.symm)
      exact this
  have hbeq : (b : Equiv.Perm (Fin n)) = Equiv.swap r r' := by
    refine Equiv.ext fun z => ?_
    by_cases hz : orbOf A z = q
    · rcases eq_or_eq_of_orbSize_le_two (h2 q) hr hr'q hz hr'ne.symm with h | h
      · rw [h, hbq, Equiv.swap_apply_left]
      · rw [h, hbr', Equiv.swap_apply_right]
    · have hbz : (b : Equiv.Perm (Fin n)) z = z :=
        fix_of_fix_orbRep hc b.2 (hbp _ hz)
      have hzr : z ≠ r := fun h => hz (h ▸ hr)
      have hzr' : z ≠ r' := fun h => hz (h ▸ hr'q)
      rw [hbz, Equiv.swap_apply_of_ne_of_ne hzr hzr']
  rw [hsw, ← hbeq]
  exact b.2

theorem eq_closure_swaps {A : Subgroup (Equiv.Perm (Fin n))}
    (hswap : ∀ x y : Fin n, x ≠ y → (∃ a ∈ A, a x = y) → Equiv.swap x y ∈ A) :
    A = Subgroup.closure {t : Equiv.Perm (Fin n) | t ∈ A ∧ t.IsSwap} := by
  apply le_antisymm
  · have key : ∀ m : ℕ, ∀ a ∈ A, a.support.card = m →
        a ∈ Subgroup.closure {t : Equiv.Perm (Fin n) | t ∈ A ∧ t.IsSwap} := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro a ha hm
        by_cases ha1 : a = 1
        · rw [ha1]
          exact Subgroup.one_mem _
        · obtain ⟨x, hx⟩ : ∃ x, a x ≠ x := by
            by_contra hall
            push Not at hall
            exact ha1 (Equiv.ext hall)
          have hxy : x ≠ a x := fun h => hx h.symm
          have hs : Equiv.swap x (a x) ∈ A := hswap x (a x) hxy ⟨a, ha, rfl⟩
          have hsT : Equiv.swap x (a x) ∈
              Subgroup.closure {t : Equiv.Perm (Fin n) | t ∈ A ∧ t.IsSwap} :=
            Subgroup.subset_closure ⟨hs, x, a x, hxy, rfl⟩
          have hlt : (Equiv.swap x (a x) * a).support.card < m := by
            rw [← hm]
            apply Finset.card_lt_card
            refine ⟨fun z hz => ?_, fun hsub => ?_⟩
            · rw [Equiv.Perm.mem_support] at hz ⊢
              intro haz
              apply hz
              have hzx : z ≠ x := fun h => hx (h ▸ haz)
              have hzy : z ≠ a x := by
                intro h
                apply hx
                have : a (a x) = a x := by rw [← h]; exact haz
                exact (a.injective this)
              rw [Equiv.Perm.mul_apply, haz, Equiv.swap_apply_of_ne_of_ne hzx hzy]
            · have h1 : x ∈ a.support := Equiv.Perm.mem_support.2 hx
              have h2 := hsub h1
              rw [Equiv.Perm.mem_support, Equiv.Perm.mul_apply, Equiv.swap_apply_right] at h2
              exact h2 rfl
          have h3 := ih _ hlt (Equiv.swap x (a x) * a) (A.mul_mem hs ha) rfl
          have h4 : a = (Equiv.swap x (a x))⁻¹ * (Equiv.swap x (a x) * a) := by
            rw [inv_mul_cancel_left]
          rw [h4]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hsT) h3
    exact fun a ha => key _ a ha rfl
  · exact (Subgroup.closure_le A).2 fun t ht => ht.1

theorem vcoord_comm_apply (a : Equiv.Perm (Fin n)) (v : ↥(coreMod n)) (i : Fin n) :
    vcoord (coreAct n a v * v⁻¹) i = vcoord v (a⁻¹ i) + vcoord v i := by
  rw [vcoord_mul, vcoord_inv, vcoord_coreAct]

theorem isQuadratic_of_orbSize_le_two {A : Subgroup (Equiv.Perm (Fin n))}
    (h2 : ∀ q : OrbQ A, orbSize A q ≤ 2) : IsQuadratic (A.map (coreAct n)) := by
  unfold IsQuadratic
  rw [G6.commV_le_iff]
  intro x hx v
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
  rw [mem_fixV_map_iff]
  intro b hb i
  show vcoord (coreAct n a v * v⁻¹) (b i) = vcoord (coreAct n a v * v⁻¹) i
  rw [vcoord_comm_apply, vcoord_comm_apply]
  by_cases hbi : b i = i
  · rw [hbi]
  · have hq1 : orbOf A (b i) = orbOf A i := orbOf_apply hb i
    have hq2 : orbOf A (a⁻¹ i) = orbOf A i := orbOf_apply (A.inv_mem ha) i
    have hq3 : orbOf A (a⁻¹ (b i)) = orbOf A i := by rw [orbOf_apply (A.inv_mem ha), hq1]
    rcases eq_or_eq_of_orbSize_le_two (h2 (orbOf A i)) rfl hq1 hq2 (Ne.symm hbi) with h | h
    ·
      have h' : a⁻¹ (b i) = b i := by
        rcases eq_or_eq_of_orbSize_le_two (h2 (orbOf A i)) rfl hq1 hq3 (Ne.symm hbi) with h3 | h3
        · exfalso
          have : a⁻¹ (b i) = a⁻¹ i := h3.trans h.symm
          exact hbi ((a⁻¹).injective this)
        · exact h3
      rw [h, h', CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
    ·
      have h' : a⁻¹ (b i) = i := by
        rcases eq_or_eq_of_orbSize_le_two (h2 (orbOf A i)) rfl hq1 hq3 (Ne.symm hbi) with h3 | h3
        · exact h3
        · exfalso
          have : a⁻¹ (b i) = a⁻¹ i := h3.trans h.symm
          exact hbi ((a⁻¹).injective this)
      rw [h, h', add_comm]

end CFSG.CGT.PushingUpLit.BHS

