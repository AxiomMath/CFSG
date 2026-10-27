module

public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

variable {d : ℕ}

theorem eq_one_or_swap {i j : Fin d} (hij : i ≠ j) {σ : Perm (Fin d)}
    (hstab : σ ∈ setStab ({i, j} : Finset (Fin d))) (hfix : ∀ x, x ≠ i → x ≠ j → σ x = x) :
    σ = 1 ∨ σ = swap i j := by
  have hi : σ i ∈ ({i, j} : Finset (Fin d)) := (mem_setStab.1 hstab i).2 (by simp)
  have hj : σ j ∈ ({i, j} : Finset (Fin d)) := (mem_setStab.1 hstab j).2 (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with hi | hi
  · left
    refine Equiv.ext fun x => ?_
    by_cases hxi : x = i
    · subst hxi; simpa using hi
    by_cases hxj : x = j
    · subst hxj
      rcases hj with hj | hj
      · exact absurd (σ.injective (hj.trans hi.symm)) (Ne.symm hij)
      · simpa using hj
    · simpa using hfix x hxi hxj
  · right
    refine Equiv.ext fun x => ?_
    by_cases hxi : x = i
    · subst hxi; simpa using hi
    by_cases hxj : x = j
    · subst hxj
      rcases hj with hj | hj
      · simpa using hj
      · exact absurd (σ.injective (hj.trans hi.symm)) (Ne.symm hij)
    · rw [swap_apply_of_ne_of_ne hxi hxj]
      exact hfix x hxi hxj

theorem card_le_two_mul_fix_swap {i j : Fin d} (hij : i ≠ j) :
    Nat.card ↥(coreMod d) ≤
      2 * Nat.card {v : ↥(coreMod d) // coreAct d (swap i j) v = v} := by
  classical
  let p : ↥(coreMod d) →* Multiplicative (ZMod 2) :=
    MonoidHom.mk' (fun v => Multiplicative.ofAdd (vcoord v i + vcoord v j)) (fun u v => by
      show Multiplicative.ofAdd (vcoord (u * v) i + vcoord (u * v) j) =
        Multiplicative.ofAdd (vcoord u i + vcoord u j) *
          Multiplicative.ofAdd (vcoord v i + vcoord v j)
      rw [vcoord_mul, vcoord_mul, ← ofAdd_add]
      congr 1
      ring)
  have h1 := Subgroup.card_ker_mul_card_range p
  have h2 : Nat.card p.range ≤ 2 := by
    have := Nat.card_le_card_of_injective (fun x : p.range => (x : Multiplicative (ZMod 2)))
      Subtype.val_injective
    rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)),
      show Fintype.card (Multiplicative (ZMod 2)) = 2 from by
        rw [Fintype.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
          ZMod.card]] at this
  have h3 : Nat.card ↥p.ker ≤ Nat.card {v : ↥(coreMod d) // coreAct d (swap i j) v = v} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨(v : ↥(coreMod d)), ?_⟩) ?_
    · have hv : vcoord (v : ↥(coreMod d)) i + vcoord (v : ↥(coreMod d)) j = 0 := by
        have := v.2
        rw [MonoidHom.mem_ker] at this
        exact Multiplicative.ofAdd.injective this
      have hvij : vcoord (v : ↥(coreMod d)) i = vcoord (v : ↥(coreMod d)) j := by
        generalize vcoord (v : ↥(coreMod d)) i = a at hv ⊢
        generalize vcoord (v : ↥(coreMod d)) j = b at hv ⊢
        revert a b
        decide
      refine vcoord_ext fun x => ?_
      rw [vcoord_coreAct]
      by_cases hxi : x = i
      · subst hxi
        simp [hvij]
      by_cases hxj : x = j
      · subst hxj
        simp [hvij]
      · rw [Equiv.swap_inv, swap_apply_of_ne_of_ne hxi hxj]
    · intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab
  have h4 : Nat.card ↥(coreMod d) = Nat.card ↥p.ker * Nat.card p.range := h1.symm
  calc Nat.card ↥(coreMod d) = Nat.card ↥p.ker * Nat.card p.range := h4
    _ ≤ Nat.card ↥p.ker * 2 := Nat.mul_le_mul_left _ h2
    _ ≤ Nat.card {v : ↥(coreMod d) // coreAct d (swap i j) v = v} * 2 :=
        Nat.mul_le_mul_right _ h3
    _ = 2 * Nat.card {v : ↥(coreMod d) // coreAct d (swap i j) v = v} := mul_comm _ _

end CFSG.CGT.PushingUpLit.SolK
