module

public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsCount

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

variable {d : ℕ}

@[expose] def vsupp (v : ↥(coreMod d)) : Finset (Fin d) :=
  Finset.univ.filter fun i => vcoord v i = 1

theorem mem_vsupp {v : ↥(coreMod d)} {i : Fin d} : i ∈ vsupp v ↔ vcoord v i = 1 := by
  simp [vsupp]

theorem vcoord_eq_zero_of_not_mem {v : ↥(coreMod d)} {i : Fin d} (h : i ∉ vsupp v) :
    vcoord v i = 0 := by
  rw [mem_vsupp] at h
  generalize vcoord v i = a at h ⊢
  revert a
  decide

theorem even_card_vsupp (v : ↥(coreMod d)) : Even (vsupp v).card := by
  have h : ∑ i, vcoord v i = 0 := sum_vcoord v
  have h2 : ∑ i, vcoord v i = ((vsupp v).card : ZMod 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => vcoord v i = 1)]
    have h3 : ∑ i ∈ Finset.univ.filter (fun i => ¬ vcoord v i = 1), vcoord v i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : i ∉ vsupp v := by simpa [vsupp] using hi
        exact vcoord_eq_zero_of_not_mem this
    rw [h3, add_zero]
    have h4 : ∑ i ∈ Finset.univ.filter (fun i => vcoord v i = 1), vcoord v i =
        ∑ i ∈ Finset.univ.filter (fun i => vcoord v i = 1), (1 : ZMod 2) :=
      Finset.sum_congr rfl fun i hi => by simpa using hi
    rw [h4]
    simp [vsupp]
  rw [h] at h2
  exact (ZMod.natCast_eq_zero_iff_even).1 h2.symm

theorem coreAct_eq_iff (σ : Perm (Fin d)) (v : ↥(coreMod d)) :
    coreAct d σ v = v ↔ σ ∈ setStab (vsupp v) := by
  constructor
  · intro h x
    have hx := congrArg (fun u => vcoord u (σ x)) h
    simp only [vcoord_coreAct, perm_inv_apply_self] at hx
    simp only [mem_vsupp]
    rw [hx]
  · intro h
    refine vcoord_ext fun i => ?_
    rw [vcoord_coreAct]
    have h1 : σ⁻¹ i ∈ vsupp v ↔ i ∈ vsupp v := by
      have := mem_setStab.1 h (σ⁻¹ i)
      rw [perm_apply_inv_self] at this
      exact this.symm
    simp only [mem_vsupp] at h1
    generalize vcoord v (σ⁻¹ i) = a at h1 ⊢
    generalize vcoord v i = b at h1 ⊢
    revert a b
    decide

theorem altOn_le_setStab (B : Finset (Fin d)) : altOn B ≤ setStab B := by
  intro τ hτ x
  rw [mem_altOn] at hτ
  by_cases hx : x ∈ B
  · constructor
    · intro _; exact hx
    · intro _
      by_contra hτx
      have h1 : τ (τ x) = τ x := hτ.1 _ hτx
      have h2 : τ x = x := τ.injective h1
      exact hτx (by rw [h2]; exact hx)
  · have h1 : τ x = x := hτ.1 x hx
    rw [h1]

end CFSG.CGT.PushingUpLit.SolK
