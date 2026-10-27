module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def wvec (i : Fin 5) : Fin 5 → ZMod 2 := fun j => if j = i then 0 else 1

theorem wvec_even (i : Fin 5) : IsEvenVec (wvec i) := by
  revert i
  unfold IsEvenVec wvec
  decide +kernel

theorem permVec_wvec (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    permVec σ (wvec i) = wvec (σ i) := by
  funext j
  simp only [permVec, wvec, Function.comp_apply, Equiv.symm_apply_eq]

theorem wvec_injective : Function.Injective wvec := by
  intro i j h
  revert i j
  unfold wvec
  decide +kernel

theorem exists_alt_apply (i j : Fin 5) : ∃ σ ∈ alternatingGroup (Fin 5), σ i = j := by
  revert i j
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem alt_stab_decomp (i : Fin 5) {σ : Equiv.Perm (Fin 5)}
    (hσ : σ ∈ alternatingGroup (Fin 5)) (hi : σ i = i) :
    ∃ ρ₁ ∈ alternatingGroup (Fin 5), ∃ ρ₂ ∈ alternatingGroup (Fin 5),
      ρ₁ i = i ∧ ρ₂ i = i ∧ ρ₁ ^ 3 = 1 ∧ ρ₂ ^ 3 = 1 ∧ σ = ρ₁ * ρ₂ := by
  revert hi hσ σ i
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem permVec_cube {σ : Equiv.Perm (Fin 5)} (h : σ ^ 3 = 1) (v : Fin 5 → ZMod 2) :
    permVec σ (permVec σ (permVec σ v)) = v := by
  have h1 : permVec (σ * σ * σ) v = v := by
    rw [show σ * σ * σ = σ ^ 3 from (pow_three' σ).symm, h]
    rfl
  simpa [permVec_mul] using h1

theorem even_eq_sum_wvec {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    (∑ i, v i • wvec i) = v := by
  revert v
  unfold IsEvenVec wvec
  decide +kernel

theorem even_eq_four_wvec {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    ∃ a b c d : Fin 5, v = (wvec a + wvec b) + (wvec c + wvec d) := by
  revert v
  unfold IsEvenVec wvec
  decide +kernel

theorem wvec_add_even (i j : Fin 5) : IsEvenVec (wvec i + wvec j) := by
  revert i j
  unfold IsEvenVec wvec
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
