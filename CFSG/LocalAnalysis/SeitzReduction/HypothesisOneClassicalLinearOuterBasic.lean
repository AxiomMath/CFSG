module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic

public section

namespace CFSG.SeitzReduction

open Subgroup

variable {C : Type*} [Group C]

theorem map_comap_conj_eq_of_le_range {N : Subgroup (MulAut C)}
    (hN : N ≤ (MulAut.conj : C →* MulAut C).range) :
    (N.comap (MulAut.conj : C →* MulAut C)).map (MulAut.conj : C →* MulAut C) = N := by
  rw [Subgroup.map_comap_eq, inf_eq_right.mpr hN]

theorem mem_centralizer_of_forall_comap_conj {N : Subgroup (MulAut C)}
    (hN : N ≤ (MulAut.conj : C →* MulAut C).range) {β : MulAut C}
    (hβ : ∀ c ∈ N.comap (MulAut.conj : C →* MulAut C), β c = c) :
    β ∈ centralizer (N : Set (MulAut C)) := by
  rw [mem_centralizer_iff]
  intro y hy
  rw [SetLike.mem_coe, ← map_comap_conj_eq_of_le_range hN] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  have h1 := mul_conj_mul_inv_eq_conj β c
  rw [hβ c hc, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem apply_eq_of_mem_comap_conj (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    {x : MulAut C} {N : Subgroup (MulAut C)} (hNx : N ≤ centralizer ({x} : Set (MulAut C)))
    {c : C} (hc : c ∈ N.comap (MulAut.conj : C →* MulAut C)) : x c = c :=
  apply_eq_of_mul_conj_eq hinj (mem_centralizer_singleton_iff.mp (hNx hc)).symm

theorem involutionCriterion_of_inner_commutator [Finite C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {x : MulAut C}
    {A P : Subgroup (MulAut C)} (hAP : A ≤ P)
    (hPinn : P ≤ (MulAut.conj : C →* MulAut C).range)
    (hPx : P ≤ centralizer ({x} : Set (MulAut C))) (hA : A ≤ ⁅A, P⁆)
    (hsq : ∀ β ∈ centralizer ({x} : Set (MulAut C)) ⊓ centralizer (A : Set (MulAut C)),
      β ^ 2 = 1) :
    InvolutionCriterion x := by
  set ι : C →* MulAut C := MulAut.conj with hι
  have hAinn : A ≤ ι.range := hAP.trans hPinn
  have hmapA := map_comap_conj_eq_of_le_range hAinn
  have hmapP := map_comap_conj_eq_of_le_range hPinn
  have hA₀P₀ : A.comap ι ≤ P.comap ι := Subgroup.comap_mono hAP
  have hA₀ : A.comap ι ≤ ⁅A.comap ι, P.comap ι⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective hinj, Subgroup.map_commutator, hmapA, hmapP]
    exact hA
  have hD := le_closure_odd_fixed_of_le_commutator hA₀P₀
    (fun c hc => apply_eq_of_mem_comap_conj hinj hPx hc) hA₀
  refine involutionCriterion_of_fixes hD fun β hβx hβA => hsq β (mem_inf.mpr
    ⟨mem_centralizer_singleton_iff.mpr hβx, mem_centralizer_of_forall_comap_conj hAinn hβA⟩)

theorem involutionCriterion_of_inner_perfect [Finite C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {x : MulAut C} (hx : x ^ 2 = 1)
    {N : Subgroup (MulAut C)} (hNinn : N ≤ (MulAut.conj : C →* MulAut C).range)
    (hNx : N ≤ centralizer ({x} : Set (MulAut C))) (hperf : ⁅N, N⁆ = N)
    (hC : centralizer ({x} : Set (MulAut C)) ⊓ centralizer (N : Set (MulAut C)) ≤ zpowers x) :
    InvolutionCriterion x :=
  involutionCriterion_of_inner_commutator hinj le_rfl hNinn hNx hperf.ge fun β hβ => by
    rcases eq_one_or_eq_of_mem_zpowers hx (hC hβ) with rfl | rfl
    · exact one_pow 2
    · exact hx

end CFSG.SeitzReduction
