module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRS3A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRS3B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fzr_invol_coset {X : Subgroup G} {rho y : G} (hX : IsPGroup 2 X)
    (hrX : ∀ x ∈ X, rho * x * rho⁻¹ ∈ X) (hyX : ∀ x ∈ X, y * x * y⁻¹ ∈ X)
    (hr3 : rho ^ 3 = 1) (hy : orderOf y = 2) (hyr : y * rho * y⁻¹ = rho⁻¹)
    (hfpf : ∀ x ∈ X, rho * x * rho⁻¹ = x → x = 1) :
    {j : G | (∃ s ∈ X, j = y * s) ∧ orderOf j = 2} = {j : G | ∃ w ∈ X, j = w * y * w⁻¹} ∧
      Nat.card ↥(X ⊓ Subgroup.centralizer ({y} : Set G)) ^ 2 = Nat.card ↥X := by
  have hA : ∀ g ∈ ({rho, y} : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    have hg' : g = rho ∨ g = y := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg
    rcases hg' with rfl | rfl
    · exact hrX x hx
    · exact hyX x hx
  obtain ⟨n, W, h0, hn, hle, hinv, hcomm, hsq⟩ :=
    fzr_series_exists (A := ({rho, y} : Set G)) hX hA
  have hWX : ∀ i ≤ n, W i ≤ X := by
    intro i
    induction i with
    | zero =>
        intro _
        rw [h0]
    | succ i ih =>
        intro hi
        exact le_trans (hle i (by omega)) (ih (by omega))
  have hWp : ∀ i ≤ n, IsPGroup 2 (W i) := fun i hi => hX.to_le (hWX i hi)
  have htnorm : ∀ i ≤ n, ∀ g ∈ W i, y * g * y⁻¹ ∈ W i :=
    fun i hi g hg => hinv i hi y (by simp) g hg
  have hreg : ∀ i < n, ActsRegularly y (W (i + 1)) (W i) := by
    intro i hi
    have hi' : i + 1 ≤ n := by omega
    have hrN : ∀ x ∈ W (i + 1), rho * x * rho⁻¹ ∈ W (i + 1) :=
      fun x hx => hinv (i + 1) hi' rho (by simp) x hx
    refine fzr_regular_section (M := W i) (N := W (i + 1)) (hcomm i hi) (hsq i hi)
      ?_ hrN hr3 hyr ?_
    · intro x hx
      exact hinv i hi.le rho (by simp) x hx
    · intro m hm hconj
      exact fzr_fpf_section (hWp i hi.le) (hle i hi) (hcomm i hi) hrN hr3
        (fun x hx hfix => hfpf x (hWX i hi.le hx) hfix) m hm hconj
  exact lemma36 X y hy n W h0 hn hle htnorm hcomm hsq hreg

theorem fzr_conj_of_invol_mul {X : Subgroup G} {rho y : G} (hX : IsPGroup 2 X)
    (hrX : ∀ x ∈ X, rho * x * rho⁻¹ ∈ X) (hyX : ∀ x ∈ X, y * x * y⁻¹ ∈ X)
    (hr3 : rho ^ 3 = 1) (hy : orderOf y = 2) (hyr : y * rho * y⁻¹ = rho⁻¹)
    (hfpf : ∀ x ∈ X, rho * x * rho⁻¹ = x → x = 1) {x : G} (hx : x ∈ X)
    (hxy : orderOf (x * y) = 2) : ∃ w ∈ X, w * y * w⁻¹ = x * y := by
  have hy2 : y * y = 1 := by
    rw [← pow_two, ← hy]
    exact pow_orderOf_eq_one y
  have hyinv : y⁻¹ = y := inv_eq_iff_mul_eq_one.mpr hy2
  have hset := (fzr_invol_coset hX hrX hyX hr3 hy hyr hfpf).1
  have hj : (x * y) ∈ {j : G | (∃ s ∈ X, j = y * s) ∧ orderOf j = 2} := by
    refine ⟨⟨y * x * y⁻¹, hyX x hx, ?_⟩, hxy⟩
    rw [hyinv]
    calc x * y = 1 * (x * y) := (one_mul _).symm
      _ = (y * y) * (x * y) := by rw [← hy2]
      _ = y * (y * x * y) := by group
  rw [hset] at hj
  obtain ⟨w, hw, hwj⟩ := hj
  exact ⟨w, hw, hwj.symm⟩

end CFSG.OddStandard.SmallF3.FritzII
