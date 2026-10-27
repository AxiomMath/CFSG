module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUGen
public import CFSG.LieType.SeitzGeneration.UnitaryCenters

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} {k : Subfield K}

section Subfield

variable (σk : k ≃+* k) (hσk : ∀ x : k, ((σk x : k) : K) = σ (x : K))

theorem subSU_smul (g : SUid σk n) (v : Fin n → k) :
    (subSU n σk hσk g) • (fun i => (v i : K)) = fun i => (((g • v) i : k) : K) := by
  funext i
  rw [smul_def, smul_def]
  simp only [coe_subSU, Matrix.mulVec, dotProduct, Matrix.map_apply]
  show _ = k.subtype (∑ x, _)
  rw [map_sum]
  simp

theorem subSU_mem_ratSU (hk : ∀ x ∈ k, σ x ∈ k) (g : SUid σk n) :
    subSU n σk hσk g ∈ ratSU σ k hk n := by
  intro i j
  rw [coe_subSU]
  exact ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j |>.2

include hσk in
theorem isCenter_of_isRat (hk : ∀ x ∈ k, σ x ∈ k) (hUk : IsUnitaryInvolution σk) (hn : 3 ≤ n)
    {H : Subgroup (SUid σ n)} (hH : ratSU σ k hk n ≤ H) {e : Fin n → K} (he : IsRat k e)
    (he0 : e ≠ 0) (hie : herm σ e e = 0) (hc : IsCenter H e) {a : Fin n → K} (ha : IsRat k a)
    (hia : herm σ a a = 0) : IsCenter H a := by
  by_cases ha0 : a = 0
  · rw [ha0]
    exact isCenter_zero
  set e' : Fin n → k := fun i => ⟨e i, he i⟩ with he'
  set a' : Fin n → k := fun i => ⟨a i, ha i⟩ with ha'
  have hee : (fun i => (e' i : K)) = e := rfl
  have haa : (fun i => (a' i : K)) = a := rfl
  have he0' : e' ≠ 0 := by
    intro h
    apply he0
    rw [← hee, h]
    rfl
  have ha0' : a' ≠ 0 := by
    intro h
    apply ha0
    rw [← haa, h]
    rfl
  have hie' : herm σk e' e' = 0 := by
    apply Subtype.ext
    have := herm_subtype σk hσk e' e'
    rw [hee, hie] at this
    exact this.symm
  have hia' : herm σk a' a' = 0 := by
    apply Subtype.ext
    have := herm_subtype σk hσk a' a'
    rw [haa, hia] at this
    exact this.symm
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hUk hn he0' hie' ha0' hia'
  have h1 := hc.map (hH (subSU_mem_ratSU σk hσk hk t))
  have h2 := subSU_smul σk hσk t e'
  rw [hee] at h2
  rw [h2, ht] at h1
  exact h1

end Subfield

section Span

theorem isCenter_of_pair_span (hσ : ∀ c, σ (σ c) = c) {H : Subgroup (SUid σ n)}
    {a a' : Fin n → K} (ha : IsCenter H a) (ha' : IsCenter H a') (hne : herm σ a a' ≠ 0)
    {x y : K} (hiso : herm σ (x • a + y • a') (x • a + y • a') = 0) :
    IsCenter H (x • a + y • a') := by
  by_cases hy : y = 0
  · rw [hy, zero_smul, add_zero]
    exact ha.smul hσ x
  have hγ : herm σ a' a = σ (herm σ a a') := herm_conj σ hσ a a'
  set γ : K := herm σ a a' with hγdef
  have hσγ : σ γ ≠ 0 := (map_ne_zero σ).mpr hne
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hy
  have hiso' : σ x * y * γ + x * σ y * σ γ = 0 := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha.1, ha'.1,
      hγ] at hiso
    linear_combination hiso
  have hc : (x / y / γ) + σ (x / y / γ) = 0 := by
    rw [map_div₀, map_div₀]
    field_simp
    linear_combination hiso'
  have h1 := (ha.move ha' hc).smul hσ y
  have h2 : y • (a' + (x / y / γ * herm σ a a') • a) = x • a + y • a' := by
    rw [← hγdef, div_mul_cancel₀ _ hne, smul_add, smul_smul, mul_div_cancel₀ _ hy, add_comm]
  rwa [h2] at h1

end Span

end CFSG.LieType.SeitzGeneration.SUPair
