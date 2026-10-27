module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8T
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix Finset

variable {G : Type*} [Group G]

theorem ECoord.mat_pow {C : ECoord G} {x : G} (hx : x ∈ normalizer (C.E : Set G)) (k : ℕ) :
    C.mat (x ^ k) = C.mat x ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, C.mat_one]
  | succ k ih => rw [pow_succ, pow_succ, C.mat_mul (pow_mem hx k) hx, ih]

theorem ECoord.mat_inv_eq {C : ECoord G} {z : G} (hz : z ∈ normalizer (C.E : Set G)) {A A' : M4}
    (hz' : C.mat z = A) (hAA : A * A' = 1) : C.mat z⁻¹ = A' := by
  calc C.mat z⁻¹ = C.mat z⁻¹ * (A * A') := by rw [hAA, mul_one]
    _ = (C.mat z⁻¹ * C.mat z) * A' := by rw [← hz', mul_assoc]
    _ = A' := by rw [C.mat_inv_mul hz, one_mul]

theorem mem_tConjClass {T : Subgroup G} {x y : G} :
    y ∈ tConjClass T x ↔ ∃ z ∈ T, z * x * z⁻¹ = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

section ClassLemmas

variable {C : ECoord G} {tl : List M4} {hone : (1 : M4) ∈ tl}
  {hmul : ∀ A ∈ tl, ∀ B ∈ tl, A * B ∈ tl} {hinv : ∀ A ∈ tl, ∃ B ∈ tl, A * B = 1}

theorem class_le_orbit [Finite G] {x : G} (hx : x ∈ C.E) :
    (tConjClass (Tsub C tl hone hmul hinv) x).ncard ≤
      ((tl.map fun A => A *ᵥ C.vec x).toFinset).card := by
  have hsub : tConjClass (Tsub C tl hone hmul hinv) x ⊆
      C.elt '' (((tl.map fun A => A *ᵥ C.vec x).toFinset : Finset V4) : Set V4) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_tConjClass.1 hy
    refine ⟨C.mat z *ᵥ C.vec x, ?_, ?_⟩
    · simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
      exact ⟨C.mat z, hz.2, rfl⟩
    · rw [← C.conj_elt hz.1, C.elt_vec hx]
  calc (tConjClass (Tsub C tl hone hmul hinv) x).ncard
      ≤ (C.elt '' (((tl.map fun A => A *ᵥ C.vec x).toFinset : Finset V4) : Set V4)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (((tl.map fun A => A *ᵥ C.vec x).toFinset : Finset V4) : Set V4).ncard :=
        Set.ncard_image_le (Set.toFinite _)
    _ = ((tl.map fun A => A *ᵥ C.vec x).toFinset).card := Set.ncard_coe_finset _

theorem orbit_le_class [Finite G] (hR : ∀ A ∈ tl, ∃ z ∈ Tsub C tl hone hmul hinv, C.mat z = A)
    {x : G} (hx : x ∈ C.E) :
    ((tl.map fun A => A *ᵥ C.vec x).toFinset).card ≤
      (tConjClass (Tsub C tl hone hmul hinv) x).ncard := by
  have hsub : C.elt '' (((tl.map fun A => A *ᵥ C.vec x).toFinset : Finset V4) : Set V4) ⊆
      tConjClass (Tsub C tl hone hmul hinv) x := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hv
    obtain ⟨A, hA, rfl⟩ := hv
    obtain ⟨z, hz, hzA⟩ := hR A hA
    refine mem_tConjClass.2 ⟨z, hz, ?_⟩
    calc z * x * z⁻¹ = z * C.elt (C.vec x) * z⁻¹ := by rw [C.elt_vec hx]
      _ = C.elt (C.mat z *ᵥ C.vec x) := C.conj_elt hz.1 _
      _ = C.elt (A *ᵥ C.vec x) := by rw [hzA]
  calc ((tl.map fun A => A *ᵥ C.vec x).toFinset).card
      = (((tl.map fun A => A *ᵥ C.vec x).toFinset : Finset V4) : Set V4).ncard :=
        (Set.ncard_coe_finset _).symm
    _ = (C.elt '' (((tl.map fun A => A *ᵥ C.vec x).toFinset : Finset V4) : Set V4)).ncard :=
        (Set.ncard_image_of_injective _ C.elt_injective).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem conj_mul_elt {C : ECoord G} {x : G} (hx : x ∈ normalizer (C.E : Set G)) (v : V4) :
    C.elt v * x * (C.elt v)⁻¹ = C.elt ((1 - C.mat x) *ᵥ v) * x := by
  have h1 : x * (C.elt v)⁻¹ * x⁻¹ = C.elt (-(C.mat x *ᵥ v)) := by
    rw [← C.elt_neg, C.elt_neg, ← Matrix.mulVec_neg, ← C.conj_elt hx, ← C.elt_neg]
  calc C.elt v * x * (C.elt v)⁻¹ = C.elt v * (x * (C.elt v)⁻¹ * x⁻¹) * x := by group
    _ = C.elt v * C.elt (-(C.mat x *ᵥ v)) * x := by rw [h1]
    _ = C.elt ((1 - C.mat x) *ᵥ v) * x := by
      rw [← C.elt_add, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_add_neg]

theorem class_ge [Finite G] (hR : ∀ A ∈ tl, ∃ z ∈ Tsub C tl hone hmul hinv, C.mat z = A)
    {x : G} (hx : x ∈ Tsub C tl hone hmul hinv) :
    ∑ B' ∈ clSet tl (C.mat x), (imSet B').card ≤
      (tConjClass (Tsub C tl hone hmul hinv) x).ncard := by
  classical
  set T := Tsub C tl hone hmul hinv with hTdef
  have hex : ∀ B' ∈ clSet tl (C.mat x), ∃ z ∈ T, C.mat (z * x * z⁻¹) = B' := by
    intro B' hB'
    obtain ⟨⟨A, A'⟩, hp, rfl⟩ := mem_clSet.1 hB'
    obtain ⟨hA, hA', hAA⟩ := mem_invPairs hp
    obtain ⟨z, hz, hzA⟩ := hR A hA
    refine ⟨z, hz, ?_⟩
    have hzi : C.mat z⁻¹ = A' := C.mat_inv_eq hz.1 hzA hAA
    rw [C.mat_mul (mul_mem hz.1 hx.1) (inv_mem hz.1), C.mat_mul hz.1 hx.1, hzi, hzA]
  let rep : M4 → G := fun B' =>
    if hB : ∃ z ∈ T, C.mat (z * x * z⁻¹) = B' then hB.choose * x * hB.choose⁻¹ else 1
  have hrep : ∀ B' ∈ clSet tl (C.mat x),
      (∃ z ∈ T, rep B' = z * x * z⁻¹) ∧ C.mat (rep B') = B' := by
    intro B' hB'
    have hB := hex B' hB'
    have hspec := hB.choose_spec
    have e : rep B' = hB.choose * x * hB.choose⁻¹ := by simp only [rep, hB, ↓reduceDIte]
    rw [e]
    exact ⟨⟨hB.choose, hspec.1, rfl⟩, hspec.2⟩
  let S : Finset (Σ _ : M4, V4) := (clSet tl (C.mat x)).sigma fun B' => imSet B'
  have hψ : ∀ p ∈ (S : Set (Σ _ : M4, V4)), C.elt p.2 * rep p.1 ∈ tConjClass T x := by
    intro p hp
    simp only [S, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨⟨z, hz, hzr⟩, hmat⟩ := hrep p.1 hp1
    simp only [imSet, Finset.mem_image, Finset.mem_univ, true_and] at hp2
    obtain ⟨v, hv⟩ := hp2
    have hxr : rep p.1 ∈ T := by rw [hzr]; exact T.mul_mem (T.mul_mem hz hx) (T.inv_mem hz)
    have hE : C.elt v * z ∈ T := T.mul_mem (E_le_Tsub (C.elt_mem v)) hz
    refine mem_tConjClass.2 ⟨C.elt v * z, hE, ?_⟩
    have h1 := conj_mul_elt hxr.1 v
    rw [hmat, hv, hzr] at h1
    rw [hzr, ← h1]
    group
  have hinj :
      Set.InjOn (fun p : (Σ _ : M4, V4) => C.elt p.2 * rep p.1) (S : Set (Σ _ : M4, V4)) := by
    rintro ⟨B₁, w₁⟩ h₁ ⟨B₂, w₂⟩ h₂ heq
    simp only [S, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at h₁ h₂
    simp only at heq h₁ h₂
    have hmat : ∀ (B : M4) (w : V4), B ∈ clSet tl (C.mat x) →
        C.mat (C.elt w * rep B) = B := by
      intro B w hB
      obtain ⟨⟨z, hz, hzr⟩, hm⟩ := hrep B hB
      have hxr : rep B ∈ T := by rw [hzr]; exact T.mul_mem (T.mul_mem hz hx) (T.inv_mem hz)
      have hEn : C.elt w ∈ normalizer (C.E : Set G) := le_normalizer (C.elt_mem w)
      have h1 : C.mat (C.elt w) = 1 := (C.mat_eq_one_iff hEn).2 fun e he => C.comm (C.elt_mem w) he
      rw [C.mat_mul hEn hxr.1, h1, one_mul, hm]
    have hB : B₁ = B₂ := by
      have := congrArg C.mat heq
      rwa [hmat B₁ w₁ h₁.1, hmat B₂ w₂ h₂.1] at this
    subst hB
    have : C.elt w₁ = C.elt w₂ := mul_right_cancel heq
    rw [C.elt_injective this]
  have hcard : S.card = ∑ B' ∈ clSet tl (C.mat x), (imSet B').card := Finset.card_sigma _ _
  rw [← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn _ hψ hinj (Set.toFinite _)

end ClassLemmas

end CFSG.EvenSporadicStandard.TwoHS
