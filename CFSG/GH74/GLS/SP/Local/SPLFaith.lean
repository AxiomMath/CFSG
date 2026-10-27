module

public import CFSG.GH74.GLS.SP.GlueBN

public section

namespace CFSG.GH74.GLS.SP

open Subgroup CFSG.GH74.BNPair CFSG.GroupActions
open scoped Pointwise


variable {X : Type*} [Group X] {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

namespace RGD2

variable (R : RGD2 n H r₁ r₂ U root)

include R in
theorem parabolic_inf [(cartan (H ⊔ U) R.N).Normal] (hgen : (H ⊔ U) ⊔ R.N = ⊤) :
    parabolic (H ⊔ U) R.N {R.w₁} ⊓ parabolic (H ⊔ U) R.N {R.w₂} = H ⊔ U := by
  classical
  have hT := R.isTitsSystem hgen
  have hP := hT.proposition302
  have hS1 : ({R.w₁} : Finset (WeylGroup (H ⊔ U) R.N)) ⊆ {R.w₁, R.w₂} := by simp
  have hS2 : ({R.w₂} : Finset (WeylGroup (H ⊔ U) R.N)) ⊆ {R.w₁, R.w₂} := by simp
  have hB1 : H ⊔ U ≤ parabolic (H ⊔ U) R.N {R.w₁} := by
    have := hT.le_parabolic hS1
    simpa using this
  have hB2 : H ⊔ U ≤ parabolic (H ⊔ U) R.N {R.w₂} := by
    have := hT.le_parabolic hS2
    simpa using this
  obtain ⟨J, hJS, hQJ⟩ := hP.exists_parabolic _ (le_inf hB1 hB2)
  have hJ1 : J ⊆ {R.w₁} := by
    refine (hP.parabolic_le_iff J {R.w₁} hJS hS1).1 ?_
    rw [← hQJ]
    simp
  have hJ2 : J ⊆ {R.w₂} := by
    refine (hP.parabolic_le_iff J {R.w₂} hJS hS2).1 ?_
    rw [← hQJ]
    simp
  have hJe : J = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have h1 := Finset.mem_singleton.1 (hJ1 hx)
    have h2 := Finset.mem_singleton.1 (hJ2 hx)
    exact R.weyl_ne (h1.symm.trans h2)
  rw [hQJ, hJe]
  simpa using hP.parabolic_empty

include R in
theorem normalizer_B (hgen : (H ⊔ U) ⊔ R.N = ⊤) :
    Subgroup.normalizer ((H ⊔ U : Subgroup X) : Set X) = H ⊔ U := by
  classical
  have := R.cartan_normal
  have hT := R.isTitsSystem hgen
  have h := hT.normalizer_parabolic (J := ∅) (Finset.empty_subset _)
  rw [Finset.coe_empty, parabolic_empty] at h
  exact h

include R in
theorem faithful [(cartan (H ⊔ U) R.N).Normal] (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot n i → ∀ x ∈ root i, g * x = x * g) → g = 1) :
    FaithfulOnBuilding (H ⊔ U) R.N R.w₁ R.w₂ := by
  classical
  intro g hg
  have hinf := R.parabolic_inf hgen
  have hcore : ∀ x : X, x * g * x⁻¹ ∈ H ⊔ U := by
    intro x
    rw [← hinf]
    constructor
    · have hv := hg _ (Or.inl ⟨x, rfl⟩ : _ ∈ rankTwoVertices (H ⊔ U) R.N R.w₁ R.w₂)
      have hx : x * g ∈ ((parabolic (H ⊔ U) R.N {R.w₁} : Subgroup X) : Set X) * {x} * {g} :=
        Set.mem_mul.2 ⟨x, Set.mem_mul.2 ⟨1, (parabolic (H ⊔ U) R.N {R.w₁}).one_mem, x, rfl,
          one_mul x⟩, g, rfl, rfl⟩
      rw [hv] at hx
      obtain ⟨p, hp, y, hy, hpy⟩ := Set.mem_mul.1 hx
      rw [Set.mem_singleton_iff] at hy
      rw [hy] at hpy
      have : x * g * x⁻¹ = p := by rw [← hpy]; group
      rw [this]
      exact hp
    · have hv := hg _ (Or.inr ⟨x, rfl⟩ : _ ∈ rankTwoVertices (H ⊔ U) R.N R.w₁ R.w₂)
      have hx : x * g ∈ ((parabolic (H ⊔ U) R.N {R.w₂} : Subgroup X) : Set X) * {x} * {g} :=
        Set.mem_mul.2 ⟨x, Set.mem_mul.2 ⟨1, (parabolic (H ⊔ U) R.N {R.w₂}).one_mem, x, rfl,
          one_mul x⟩, g, rfl, rfl⟩
      rw [hv] at hx
      obtain ⟨p, hp, y, hy, hpy⟩ := Set.mem_mul.1 hx
      rw [Set.mem_singleton_iff] at hy
      rw [hy] at hpy
      have : x * g * x⁻¹ = p := by rw [← hpy]; group
      rw [this]
      exact hp
  have hsat := R.isSaturated
  unfold IsSaturated at hsat
  have hH : ∀ x : X, x * g * x⁻¹ ∈ H := by
    intro x
    have hmem : x * g * x⁻¹ ∈ (H ⊔ U) ⊓ R.N := by
      rw [hsat, Subgroup.mem_iInf]
      intro m
      show _ ∈ conjBy (m : X) (H ⊔ U)
      rw [mem_conjBy_iff]
      have := hcore ((m : X) * x)
      simpa [mul_assoc] using this
    rwa [R.B_inf_N] at hmem
  have hgH : g ∈ H := by simpa using hH 1
  have hcomm : ∀ i, IsRoot n i → ∀ y ∈ root i, g * y = y * g := by
    intro i hi y hy
    have h1 : y * g * y⁻¹ ∈ H := hH y
    have hc : y * g * y⁻¹ * g⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem hgH)
    have hinv : g * y⁻¹ * g⁻¹ ∈ root i := R.invariant i hi g hgH y⁻¹ ((root i).inv_mem hy)
    have hc2 : y * g * y⁻¹ * g⁻¹ ∈ root i := by
      have := (root i).mul_mem hy hinv
      simpa [mul_assoc] using this
    have h1' : y * g * y⁻¹ * g⁻¹ = 1 := by
      obtain ⟨hi0, hin⟩ := hi
      rcases le_or_gt 1 i with hi1 | hi1
      · have hiU : root i ≤ U := R.root_le_U hi1 (by omega)
        have : y * g * y⁻¹ * g⁻¹ ∈ U ⊓ H := ⟨hiU hc2, hc⟩
        rw [R.U_inf_H] at this
        exact this
      · have hk : y * g * y⁻¹ * g⁻¹ ∈ negGen n root :=
          mem_negGen_of_mem (k := -i) (by omega) (by omega) (by simpa using hc2)
        exact R.meet_one _ ((le_sup_left : H ≤ H ⊔ U) hc) hk
    have : g * y = y * g := by
      have e : y * g * y⁻¹ * g⁻¹ = 1 := h1'
      calc g * y = (y * g * y⁻¹ * g⁻¹)⁻¹ * (y * g) := by group
        _ = y * g := by rw [e]; group
    exact this
  exact hZ g hgH hcomm

end RGD2

end CFSG.GH74.GLS.SP
