module

public import CFSG.Adapters.TauCetiExceptional.MinusculeLie
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjSigns
public import CFSG.Adapters.TauCetiExceptional.MinusculeMatch

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData

variable {τ : Tag} {D : MinData τ} (R : Type*) [CommRing R]

@[expose] def adjMap (S : AdjSigns τ) (D : MinData τ) :
    RootModule τ R →ₗ[R] Module.End R (Fin D.d →₀ R) :=
  Finsupp.linearCombination R fun l => match l with
    | .inl j => ((S.epsZ j : ℤ) : R) • cartanOp R D j
    | .inr α => ((S.sRoot α.1 : ℤ) : R) • D.rootOp R α.1

variable (S : AdjSigns τ)

theorem adjMap_hVec (j : Fin τ.rank) :
    adjMap R S D (hVec τ R j) = ((S.epsZ j : ℤ) : R) • cartanOp R D j := by
  rw [hVec, adjMap, Finsupp.linearCombination_single, one_smul]

theorem rootVec_eq_single {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootVec τ R α = Finsupp.single (Sum.inr ⟨α, hα⟩) 1 := by
  classical
  rw [rootVec, dite_eq_left hα]

theorem adjMap_rootVec
    (α : Fin τ.rank → ℤ) :
    adjMap R S D (rootVec τ R α) = ((S.sRoot α : ℤ) : R) • D.rootOp R α := by
  by_cases hα : IsRoot τ α
  · rw [rootVec_eq_single R hα, adjMap, Finsupp.linearCombination_single, one_smul]
  · classical
    rw [rootVec, dite_eq_right hα, map_zero, rootOp_eq_zero hα, smul_zero]

theorem one_add_smul_mul_mul_one_sub_smul {M : Type*} [AddCommGroup M] [Module R M]
    (E Y : Module.End R M) (c : R) :
    (1 + c • E) * Y * (1 - c • E) = Y + c • (E * Y - Y * E) - (c * c) • (E * Y * E) := by
  have h1 : ∀ A : Module.End R M, (1 + A) * Y * (1 - A) = Y + (A * Y - Y * A) - A * Y * A :=
    fun A => by noncomm_ring
  rw [h1, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]

theorem xOp_hVec' (i j : Fin τ.rank) (c : R) :
    xOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1) := by
  change xOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

theorem xOp_rootVec_single' (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (Pi.single i 1)) = rootVec τ R (Pi.single i 1) := by
  rw [rootVec_eq_single R (IsRoot.basis i), xOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

theorem xOp_rootVec_neg_single' (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (-Pi.single i 1)) =
      rootVec τ R (-Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1) := by
  rw [rootVec_eq_single R (isRoot_neg_single τ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

theorem xOp_rootVec_of_ne' (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringUp τ i α + 1),
        (((stringDown τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α + (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_eq_single R hα, xOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₁).trans (ite_eq_right h₂)

variable (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)

include hpd in
theorem xOp_rootVec_of_add
    (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) (hr : IsRoot τ (α + Pi.single i 1)) :
    xOp τ R i c (rootVec τ R α) = rootVec τ R α + c • rootVec τ R (α + Pi.single i 1) := by
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  obtain ⟨-, hdown, hup⟩ := string_of_add hpd hα hr
  have h1 := (hint 1).1 (by rwa [one_smul])
  have h2 := fun h => hup ((hint 2).2 h)
  have h3 := fun h => hdown (by
    have := (hint (-1)).2 h
    rwa [neg_smul, one_smul, ← sub_eq_add_neg] at this)
  have hp : stringUp τ i α = 1 := by
    have := h1.2
    by_contra hne
    exact h2 ⟨by omega, by omega⟩
  have hq : stringDown τ i α = 0 := by
    have := h1.2
    by_contra hne
    exact h3 ⟨by omega, by omega⟩
  rw [xOp_rootVec_of_ne' R i c hα h₁ h₂, hp, hq, Finset.sum_range_succ, Finset.sum_range_one]
  simp

theorem xOp_rootVec_of_not_add
    (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1)
    (hr : ¬ IsRoot τ (α + Pi.single i 1)) : xOp τ R i c (rootVec τ R α) = rootVec τ R α := by
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have hp : stringUp τ i α = 0 := by
    by_contra h
    exact hr (by simpa using (hint 1).2 ⟨by omega, by omega⟩)
  rw [xOp_rootVec_of_ne' R i c hα h₁ h₂, hp, Finset.sum_range_one]
  simp

variable {S} (hV : D.Valid) (hS : S.check D = true)

theorem coe_rootUnit_inv
    (γ : Fin τ.rank → ℤ) (c : R) :
    (((rootUnit hV R γ c)⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) =
      1 - c • D.rootOp R γ :=
  rfl

include hV in
theorem rootOp_single_mul_cartanOp_mul
    (i j : Fin τ.rank) :
    D.rootOp R (Pi.single i 1) * cartanOp R D j * D.rootOp R (Pi.single i 1) = 0 := by
  have h := cartanOp_comm_rootOp hV R (IsRoot.basis i) j
  have e : cartanOp R D j * D.rootOp R (Pi.single i 1) = D.rootOp R (Pi.single i 1) *
      cartanOp R D j + ((toWeight (Pi.single i 1) j : ℤ) : R) • D.rootOp R (Pi.single i 1) := by
    rw [← h]
    abel
  rw [mul_assoc, e, mul_add, ← mul_assoc, hV.rootOp_mul_self, zero_mul, mul_smul_comm,
    hV.rootOp_mul_self, smul_zero, add_zero]

include hV hS hpd in
theorem rootUnit_conj_adjMap_single
    (i : Fin τ.rank) (c : R) (l : Label τ) :
    (rootUnit hV R (Pi.single i 1) c : Module.End R (Fin D.d →₀ R)) *
        adjMap R S D (Finsupp.single l 1) *
          (((rootUnit hV R (Pi.single i 1) c)⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) :
            Module.End R (Fin D.d →₀ R)) =
      adjMap R S D (xOp τ R i c (Finsupp.single l 1)) := by
  rw [coe_rootUnit, coe_rootUnit_inv, one_add_smul_mul_mul_one_sub_smul]
  rcases l with j | ⟨α, hα⟩
  · change _ = adjMap R S D (xOp τ R i c (hVec τ R j))
    rw [xOp_hVec', map_add, map_smul, adjMap_hVec, adjMap_rootVec, AdjSigns.sRoot_single hS,
      show (Finsupp.single (Sum.inl j) 1 : RootModule τ R) = hVec τ R j from rfl, adjMap_hVec]
    have hc := cartanOp_comm_rootOp hV R (IsRoot.basis i) j
    rw [toWeight_single] at hc
    have h1 : D.rootOp R (Pi.single i 1) * (((S.epsZ j : ℤ) : R) • cartanOp R D j) -
        (((S.epsZ j : ℤ) : R) • cartanOp R D j) * D.rootOp R (Pi.single i 1) =
          -(((S.epsZ j * τ.cartan j i : ℤ) : R) • D.rootOp R (Pi.single i 1)) := by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ← neg_sub, hc, smul_neg, smul_smul]
      push_cast
      rfl
    have h2 : D.rootOp R (Pi.single i 1) * (((S.epsZ j : ℤ) : R) • cartanOp R D j) *
        D.rootOp R (Pi.single i 1) = 0 := by
      rw [mul_smul_comm, smul_mul_assoc, rootOp_single_mul_cartanOp_mul R hV, smul_zero]
    rw [h1, h2, smul_zero, sub_zero, smul_neg, smul_smul, smul_smul, ← neg_smul]
    congr 2
    rcases AdjSigns.cartan_cases hS j i with rfl | h0 | ⟨h0, he⟩
    · rw [Tag.cartan_self]
      push_cast
      ring
    · rw [h0]
      push_cast
      ring
    · rw [h0, he]
      push_cast
      ring
  · rw [← rootVec_eq_single R hα, adjMap_rootVec]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xOp_rootVec_single', adjMap_rootVec, mul_smul_comm, smul_mul_assoc, sub_self,
        smul_zero, add_zero, smul_mul_assoc, mul_assoc, hV.rootOp_mul_self, mul_zero, smul_zero,
        smul_zero, sub_zero]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xOp_rootVec_neg_single', map_add, map_add, map_smul, map_smul, adjMap_rootVec,
        adjMap_hVec, adjMap_rootVec, AdjSigns.sRoot_neg_single hS, AdjSigns.sRoot_single hS,
        mul_smul_comm, smul_mul_assoc, ← smul_sub, rootOp_single_comm_neg_single hV R i,
        smul_mul_assoc, rootOp_single_mul_neg_single_mul_single hV R i]
      push_cast
      rw [neg_smul, smul_neg, sub_eq_add_neg, pow_two]
    by_cases hr : IsRoot τ (α + Pi.single i 1)
    · have hr' : IsRoot τ (Pi.single i 1 + α) := by rwa [add_comm]
      rw [xOp_rootVec_of_add R hpd i c hα h₁ h₂ hr, map_add, map_smul, adjMap_rootVec,
        adjMap_rootVec, mul_smul_comm, smul_mul_assoc, ← smul_sub,
        AdjSigns.rootOp_single_comm hS hV R hα i hr', smul_mul_assoc,
        rootOp_single_mul_mul_single hV R hα i hr'.ne_zero, smul_zero, smul_zero, sub_zero,
        add_comm (Pi.single i 1) α]
      simp only [smul_smul]
      congr 2
      have h' : ((S.sRoot α : ℤ) : R) * (S.sRoot α : R) = 1 := by
        rw [← Int.cast_mul, S.sRoot_mul_self, Int.cast_one]
      push_cast
      linear_combination (c * (S.sRoot (α + Pi.single i 1) : R)) * h'
    · have hr' : ¬ IsRoot τ (Pi.single i 1 + α) := by rwa [add_comm]
      have hne : Pi.single i 1 + α ≠ 0 := fun h => h₂ (by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact h)
      have hcomm := (hV.pairRel (R := R) (IsRoot.basis i) hα hne).2 hr'
      rw [xOp_rootVec_of_not_add R i c hα h₁ h₂ hr, adjMap_rootVec, mul_smul_comm,
        smul_mul_assoc, hcomm, sub_self, smul_zero, add_zero, smul_mul_assoc, mul_assoc,
        hV.rootOp_mul_self, mul_zero, smul_zero, smul_zero, sub_zero]

include hV hS hpd in
theorem rootUnit_conj_adjMap
    (i : Fin τ.rank) (c : R) (v : RootModule τ R) :
    (rootUnit hV R (Pi.single i 1) c : Module.End R (Fin D.d →₀ R)) * adjMap R S D v *
        (((rootUnit hV R (Pi.single i 1) c)⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) :
          Module.End R (Fin D.d →₀ R)) =
      adjMap R S D (xOp τ R i c v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero, mul_zero, zero_mul]
  | add v w hv hw => rw [map_add, map_add, map_add, mul_add, add_mul, hv, hw]
  | single l b =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, mul_smul_comm, smul_mul_assoc,
      rootUnit_conj_adjMap_single R hpd hV hS i c l]

end CFSG.TauCetiBridge.Minuscule
