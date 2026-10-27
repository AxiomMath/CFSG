module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightEndPlus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightEndSign

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup

section Abstract

variable {A X P Q : Type*} [Group A] [MulAction A X] [Group P] [Group Q]

theorem mem_dihedral_of_mem_closure {τ κ : A} (hτ3 : τ ^ 3 = 1) (hκ2 : κ * κ = 1)
    (hκτ : κ * τ * κ⁻¹ = τ⁻¹) {π : A} (hπ : π ∈ closure ({τ, κ} : Set A)) :
    π = 1 ∨ π = τ ∨ π = τ ^ 2 ∨ π = κ ∨ π = τ * κ ∨ π = τ ^ 2 * κ := by
  have hττ2 : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ3
  have hτ2τ : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ3
  have hτ2τ2 : τ ^ 2 * τ ^ 2 = τ := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, hτ3, one_mul]
  have hτinv : τ⁻¹ = τ ^ 2 := inv_eq_of_mul_eq_one_right hττ2
  have hκinv : κ⁻¹ = κ := inv_eq_of_mul_eq_one_right hκ2
  have h1 : κ * τ = τ ^ 2 * κ := by
    rw [← hτinv, ← hκτ, mul_assoc, inv_mul_cancel, mul_one]
  have h2 : κ * τ ^ 2 = τ * κ := by
    rw [sq, ← mul_assoc, h1, mul_assoc, h1, ← mul_assoc, hτ2τ2]
  have hτmul : ∀ y : A, (y = 1 ∨ y = τ ∨ y = τ ^ 2 ∨ y = κ ∨ y = τ * κ ∨ y = τ ^ 2 * κ) →
      (τ * y = 1 ∨ τ * y = τ ∨ τ * y = τ ^ 2 ∨ τ * y = κ ∨ τ * y = τ * κ ∨
        τ * y = τ ^ 2 * κ) := by
    rintro y (h | h | h | h | h | h) <;> rw [h]
    · exact Or.inr (Or.inl (mul_one τ))
    · exact Or.inr (Or.inr (Or.inl (sq τ).symm))
    · exact Or.inl hττ2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← mul_assoc, ← sq])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hττ2, one_mul]))))
  have hτ2mul : ∀ y : A, (y = 1 ∨ y = τ ∨ y = τ ^ 2 ∨ y = κ ∨ y = τ * κ ∨ y = τ ^ 2 * κ) →
      (τ ^ 2 * y = 1 ∨ τ ^ 2 * y = τ ∨ τ ^ 2 * y = τ ^ 2 ∨ τ ^ 2 * y = κ ∨
        τ ^ 2 * y = τ * κ ∨ τ ^ 2 * y = τ ^ 2 * κ) := by
    rintro y (h | h | h | h | h | h) <;> rw [h]
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inl hτ2τ
    · exact Or.inr (Or.inl hτ2τ2)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hτ2τ, one_mul]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hτ2τ2])))))
  have hκmul : ∀ y : A, (y = 1 ∨ y = τ ∨ y = τ ^ 2 ∨ y = κ ∨ y = τ * κ ∨ y = τ ^ 2 * κ) →
      (κ * y = 1 ∨ κ * y = τ ∨ κ * y = τ ^ 2 ∨ κ * y = κ ∨ κ * y = τ * κ ∨
        κ * y = τ ^ 2 * κ) := by
    rintro y (h | h | h | h | h | h) <;> rw [h]
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mul_one _))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))
    · exact Or.inl hκ2
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, h1, mul_assoc, hκ2, mul_one])))
    · exact Or.inr (Or.inl (by rw [← mul_assoc, h2, mul_assoc, hκ2, mul_one]))
  induction hπ using closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left a ha y hy ih =>
    rcases ha with rfl | ha
    · exact hτmul y ih
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hκmul y ih
  | inv_mul_cancel a ha y hy ih =>
    rcases ha with rfl | ha
    · rw [hτinv]
      exact hτ2mul y ih
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hκinv]
      exact hκmul y ih

theorem dihedral_mul_eq {τ κ : A} (hτ3 : τ ^ 3 = 1) (hκτ : κ * τ * κ⁻¹ = τ⁻¹) :
    κ * τ = τ ^ 2 * κ := by
  have hττ2 : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ3
  rw [← inv_eq_of_mul_eq_one_right hττ2, ← hκτ, mul_assoc, inv_mul_cancel, mul_one]

theorem dihedral_mul_sq_eq {τ κ : A} (hτ3 : τ ^ 3 = 1) (hκτ : κ * τ * κ⁻¹ = τ⁻¹) :
    κ * τ ^ 2 = τ * κ := by
  have hτ2τ2 : τ ^ 2 * τ ^ 2 = τ := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, hτ3, one_mul]
  rw [sq, ← mul_assoc, dihedral_mul_eq hτ3 hκτ, mul_assoc, dihedral_mul_eq hτ3 hκτ,
    ← mul_assoc, hτ2τ2]

theorem exists_normalForm_of_triality (c : P →* A) (s : Q →* A) {x y z : X}
    (hxy : x ≠ y) (hyz : y ≠ z)
    (hT : ∀ α : A, α • x = x ∨ α • x = y ∨ α • x = z)
    (hc : ∀ g, c g • x = x ∧ c g • y = y ∧ c g • z = z)
    (hs : ∀ σ, s σ • x = x ∧ s σ • y = y ∧ s σ • z = z)
    (hstab : ∀ β : A, β • x = x → β • y = y → ∃ g σ, β = c g * s σ)
    (hfield : ∀ g σ, c g = s σ → σ = 1)
    (hconj : ∀ (α : A) (g : P), ∃ g', α * c g * α⁻¹ = c g')
    {τ κ : A} (hτ3 : τ ^ 3 = 1) (hτx : τ • x ≠ x) (hκx : κ • x = x) (hκy : κ • y = z)
    (hκ2 : κ * κ = 1) (hκτ : κ * τ * κ⁻¹ = τ⁻¹) (hτs : ∀ σ, τ * s σ = s σ * τ)
    (hκs : ∀ σ, κ * s σ = s σ * κ) :
    ∃ Φ : A →* Q, (∀ g, Φ (c g) = 1) ∧ (∀ σ, Φ (s σ) = σ) ∧
      (∀ π ∈ closure ({τ, κ} : Set A), Φ π = 1 ∧ π ^ 6 = 1 ∧ ∀ σ, π * s σ = s σ * π) ∧
      ∀ α : A, ∃ g, ∃ π ∈ closure ({τ, κ} : Set A), ∃ σ, α = c g * π * s σ := by
  classical
  set Γ : Subgroup A := closure ({τ, κ} : Set A) with hΓ
  have hτΓ : τ ∈ Γ := subset_closure (Set.mem_insert _ _)
  have hκΓ : κ ∈ Γ := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmem : ∀ π ∈ Γ, π = 1 ∨ π = τ ∨ π = τ ^ 2 ∨ π = κ ∨ π = τ * κ ∨ π = τ ^ 2 * κ :=
    fun π hπ => mem_dihedral_of_mem_closure hτ3 hκ2 hκτ hπ
  have h1 := dihedral_mul_eq hτ3 hκτ
  have h2 := dihedral_mul_sq_eq hτ3 hκτ
  have hΓs : ∀ π ∈ Γ, ∀ σ, π * s σ = s σ * π := by
    intro π hπ σ
    have hle : Γ ≤ centralizer (s.range : Set A) := by
      rw [hΓ, closure_le]
      intro a ha
      rw [SetLike.mem_coe, mem_centralizer_iff]
      rintro _ ⟨σ', rfl⟩
      rcases ha with ha | ha
      · rw [ha]
        exact (hτs σ').symm
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact (hκs σ').symm
    exact (mem_centralizer_iff.1 (hle hπ) (s σ) ⟨σ, rfl⟩).symm
  have hord : ∀ π ∈ Γ, π ^ 6 = 1 := by
    intro π hπ
    rcases hmem π hπ with h | h | h | h | h | h <;> rw [h]
    · exact one_pow 6
    · rw [show 6 = 3 * 2 by rfl, pow_mul, hτ3, one_pow]
    · rw [← pow_mul, show 2 * 6 = 3 * 4 by rfl, pow_mul, hτ3, one_pow]
    · rw [show 6 = 2 * 3 by rfl, pow_mul, sq, hκ2, one_pow]
    · have e : τ * κ * (τ * κ) = 1 := by
        rw [mul_assoc, ← mul_assoc κ, h1, ← mul_assoc, ← mul_assoc, ← pow_succ', hτ3, one_mul,
          hκ2]
      rw [show 6 = 2 * 3 by rfl, pow_mul, sq, e, one_pow]
    · have e : τ ^ 2 * κ * (τ ^ 2 * κ) = 1 := by
        rw [mul_assoc, ← mul_assoc κ, h2, ← mul_assoc, ← mul_assoc, ← pow_succ, hτ3, one_mul,
          hκ2]
      rw [show 6 = 2 * 3 by rfl, pow_mul, sq, e, one_pow]
  have hτ2x : τ ^ 2 • x ≠ x := by
    intro h
    apply hτx
    have h3 : (τ * τ ^ 2) • x = τ • x := by rw [mul_smul, h]
    rw [← pow_succ', hτ3, one_smul] at h3
    exact h3.symm
  have hτxτ2x : τ • x ≠ τ ^ 2 • x := by
    intro h
    apply hτx
    have h' : τ⁻¹ • (τ • x) = τ⁻¹ • (τ ^ 2 • x) := by rw [h]
    rw [inv_smul_smul, ← mul_smul, sq, inv_mul_cancel_left] at h'
    exact h'.symm
  have hall : ∀ w : X, (w = x ∨ w = y ∨ w = z) → ∃ a : ℕ, τ ^ a • x = w := by
    intro w hw
    have h0 : τ ^ 0 • x = x := by rw [pow_zero, one_smul]
    rcases hT τ with ht | ht | ht
    · exact absurd ht hτx
    · rcases hT (τ ^ 2) with ht2 | ht2 | ht2
      · exact absurd ht2 hτ2x
      · exact absurd (ht.trans ht2.symm) hτxτ2x
      · rcases hw with hw | hw | hw <;> rw [hw]
        · exact ⟨0, h0⟩
        · exact ⟨1, by rw [pow_one, ht]⟩
        · exact ⟨2, ht2⟩
    · rcases hT (τ ^ 2) with ht2 | ht2 | ht2
      · exact absurd ht2 hτ2x
      · rcases hw with hw | hw | hw <;> rw [hw]
        · exact ⟨0, h0⟩
        · exact ⟨2, ht2⟩
        · exact ⟨1, by rw [pow_one, ht]⟩
      · exact absurd (ht.trans ht2.symm) hτxτ2x
  have hTT : ∀ (α : A) (w : X), (w = x ∨ w = y ∨ w = z) →
      (α • w = x ∨ α • w = y ∨ α • w = z) := by
    intro α w hw
    obtain ⟨a, ha⟩ := hall w hw
    rw [← ha, ← mul_smul]
    exact hT _
  have hfix : ∀ π ∈ Γ, π • x = x → π • y = y → π = 1 := by
    intro π hπ hx hy
    rcases hmem π hπ with h | h | h | h | h | h
    · exact h
    · rw [h] at hx
      exact absurd hx hτx
    · rw [h] at hx
      exact absurd hx hτ2x
    · rw [h, hκy] at hy
      exact absurd hy.symm hyz
    · rw [h, mul_smul, hκx] at hx
      exact absurd hx hτx
    · rw [h, mul_smul, hκx] at hx
      exact absurd hx hτ2x
  have hNF : ∀ α : A, ∃ g, ∃ π ∈ Γ, ∃ σ, α = c g * π * s σ := by
    intro α
    obtain ⟨a, ha⟩ := hall (α • x) (hT α)
    set β₁ := (τ ^ a)⁻¹ * α with hβ₁
    have hα : α = τ ^ a * β₁ := by rw [hβ₁, mul_inv_cancel_left]
    have hβ₁x : β₁ • x = x := by rw [hβ₁, mul_smul, ← ha, inv_smul_smul]
    have hpow : τ ^ a ∈ Γ := pow_mem hτΓ a
    rcases hTT β₁ y (Or.inr (Or.inl rfl)) with hy | hy | hy
    · exact absurd (smul_left_cancel β₁ (hy.trans hβ₁x.symm)).symm hxy
    · obtain ⟨g, σ, hgσ⟩ := hstab β₁ hβ₁x hy
      obtain ⟨g', hg'⟩ := hconj (τ ^ a) g
      refine ⟨g', τ ^ a, hpow, σ, ?_⟩
      rw [hα, hgσ, ← hg']
      group
    · have hκz : κ • z = y := by rw [← hκy, ← mul_smul, hκ2, one_smul]
      obtain ⟨g, σ, hgσ⟩ := hstab (κ * β₁) (by rw [mul_smul, hβ₁x, hκx])
        (by rw [mul_smul, hy, hκz])
      obtain ⟨g', hg'⟩ := hconj (τ ^ a * κ) g
      refine ⟨g', τ ^ a * κ, mul_mem hpow hκΓ, σ, ?_⟩
      have hα' : α = τ ^ a * κ * (κ * β₁) := by
        rw [mul_assoc, ← mul_assoc κ, hκ2, one_mul, hα]
      rw [hα', hgσ, ← hg']
      group
  have hact : ∀ (g : P) (π : A) (σ : Q) (w : X), (w = x ∨ w = y ∨ w = z) →
      (c g * π * s σ) • w = π • w := by
    intro g π σ w hw
    have hsw : s σ • w = w := by
      rcases hw with hw | hw | hw <;> rw [hw]
      exacts [(hs σ).1, (hs σ).2.1, (hs σ).2.2]
    rw [mul_smul, mul_smul, hsw]
    rcases hTT π w hw with h | h | h <;> rw [h]
    exacts [(hc g).1, (hc g).2.1, (hc g).2.2]
  have huniq : ∀ (g g' : P) (π π' : A), π ∈ Γ → π' ∈ Γ → ∀ σ σ' : Q,
      c g * π * s σ = c g' * π' * s σ' → σ = σ' := by
    intro g g' π π' hπ hπ' σ σ' h
    have hx' : π • x = π' • x := by
      rw [← hact g π σ x (Or.inl rfl), h, hact g' π' σ' x (Or.inl rfl)]
    have hy' : π • y = π' • y := by
      rw [← hact g π σ y (Or.inr (Or.inl rfl)), h, hact g' π' σ' y (Or.inr (Or.inl rfl))]
    have hπeq : π' = π := by
      have h0 := hfix (π'⁻¹ * π) (mul_mem (inv_mem hπ') hπ)
        (by rw [mul_smul, hx', inv_smul_smul]) (by rw [mul_smul, hy', inv_smul_smul])
      exact inv_mul_eq_one.1 h0
    rw [hπeq] at h
    obtain ⟨g'', hg''⟩ := hconj π⁻¹ (g⁻¹ * g')
    have e : s σ * (s σ')⁻¹ = π⁻¹ * c (g⁻¹ * g') * π⁻¹⁻¹ := by
      have h' : c g' = c g * π * s σ * (s σ')⁻¹ * π⁻¹ := by
        rw [h]
        group
      rw [map_mul, map_inv, h']
      group
    have h3 : c g'' = s (σ * σ'⁻¹) := by rw [map_mul, map_inv, e, hg'']
    exact mul_inv_eq_one.1 (hfield g'' _ h3)
  choose gf πf hπf σf hf using hNF
  have hσf : ∀ (α : A) (g : P) (π : A) (σ : Q), π ∈ Γ → α = c g * π * s σ → σf α = σ :=
    fun α g π σ hπ h => huniq _ _ _ _ (hπf α) hπ _ _ ((hf α).symm.trans h)
  have hmul : ∀ α β : A, σf (α * β) = σf α * σf β := by
    intro α β
    obtain ⟨g'', hg''⟩ := hconj (πf α * s (σf α)) (gf β)
    have e1 : πf α * s (σf α) * c (gf β) = c g'' * (πf α * s (σf α)) := by
      rw [← hg'']
      group
    have e2 : s (σf α) * πf β = πf β * s (σf α) := (hΓs _ (hπf β) _).symm
    refine hσf (α * β) (gf α * g'') (πf α * πf β) (σf α * σf β)
      (mul_mem (hπf α) (hπf β)) ?_
    calc α * β = (c (gf α) * πf α * s (σf α)) * (c (gf β) * πf β * s (σf β)) :=
          congrArg₂ (· * ·) (hf α) (hf β)
      _ = c (gf α) * (πf α * s (σf α) * c (gf β)) * πf β * s (σf β) := by group
      _ = c (gf α) * (c g'' * (πf α * s (σf α))) * πf β * s (σf β) := by rw [e1]
      _ = c (gf α) * c g'' * πf α * (s (σf α) * πf β) * s (σf β) := by group
      _ = c (gf α) * c g'' * πf α * (πf β * s (σf α)) * s (σf β) := by rw [e2]
      _ = c (gf α * g'') * (πf α * πf β) * s (σf α * σf β) := by
          rw [map_mul, map_mul]
          group
  let Φ : A →* Q :=
    { toFun := σf
      map_one' := hσf 1 1 1 1 (one_mem _) (by rw [map_one, map_one, one_mul, one_mul])
      map_mul' := hmul }
  refine ⟨Φ, fun g => ?_, fun σ => ?_, fun π hπ => ⟨?_, hord π hπ, hΓs π hπ⟩,
    fun α => ⟨gf α, πf α, hπf α, σf α, hf α⟩⟩
  · exact hσf (c g) g 1 1 (one_mem _) (by rw [map_one, mul_one, mul_one])
  · exact hσf (s σ) 1 1 σ (one_mem _) (by rw [map_one, one_mul, one_mul])
  · exact hσf π 1 π 1 hπ (by rw [map_one, map_one, one_mul, mul_one])

end Abstract

section Reflection

open QuadraticMap Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryGL_mulVec_of_charTwo
  symmetryIsometry symmetryAut)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldPair)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem coordinateFieldMap_lastPlaneVec {r : ℕ} (σ : F ≃+* F) :
    coordinateFieldMap (2 * (r + 1)) σ (lastPlaneVec r) = lastPlaneVec (F := F) r := by
  funext i
  rw [coordinateFieldMap_apply, lastPlaneVec]
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp

theorem glFieldAut_symmetryGL_of_fixed {n : ℕ} {v : Fin (2 * n) → F}
    (hv : coordinateQuadPlus n F v = 1) (σ : F ≃+* F)
    (hσv : coordinateFieldMap (2 * n) σ v = v) :
    glFieldAut (Fin (2 * n)) F σ (symmetryGL (coordinateQuadPlus n F) v) =
      symmetryGL (coordinateQuadPlus n F) v := by
  have key : ∀ w : Fin (2 * n) → F,
      (glFieldAut (Fin (2 * n)) F σ (symmetryGL (coordinateQuadPlus n F) v) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) *ᵥ w =
      (symmetryGL (coordinateQuadPlus n F) v :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) *ᵥ w := by
    intro w
    obtain ⟨w', rfl⟩ := (coordinateFieldMap (2 * n) σ).surjective w
    have h1 := coordinateFieldMap_matrix σ (symmetryGL (coordinateQuadPlus n F) v) w'
    rw [matrixLinearEquiv_apply, matrixLinearEquiv_apply] at h1
    have hp := polar_coordinateFieldMap (n := n) σ v w'
    rw [hσv] at hp
    rw [← h1, symmetryGL_mulVec_of_charTwo hv, symmetryGL_mulVec_of_charTwo hv, map_add,
      coordinateFieldMap_smul, hσv, hp]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h

theorem symmetryAut_mul_fieldAutHom_of_fixed {n : ℕ} {v : Fin (2 * n) → F}
    (hv : coordinateQuadPlus n F v = 1) (σ : F ≃+* F)
    (hσv : coordinateFieldMap (2 * n) σ v = v) :
    symmetryAut (coordinateQuadPlus n F) v * fieldAutHom F n σ =
      fieldAutHom F n σ * symmetryAut (coordinateQuadPlus n F) v := by
  change matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ (symmetryIsometry _ v)) *
      matrixProjectiveConjugationHom _ (fieldPair _ _ _) =
    matrixProjectiveConjugationHom _ (fieldPair _ _ _) *
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ (symmetryIsometry _ v))
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change symmetryGL (coordinateQuadPlus n F) v * glFieldAut (Fin (2 * n)) F 1 1 =
      1 * glFieldAut (Fin (2 * n)) F σ (symmetryGL (coordinateQuadPlus n F) v)
    rw [map_one, mul_one, one_mul, glFieldAut_symmetryGL_of_fixed hv σ hσv]
  · change (1 : F ≃+* F) * σ = σ * 1
    rw [one_mul, mul_one]

end Reflection

section NormalForm

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  projectivePointFamily mem_projectivePointFamilyAut_iff projective_inner_le_pointFamilyAut
  regular_coordinateQuadPlus commutator_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCX plusCXstar
  coordinate_plus_pointFamily_orbit_subset)
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit (conj_conjugacyFamily)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryAut symmetryAut_sq
  kappa_derived_eq_conj)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (evenOrthogonalRealization_of_regular)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldPair)
open scoped Pointwise

@[expose] def PlusFourTrialityInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
    ∃ τ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)),
      τ ^ 3 = 1 ∧
      τ • projectivePointFamily (coordinateQuadPlus 4 F) ≠
        projectivePointFamily (coordinateQuadPlus 4 F) ∧
      (∀ σ : F ≃+* F, τ * fieldAutHom F 4 σ = fieldAutHom F 4 σ * τ) ∧
      symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) * τ *
          (symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3))⁻¹ = τ⁻¹ ∧
      ∀ j : Fin 4, ∃ (j' : Fin 4) (x : matrixProjectiveDerived (coordinateQuadPlus 4 F)),
        (plusSignedLevelTorus F (plusNodeSet 4 j) (plusNodeFlip 4 j)).map τ.toMonoidHom =
          (plusSignedLevelTorus F (plusNodeSet 4 j') (plusNodeFlip 4 j')).map
            (MulAut.conj x).toMonoidHom

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem mul_conj_mul_inv_eq_conj_of_mulAut {X : Type*} [Group X] (α : MulAut X) (g : X) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext y
  simp [MulAut.conj_apply]

theorem eq_one_of_conj_eq_fieldAutHom {n : ℕ} (hn : 4 ≤ n)
    (x : matrixProjectiveDerived (coordinateQuadPlus n F)) (σ : F ≃+* F)
    (h : MulAut.conj x = fieldAutHom F n σ) : σ = 1 := by
  obtain ⟨g, hg, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F (by omega)
  have hE := commutator_coordinateQuadPlus (K := F) (n := n) (by omega)
  obtain ⟨-, -, -, -, Fm, hFm, -, -, -⟩ :=
    evenOrthogonalRealization_of_regular hg hFc (by omega : 1 ≤ 2 * n) _ hQ hT hE
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective _ x
  have h1 := hFm (matrixDerivedInclusion _ y)
  have h2 := hFm (fieldPair (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ))
  have h3 : (⟨matrixProjectiveConjugationHom _ (matrixDerivedInclusion _ y), ⟨_, rfl⟩⟩ :
      matrixProjectiveImage (coordinateQuadPlus n F)) =
      ⟨matrixProjectiveConjugationHom _
        (fieldPair (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ)),
        ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    change matrixProjectiveConjugationHom _ _ = fieldAutHom F n σ
    rw [kappa_derived_eq_conj, h]
  rw [h3, h2] at h1
  exact h1

theorem normalForm_four_of_triality
    {τ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))} (hτ3 : τ ^ 3 = 1)
    (hτx : τ • projectivePointFamily (coordinateQuadPlus 4 F) ≠
      projectivePointFamily (coordinateQuadPlus 4 F))
    (hτs : ∀ σ : F ≃+* F, τ * fieldAutHom F 4 σ = fieldAutHom F 4 σ * τ)
    (hκτ : symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) * τ *
      (symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3))⁻¹ = τ⁻¹) :
    ∃ Φ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) →* (F ≃+* F),
      (∀ g, Φ (MulAut.conj g) = 1) ∧ (∀ σ, Φ (fieldAutHom F 4 σ) = σ) ∧
      (∀ π ∈ closure ({τ, symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3)} :
          Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))),
        Φ π = 1 ∧ π ^ 6 = 1 ∧ ∀ σ, π * fieldAutHom F 4 σ = fieldAutHom F 4 σ * π) ∧
      ∀ α, ∃ g, ∃ π ∈ closure ({τ, symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3)} :
          Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))), ∃ σ,
        α = MulAut.conj g * π * fieldAutHom F 4 σ := by
  have hv : coordinateQuadPlus 4 F (lastPlaneVec 3) = 1 := coordinateQuadPlus_lastPlaneVec
  obtain ⟨hκX, hκX'⟩ := symmetryAut_lastPlaneVec_smul_plusCX (F := F)
  have hκim : symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) ∈
      matrixProjectiveImage (coordinateQuadPlus 4 F) := ⟨_, rfl⟩
  have hκx := (mem_image_iff_smul_pointFamily le_rfl _).1 hκim
  have hXX := plusCX_ne_plusCXstar 4 F (by norm_num)
  have hFX : projectivePointFamily (coordinateQuadPlus 4 F) ≠ plusCX 4 F := fun h =>
    hXX (by rw [← hκX, ← h, hκx, h])
  have hO := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := F) rfl
  have hstab : ∀ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)),
      β • projectivePointFamily (coordinateQuadPlus 4 F) =
        projectivePointFamily (coordinateQuadPlus 4 F) →
      β • plusCX 4 F = plusCX 4 F → ∃ g σ, β = MulAut.conj g * fieldAutHom F 4 σ := by
    intro β hβx hβy
    have hβ := (mem_image_iff_smul_pointFamily le_rfl β).2 hβx
    obtain ⟨x, c, h | h⟩ := mem_image_normalForm le_rfl hv hβ
    · exact ⟨x, c, h⟩
    · exfalso
      apply hXX
      rw [← hβy, h, mul_smul, mul_smul, fieldAutHom_smul_plusCX (by norm_num), hκX, plusCXstar,
        conj_conjugacyFamily]
  exact exists_normalForm_of_triality MulAut.conj (fieldAutHom F 4) hFX hXX
    (fun α => hO ⟨α, rfl⟩)
    (fun g => ⟨(mem_projectivePointFamilyAut_iff _ _).1
        (projective_inner_le_pointFamilyAut _ ⟨g, rfl⟩),
      by rw [plusCX, conj_conjugacyFamily], by rw [plusCXstar, conj_conjugacyFamily]⟩)
    (fun σ => ⟨(mem_image_iff_smul_pointFamily le_rfl _).1 ⟨_, rfl⟩,
      fieldAutHom_smul_plusCX (by norm_num) σ, fieldAutHom_smul_plusCXstar (by norm_num) σ⟩)
    hstab (fun g σ h => eq_one_of_conj_eq_fieldAutHom le_rfl g σ h)
    (fun α g => ⟨α g, mul_conj_mul_inv_eq_conj_of_mulAut α g⟩) hτ3 hτx hκx hκX
    (by rw [← sq]; exact symmetryAut_sq _ _) hκτ hτs
    (fun σ => symmetryAut_mul_fieldAutHom_of_fixed hv σ (coordinateFieldMap_lastPlaneVec σ))

theorem omegaPlusFourAutNormalFormInput_of_triality (htri : PlusFourTrialityInput) :
    OmegaPlusFourAutNormalFormInput := by
  intro F _ _ _
  obtain ⟨τ, hτ3, hτx, hτs, hκτ, -⟩ := htri F
  obtain ⟨Φ, h1, h2, h3, h4⟩ := normalForm_four_of_triality hτ3 hτx hτs hκτ
  exact ⟨Φ, _, h1, h2, h3, h4⟩

theorem omegaPlusFourEndInput_of_triality (htri : PlusFourTrialityInput) :
    OmegaPlusFourEndInput :=
  omegaPlusFourEndInput_of_normalForm (omegaPlusFourAutNormalFormInput_of_triality htri)

end NormalForm

end CFSG.SeitzReduction.OmegaPilot
