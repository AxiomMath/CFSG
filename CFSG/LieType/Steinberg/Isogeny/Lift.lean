module

public import CFSG.LieType.Steinberg.PartBProof
public import CFSG.Blueprint.ChevalleyStrings
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

section Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {k : Type*} [Field k]
  {K G : Type*} [Group K] [Group G]

variable {x : (ι → ℤ) → k → K} {O : CommOrder Φ} {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ}

@[expose] def presLift (hx : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval x) r = 1)
    (hbij : Function.Bijective (PresentedGroup.toGroup hx)) {y : (ι → ℤ) → k → G}
    (hy : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval y) r = 1) : K →* G :=
  (PresentedGroup.toGroup hy).comp (MulEquiv.ofBijective _ hbij).symm.toMonoidHom

theorem presLift_apply (hx : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval x) r = 1)
    (hbij : Function.Bijective (PresentedGroup.toGroup hx)) {y : (ι → ℤ) → k → G}
    (hy : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval y) r = 1) {γ : ι → ℤ}
    (hγ : γ ∈ Φ.roots) (c : k) : presLift hx hbij hy (x γ c) = y γ c := by
  have h : (MulEquiv.ofBijective _ hbij).symm (x γ c) = PresentedGroup.of (⟨γ, hγ⟩, c) := by
    rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply, PresentedGroup.toGroup.of]
    rfl
  rw [presLift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, PresentedGroup.toGroup.of]
  rfl

theorem presLift_surjective
    (hx : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval x) r = 1)
    (hbij : Function.Bijective (PresentedGroup.toGroup hx)) {y : (ι → ℤ) → k → G}
    (hy : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval y) r = 1)
    (hgen : Subgroup.closure {g | ∃ γ ∈ Φ.roots, ∃ c, y γ c = g} = ⊤) :
    Function.Surjective (presLift hx hbij hy) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, c, rfl⟩
  exact ⟨x γ c, presLift_apply hx hbij hy hγ c⟩

@[expose] def liftOfPresentationB (hx : PresentationB (Φ := Φ) x) (O : CommOrder Φ)
    (hC : CommutatorFormula x O C) {y : (ι → ℤ) → k → G}
    (hyA : ∀ γ ∈ Φ.roots, ∀ c d : k, y γ (c + d) = y γ c * y γ d)
    (hyB : CommutatorFormula y O C) : K →* G :=
  presLift ((hx O).2 C hC).fst ((hx O).2 C hC).snd (chevEval_rels hyA hyB)

theorem liftOfPresentationB_apply (hx : PresentationB (Φ := Φ) x) (O : CommOrder Φ)
    (hC : CommutatorFormula x O C) {y : (ι → ℤ) → k → G}
    (hyA : ∀ γ ∈ Φ.roots, ∀ c d : k, y γ (c + d) = y γ c * y γ d)
    (hyB : CommutatorFormula y O C) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (c : k) :
    liftOfPresentationB hx O hC hyA hyB (x γ c) = y γ c :=
  presLift_apply _ _ _ hγ c

theorem liftOfPresentationB_surjective (hx : PresentationB (Φ := Φ) x) (O : CommOrder Φ)
    (hC : CommutatorFormula x O C) {y : (ι → ℤ) → k → G}
    (hyA : ∀ γ ∈ Φ.roots, ∀ c d : k, y γ (c + d) = y γ c * y γ d)
    (hyB : CommutatorFormula y O C)
    (hgen : Subgroup.closure {g | ∃ γ ∈ Φ.roots, ∃ c, y γ c = g} = ⊤) :
    Function.Surjective (liftOfPresentationB hx O hC hyA hyB) :=
  presLift_surjective _ _ _ hgen

end Lift

section Transport

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {k : Type*} [Field k] {G H : Type*} [Group G] [Group H]

@[expose] def SameCommutators (x : (Fin τ.rank → ℤ) → k → G) (y : (Fin τ.rank → ℤ) → k → H)
    (α β : Fin τ.rank → ℤ) : Prop :=
  (IsRoot τ (α + β) → ∃ N : k, (∀ c d : k, ⁅x α c, x β d⁆ = x (α + β) (N * c * d)) ∧
      ∀ c d : k, ⁅y α c, y β d⁆ = y (α + β) (N * c * d)) ∧
    (¬IsRoot τ (α + β) → (∀ c d : k, ⁅x α c, x β d⁆ = 1) ∧ ∀ c d : k, ⁅y α c, y β d⁆ = 1)

theorem reflect_add_reflect (i : Fin τ.rank) (u v : Fin τ.rank → ℤ) :
    reflect τ i (u + reflect τ i v) = reflect τ i u + v := by
  rw [← reflectHom_apply, map_add, reflectHom_apply, reflectHom_apply, reflect_reflect]

variable {x : (Fin τ.rank → ℤ) → k → G} {y : (Fin τ.rank → ℤ) → k → H} {n : Fin τ.rank → G}
  {m : Fin τ.rank → H} {s : Fin τ.rank → (Fin τ.rank → ℤ) → k}

theorem sameCommutators_reflect (hs : ∀ i γ, IsRoot τ γ → s i γ * s i γ = 1)
    (hx : ∀ i γ, IsRoot τ γ → ∀ c, n i * x γ c * (n i)⁻¹ = x (reflect τ i γ) (s i γ * c))
    (hy : ∀ i γ, IsRoot τ γ → ∀ c, m i * y γ c * (m i)⁻¹ = y (reflect τ i γ) (s i γ * c))
    (i : Fin τ.rank) {v β : Fin τ.rank → ℤ} (hv : IsRoot τ v) (hβ : IsRoot τ β)
    (h : SameCommutators x y v (reflect τ i β)) : SameCommutators x y (reflect τ i v) β := by
  have hγ : IsRoot τ (reflect τ i β) := hβ.reflect i
  have hsum : reflect τ i (v + reflect τ i β) = reflect τ i v + β := reflect_add_reflect i v β
  have ex : ∀ c, x (reflect τ i v) c = n i * x v (s i v * c) * (n i)⁻¹ := fun c => by
    rw [hx i v hv, ← mul_assoc, hs i v hv, one_mul]
  have ex' : ∀ d, x β d = n i * x (reflect τ i β) (s i (reflect τ i β) * d) * (n i)⁻¹ :=
    fun d => by rw [hx i _ hγ, ← mul_assoc, hs i _ hγ, one_mul, reflect_reflect]
  have ey : ∀ c, y (reflect τ i v) c = m i * y v (s i v * c) * (m i)⁻¹ := fun c => by
    rw [hy i v hv, ← mul_assoc, hs i v hv, one_mul]
  have ey' : ∀ d, y β d = m i * y (reflect τ i β) (s i (reflect τ i β) * d) * (m i)⁻¹ :=
    fun d => by rw [hy i _ hγ, ← mul_assoc, hs i _ hγ, one_mul, reflect_reflect]
  have cx : ∀ c d, ⁅x (reflect τ i v) c, x β d⁆ =
      MulAut.conj (n i) ⁅x v (s i v * c), x (reflect τ i β) (s i (reflect τ i β) * d)⁆ :=
    fun c d => by rw [map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply, ← ex, ← ex']
  have cy : ∀ c d, ⁅y (reflect τ i v) c, y β d⁆ =
      MulAut.conj (m i) ⁅y v (s i v * c), y (reflect τ i β) (s i (reflect τ i β) * d)⁆ :=
    fun c d => by rw [map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply, ← ey, ← ey']
  have hiff : IsRoot τ (reflect τ i v + β) ↔ IsRoot τ (v + reflect τ i β) := by
    rw [← hsum, isRoot_reflect_iff]
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun hr => ?_, fun hnr => ?_⟩
  · have hr' := hiff.1 hr
    obtain ⟨N, hNx, hNy⟩ := h₁ hr'
    refine ⟨s i (v + reflect τ i β) * N * (s i v * s i (reflect τ i β)), fun c d => ?_,
      fun c d => ?_⟩
    · rw [cx, hNx, MulAut.conj_apply, hx i _ hr', hsum]
      congr 1
      ring
    · rw [cy, hNy, MulAut.conj_apply, hy i _ hr', hsum]
      congr 1
      ring
  · obtain ⟨h₃, h₄⟩ := h₂ fun h' => hnr (hiff.2 h')
    exact ⟨fun c d => by rw [cx, h₃, map_one], fun c d => by rw [cy, h₄, map_one]⟩

theorem sameCommutators_of_simple (hs : ∀ i γ, IsRoot τ γ → s i γ * s i γ = 1)
    (hx : ∀ i γ, IsRoot τ γ → ∀ c, n i * x γ c * (n i)⁻¹ = x (reflect τ i γ) (s i γ * c))
    (hy : ∀ i γ, IsRoot τ γ → ∀ c, m i * y γ c * (m i)⁻¹ = y (reflect τ i γ) (s i γ * c))
    (hbase : ∀ (j : Fin τ.rank) (δ : Fin τ.rank → ℤ), IsRoot τ δ → Pi.single j 1 + δ ≠ 0 →
      SameCommutators x y (Pi.single j 1) δ)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α + β ≠ 0) :
    SameCommutators x y α β := by
  induction hα generalizing β with
  | basis j => exact hbase j β hβ hne
  | @reflect i v hv ih =>
    refine sameCommutators_reflect hs hx hy i hv hβ (ih (hβ.reflect i) fun h0 => hne ?_)
    rw [← reflect_add_reflect, h0, ← reflectHom_apply, map_zero]

theorem commutatorFormula_of_sameCommutators {Φ : RootSystem (Fin τ.rank)}
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) {O : CommOrder Φ}
    (h11 : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 → IsRoot τ (α + β) → O.list α β = [(1, 1)])
    (h0 : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 → ¬IsRoot τ (α + β) → O.list α β = [])
    (hinj : ∀ γ, IsRoot τ γ → Function.Injective (x γ))
    (hsame : ∀ α β, IsRoot τ α → IsRoot τ β → α + β ≠ 0 → SameCommutators x y α β)
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ} (hC : CommutatorFormula x O C) :
    CommutatorFormula y O C := by
  intro α hα β hβ hne c d
  have hα' : IsRoot τ α := by rw [hΦ] at hα; exact hα
  have hβ' : IsRoot τ β := by rw [hΦ] at hβ; exact hβ
  obtain ⟨hs₁, hs₂⟩ := hsame α β hα' hβ' hne
  by_cases hr : IsRoot τ (α + β)
  · obtain ⟨N, hNx, hNy⟩ := hs₁ hr
    have hl := h11 α hα β hβ hne hr
    have hC1 := hC α hα β hβ hne 1 1
    rw [hl, hNx, List.map_singleton, List.prod_singleton, one_smul, one_smul] at hC1
    have hN : N = (C α β (1, 1) : k) := by simpa using hinj _ hr hC1
    rw [hl, List.map_singleton, List.prod_singleton, one_smul, one_smul, pow_one, pow_one, hNy,
      hN]
  · rw [h0 α hα β hβ hne hr, List.map_nil, List.prod_nil]
    exact (hs₂ hr).2 c d

end Transport

end CFSG.LieType.Steinberg
