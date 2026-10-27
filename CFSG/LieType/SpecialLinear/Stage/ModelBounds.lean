module

public import CFSG.LieType.SpecialLinear.Stage.InnerDichotomy
public import CFSG.LieType.SpecialLinear.SLModel.AdjointBound
public import CFSG.LieType.SpecialLinear.SLModel.CubeModel
public import CFSG.LieType.SpecialLinear.SLModel.PairModel

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.HardMathSupport.GuralnickMalle
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Theory.Representation
open CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.SpecialLinear.SLModel
open scoped TensorProduct

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {E : Type} [Field E] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E]
  {k : Type} [Field k] [CharP k 2] [Algebra E k] [Algebra F k]
  {D : Type} [Group D] [Finite D]
  {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]
  [IsScalarTower (ZMod 2) E X] [Finite X]

omit [Algebra (ZMod 2) E] [CharP k 2] [Algebra F k] [IsScalarTower (ZMod 2) E X] in
theorem stage_false_of_model_bounds {n : ℕ} (hn : 2 ≤ n)
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ)) (hne : ∃ g, σ g ≠ 1)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1) (hD1 : ∃ d, δ d ≠ 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ (τ : F ≃+* F) (ε : ℕ),
      ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ ε g) (δ d x))
    (hoff : IsOffenderOn δ ⊤ ⊤) {c : ℕ}
    (hc : c = 4 ∨ (c = 2 ∧
      ((∀ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
          ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ 0 g) (δ d x)) ∨
        (∀ d, ∀ A : GL (Fin (n + 1)) F, IsUpperGL A → ∀ τ : F ≃+* F,
          (∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ 0 g) (δ d x)) →
            τ = RingEquiv.refl F))))
    {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (n + 1)) F) V)
    (β : (k ⊗[E] X) ≃ₗ[k] V) (hβ : ∀ g v, β (extendScalars k σ g v) = ρ g (β v))
    (h1 : ∀ u : SpecialLinearGroup (Fin (n + 1)) F, u ≠ 1 → u * u = 1 →
      16 < Nat.card E ^ Module.finrank k (LinearMap.range (ρ u - 1)))
    (h2 : ∀ P : Subgroup (SpecialLinearGroup (Fin (n + 1)) F), P ≠ ⊥ → (∀ a ∈ P, a * a = 1) →
      (∀ a ∈ P, ∀ b ∈ P, (ρ a - 1) * (ρ b - 1) = 0) →
      c * Nat.card P < Nat.card E ^ (Module.finrank k V - Module.finrank k (fixSub ρ P))) :
    False := by
  rcases stage_inner_dichotomy hn σ hsimp hne δ hδE hD2 hD1 hquad hcompat hoff hc with
    ⟨u, -, hu1, hu2, hle⟩ | ⟨A₀, -, hA₀ne, hA₀inv, hA₀quad, hle⟩
  · have hlt := h1 u hu1 hu2
    have hr : Module.finrank k (LinearMap.range (extendScalars k σ u - 1)) =
        Module.finrank k (LinearMap.range (ρ u - 1)) :=
      finrank_range_sub_one_eq_of_equiv (τ := extendScalars k σ) (τ' := ρ) β hβ u
    rw [hr] at hle
    exact (not_lt_of_ge hle) hlt
  · have hquadρ : ∀ a ∈ A₀, ∀ b ∈ A₀, (ρ a - 1) * (ρ b - 1) = 0 :=
      fun a ha b hb =>
        sub_one_mul_sub_one_of_equiv (τ := extendScalars k σ) (τ' := ρ) β hβ
          (hA₀quad a ha b hb)
    have hlt := h2 A₀ hA₀ne hA₀inv hquadρ
    have hdim : Module.finrank k (k ⊗[E] X) = Module.finrank k V := β.finrank_eq
    have hfix1 : fixSub (extendScalars k σ) A₀ = fixSubGen (extendScalars k σ) A₀ := by
      ext v
      rfl
    have hfix2 : fixSub ρ A₀ = fixSubGen ρ A₀ := by
      ext v
      rfl
    have hfix : Module.finrank k (fixSub (extendScalars k σ) A₀) =
        Module.finrank k (fixSub ρ A₀) := by
      rw [hfix1, hfix2]
      exact finrank_fixSubGen_eq_of_equiv (τ := extendScalars k σ) (τ' := ρ) β hβ A₀
    rw [hdim, hfix] at hle
    exact (not_lt_of_ge hle) hlt

omit [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem stage_adjoint_false {n f : ℕ} (hn : 4 ≤ n) (hF : Fintype.card F = 2 ^ f)
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ)) (hne : ∃ g, σ g ≠ 1)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1) (hD1 : ∃ d, δ d ≠ 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ 0 g) (δ d x))
    (hoff : IsOffenderOn δ ⊤ ⊤)
    (ε : Fin f → Finset (Fin (n + 1))) (β : (k ⊗[E] X) ≃ₗ[k] BModel k ε)
    (hβ : ∀ g v, β (extendScalars k σ g v) = slModelRep (F := F) (k := k) ε g (β v))
    {s : ℕ} (hE : Fintype.card E = 2 ^ s) (hfs : f ≤ s)
    (r₀ : Fin f) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (hε : ε r₀ = {⟨1, by omega⟩, ⟨n, by omega⟩}) : False := by
  have hN : 2 ≤ Nat.card E := by
    have := Finite.one_lt_card (α := E)
    omega
  have hN' : 2 ^ f ≤ Nat.card E := by
    rw [Nat.card_eq_fintype_card, hE]
    exact pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hfs
  have hcompat' : ∀ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ (τ : F ≃+* F) (ε : ℕ),
      ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ ε g) (δ d x) := by
    intro d
    obtain ⟨A, hA, τ, hτ⟩ := hcompat d
    exact ⟨A, hA, τ, 0, hτ⟩
  refine stage_false_of_model_bounds (n := n) (c := 2) (by omega) σ hsimp hne δ hδE hD2 hD1
    hquad hcompat' hoff (Or.inr ⟨rfl, Or.inl hcompat⟩) (V := BModel k ε)
    (slModelRep (F := F) (k := k) ε) β hβ ?_ ?_
  · intro u hu1 hu2
    exact sixteen_lt_pow_finrank_range_slModelRep_adjoint (F := F) (k := k) (m := n) (f := f)
      (by omega) ε r₀ hε' hε (N := Nat.card E) hN hu2 hu1
  · intro P hP1 hP hquadP
    exact two_mul_card_lt_pow_codim_slModelRep_adjoint (F := F) (k := k) (m := n) (f := f)
      (by omega) hF ε r₀ hε' hε (N := Nat.card E) hN' hP1 hP hquadP

omit [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem stage_cube_false {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hq : 2 < Fintype.card F)
    (σ : Representation E (SpecialLinearGroup (Fin 6) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ)) (hne : ∃ g, σ g ≠ 1)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1) (hD1 : ∃ d, δ d ≠ 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin 6) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd 6 F A τ 0 g) (δ d x))
    (hoff : IsOffenderOn δ ⊤ ⊤)
    (ε : Fin f → Finset (Fin 6)) (β : (k ⊗[E] X) ≃ₗ[k] BModel k ε)
    (hβ : ∀ g v, β (extendScalars k σ g v) = slModelRep (F := F) (k := k) ε g (β v))
    {s : ℕ} (hE : Fintype.card E = 2 ^ s) (hfs : f ≤ s)
    (r₀ : Fin f) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (hε : ε r₀ = {3}) : False := by
  have hN : 2 ≤ Nat.card E := by
    have := Finite.one_lt_card (α := E)
    omega
  have hN' : 2 ^ f ≤ Nat.card E := by
    rw [Nat.card_eq_fintype_card, hE]
    exact pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hfs
  have hcompat' : ∀ d, ∃ A : GL (Fin 6) F, IsUpperGL A ∧ ∃ (τ : F ≃+* F) (ε : ℕ),
      ∀ g x, δ d (σ g x) = σ (borelStd 6 F A τ ε g) (δ d x) := by
    intro d
    obtain ⟨A, hA, τ, hτ⟩ := hcompat d
    exact ⟨A, hA, τ, 0, hτ⟩
  refine stage_false_of_model_bounds (n := 5) (c := 2) (by omega) σ hsimp hne δ hδE hD2 hD1
    hquad hcompat' hoff (Or.inr ⟨rfl, Or.inl hcompat⟩) (V := BModel k ε)
    (slModelRep (F := F) (k := k) ε) β hβ ?_ ?_
  · intro u hu1 hu2
    exact sixteen_lt_pow_finrank_range_slModelRep_cube (F := F) (k := k) (f := f)
      ε r₀ hε' hε (N := Nat.card E) hN hu2 hu1
  · intro P hP1 hP _
    exact two_mul_card_lt_pow_codim_slModelRep_cube (F := F) (k := k) (f := f)
      hF hq ε r₀ hε' hε (N := Nat.card E) hN' hP1 hP

omit [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem stage_pair_false {n f e : ℕ} (hn : 4 ≤ n) (hF : Fintype.card F = 2 ^ f)
    (hfe : f = 2 * e)
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ)) (hne : ∃ g, σ g ≠ 1)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1) (hD1 : ∃ d, δ d ≠ 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ 0 g) (δ d x))
    (hoff : IsOffenderOn δ ⊤ ⊤)
    (ε : Fin f → Finset (Fin (n + 1))) (β : (k ⊗[E] X) ≃ₗ[k] BModel k ε)
    (hβ : ∀ g v, β (extendScalars k σ g v) = slModelRep (F := F) (k := k) ε g (β v))
    {s : ℕ} (hE : Fintype.card E = 2 ^ s) (hes : e ≤ s)
    {r₁ r₂ : Fin f} (hr₂ : (r₂ : ℕ) = (r₁ + e) % f) {j : Fin (n + 1)}
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) = n) (h₁ : ε r₁ = {j}) (h₂ : ε r₂ = {j})
    (hrest : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅) : False := by
  have hfpos : 0 < f := by
    have := r₁.isLt
    omega
  have hepos : 0 < e := by omega
  have hef : e < f := by omega
  have hr : r₁ ≠ r₂ := by
    intro h
    have hv : (r₁ : ℕ) = (r₂ : ℕ) := congrArg Fin.val h
    rw [hr₂] at hv
    have hr₁ : (r₁ : ℕ) < f := r₁.isLt
    by_cases hlt : (r₁ : ℕ) + e < f
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have hle : f ≤ (r₁ : ℕ) + e := Nat.le_of_not_lt hlt
      have hlt' : (r₁ : ℕ) + e - f < f := by omega
      have hmod : ((r₁ : ℕ) + e) % f = (r₁ : ℕ) + e - f := by
        rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt']
      rw [hmod] at hv
      omega
  have hN : 2 ≤ Nat.card E := by
    have := Finite.one_lt_card (α := E)
    omega
  have hN' : 2 ^ e ≤ Nat.card E := by
    rw [Nat.card_eq_fintype_card, hE]
    exact pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hes
  have hcompat' : ∀ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ (τ : F ≃+* F) (ε : ℕ),
      ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ ε g) (δ d x) := by
    intro d
    obtain ⟨A, hA, τ, hτ⟩ := hcompat d
    exact ⟨A, hA, τ, 0, hτ⟩
  refine stage_false_of_model_bounds (n := n) (c := 2) (by omega) σ hsimp hne δ hδE hD2 hD1
    hquad hcompat' hoff (Or.inr ⟨rfl, Or.inl hcompat⟩) (V := BModel k ε)
    (slModelRep (F := F) (k := k) ε) β hβ ?_ ?_
  · intro u hu1 hu2
    exact sixteen_lt_pow_finrank_range_slModelRep_pair (F := F) (k := k) (m := n) (f := f)
      (by omega) ε hr hj h₁ h₂ hrest (N := Nat.card E) hN hu2 hu1
  · intro P hP1 hP hquadP
    exact two_mul_card_lt_pow_codim_slModelRep_pair (F := F) (k := k) (m := n) (f := f)
      (by omega) hF hfe ε hr₂ hj h₁ h₂ hrest (N := Nat.card E) hN' hP1 hP hquadP

end CFSG.LieType.SpecialLinear
