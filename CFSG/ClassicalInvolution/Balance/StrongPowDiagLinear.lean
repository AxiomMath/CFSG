module

public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open CFSG.ClassicalInvolution.RouteD.Gaps (LinearAutClassification slConjugation_diagGL_congr
  slConjugation_diagGL_apply diagGL coe_diagGL)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {n : ℕ} {k : Type} [Field k]

section Chart

variable {X : Type} [Group X]

theorem chart_of_lift_gl {P : SL(n, k)} {x : GL (Fin n) k} {σ : Fin n → Bool}
    (hx : (x : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) *
        Matrix.diagonal fun j => CFSG.ClassicalInvolution.Models.signOf k (σ j))
    (y : SL(n, k)) :
    slConjugation n k x (P * y * P⁻¹) = P * slConjugation n k (signGL k σ) y * P⁻¹ := by
  have hGL : x = Matrix.SpecialLinearGroup.toGL P * signGL k σ *
      (Matrix.SpecialLinearGroup.toGL P)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, signGL, coe_diagGL]
    simp only [signOf_eq_signUnit] at hx
    exact hx
  have hinv : (Matrix.SpecialLinearGroup.toGL P)⁻¹ = Matrix.SpecialLinearGroup.toGL P⁻¹ :=
    (map_inv _ _).symm
  have h1 : slConjugation n k x = slConjugation n k (Matrix.SpecialLinearGroup.toGL P) *
      slConjugation n k (signGL k σ) * slConjugation n k (Matrix.SpecialLinearGroup.toGL P⁻¹) := by
    rw [hGL, hinv, map_mul, map_mul]
  rw [h1]
  simp only [MulAut.mul_apply, slConjugation_toGL]
  have e : P⁻¹ * (P * y * P⁻¹) * P⁻¹⁻¹ = y := by group
  rw [e]

theorem exists_chart_gl (hn : 0 < n) (h2 : (2 : k) ≠ 0) (ψ : SL(n, k) →* X) {f g : X}
    {x₁ x₂ : GL (Fin n) k} (hx₁ : ∀ y, f * ψ y * f⁻¹ = ψ (slConjugation n k x₁ y))
    (hx₂ : ∀ y, g * ψ y * g⁻¹ = ψ (slConjugation n k x₂ y)) (hsq₁ : x₁ * x₁ = 1)
    (hsq₂ : x₂ * x₂ = 1) (hc : x₁ * x₂ = x₂ * x₁) :
    ∃ (P : SL(n, k)) (σ₁ σ₂ : Fin n → Bool),
      (∀ y, f * ψ (P * y * P⁻¹) * f⁻¹ = ψ (P * slConjugation n k (signGL k σ₁) y * P⁻¹)) ∧
      (∀ y, g * ψ (P * y * P⁻¹) * g⁻¹ = ψ (P * slConjugation n k (signGL k σ₂) y * P⁻¹)) := by
  have hii : ∀ x : GL (Fin n) k, x * x = 1 →
      (x : Matrix (Fin n) (Fin n) k) * (x : Matrix (Fin n) (Fin n) k) = 1 := by
    intro x hx
    have := congrArg (fun z : GL (Fin n) k => (z : Matrix (Fin n) (Fin n) k)) hx
    simpa only [Units.val_mul, Units.val_one] using this
  have hcomm : (x₁ : Matrix (Fin n) (Fin n) k) * (x₂ : Matrix (Fin n) (Fin n) k) =
      (x₂ : Matrix (Fin n) (Fin n) k) * (x₁ : Matrix (Fin n) (Fin n) k) := by
    have := congrArg (fun z : GL (Fin n) k => (z : Matrix (Fin n) (Fin n) k)) hc
    simpa only [Units.val_mul] using this
  obtain ⟨P, ε, hP₁, hP₂⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_sl_frame_signs h2 hn
    (hii x₁ hsq₁) (hii x₂ hsq₂) hcomm
  refine ⟨P, fun j => (ε j).1, fun j => (ε j).2, fun y => ?_, fun y => ?_⟩
  · rw [hx₁ (P * y * P⁻¹), chart_of_lift_gl hP₁ y]
  · rw [hx₂ (P * y * P⁻¹), chart_of_lift_gl hP₂ y]

theorem exists_chart_of_lifts_gl (hn : 0 < n) (h2 : (2 : k) ≠ 0) (ψ : SL(n, k) →* X)
    {F₀ : Subgroup X} (htoral : ToralDiagGL 2 ψ F₀) {f g : X} (hf : f ∈ F₀) (hg : g ∈ F₀) :
    ∃ (P₀ : SL(n, k)) (σ₁ σ₂ : Fin n → Bool),
      (∀ y, f * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation n k (signGL k σ₁) y)) ∧
      (∀ y, g * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * g⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation n k (signGL k σ₂) y)) := by
  obtain ⟨P, hP, hact⟩ := htoral
  obtain ⟨x₁, hx₁P, hx₁k, hx₁⟩ := hact f hf
  obtain ⟨x₂, hx₂P, hx₂k, hx₂⟩ := hact g hg
  exact exists_chart_gl hn h2 ψ hx₁ hx₂ (by rwa [← pow_two]) (by rwa [← pow_two])
    (hP x₁ hx₁P x₂ hx₂P)

end Chart

section Delta

variable {X : Type} [Group X] [Finite X] [Finite k]

theorem deltaCore_trivial_gl (hn : 3 ≤ n) (h2 : (2 : k) ≠ 0) (h4 : 4 ≤ Nat.card k)
    (hcl : LinearAutClassification k n) (ψ : SL(n, k) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (htoral : ToralDiagGL 2 ψ F) {d : X}
    (hd : d ∈ CFSG.ClassicalInvolution.Balance.deltaCore F) {x : X} (hx : x ∈ ψ.range) :
    d * x = x * d := by
  have hn0 : 0 < n := by omega
  obtain ⟨a, haF, b, hbF, ha1, hb1, hab1⟩ := exists_pair_of_card_four hcard hF2
  have hdmem : ∀ f ∈ F, f ≠ 1 → d ∈ involutionOddCore f := fun f hf hf1 =>
    CFSG.ClassicalInvolution.Balance.mem_deltaCore_iff.mp hd f hf hf1
  obtain ⟨P₀, σ₁, σ₂, hch₁, hch₂⟩ := exists_chart_of_lifts_gl hn0 h2 ψ htoral haF hbF
  have hrange : (ψ.comp (MulAut.conj P₀).toMonoidHom).range = ψ.range :=
    CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hΨnorm : (ψ.comp (MulAut.conj P₀).toMonoidHom).range.Normal := by
    rw [hrange]
    exact hnorm
  have hΨker := ker_comp_conj_le_center ψ hker P₀
  have hperf : Group.IsPerfect SL(n, k) := isPerfect_specialLinear (by omega) h4
  have hch₃ : ∀ y, (a * b) * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (a * b)⁻¹ =
      (ψ.comp (MulAut.conj P₀).toMonoidHom)
        (slConjugation n k (signGL k (fun j => decide (σ₁ j = σ₂ j))) y) := by
    intro y
    have e : (a * b) * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (a * b)⁻¹ =
        a * (b * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * b⁻¹) * a⁻¹ := by group
    rw [e, hch₂ y, hch₁, signGL_agree, map_mul]
    rfl
  obtain ⟨u₁, hc₁, hu₁⟩ := act_diagonal_of_mem_involutionOddCore hn h2 h4 hcl _ hΨker hΨnorm a σ₁
    hch₁ (hdmem a haF ha1)
  obtain ⟨u₂, hc₂, hu₂⟩ := act_diagonal_of_mem_involutionOddCore hn h2 h4 hcl _ hΨker hΨnorm b σ₂
    hch₂ (hdmem b hbF hb1)
  obtain ⟨u₃, hc₃, hu₃⟩ := act_diagonal_of_mem_involutionOddCore hn h2 h4 hcl _ hΨker hΨnorm
    (a * b) _ hch₃ (hdmem _ (F.mul_mem haF hbF) hab1)
  have hagree : ∀ (v w : Fin n → kˣ),
      (∀ y, d * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * d⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation n k (diagGL v) y)) →
      (∀ y, d * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * d⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation n k (diagGL w) y)) →
      ∀ y, slConjugation n k (diagGL v) y = slConjugation n k (diagGL w) y := by
    intro v w hv hw
    have := CFSG.ClassicalInvolution.RouteD.Gaps.hom_eq_of_central_ker _ hΨker
      (L := SL(n, k)) (slConjugation n k (diagGL v)).toMonoidHom
      (slConjugation n k (diagGL w)).toMonoidHom (fun y => by
        simp only [MulEquiv.coe_toMonoidHom]
        rw [← hv y, ← hw y])
    intro y
    exact congrArg (fun h => h y) this
  have hconst := const_of_three σ₁ σ₂ u₁ u₂ u₃ hc₁ hc₂ hc₃ (hagree u₁ u₂ hu₁ hu₂)
    (hagree u₁ u₃ hu₁ hu₃)
  have hid : ∀ y, slConjugation n k (diagGL u₁) y = y := by
    intro y
    rw [slConjugation_diagGL_congr u₁ 1 (u₁ ⟨0, hn0⟩) (fun i => by simp [hconst i ⟨0, hn0⟩]) y,
      slConjugation_diagGL_one]
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  have := hu₁ y
  rw [hid y] at this
  exact mul_inv_eq_iff_eq_mul.mp this

end Delta

section Two

variable {X : Type} [Group X] [Finite X]

theorem slConjugation_signGL_of_const {σ : Fin n → Bool} (hσ : ∀ i j, σ i = σ j) (hn : 0 < n)
    (y : SL(n, k)) : slConjugation n k (signGL k σ) y = y := by
  rw [signGL, slConjugation_diagGL_congr (fun i => signUnit k (σ i)) 1
    (signUnit k (σ ⟨0, hn⟩)) (fun i => by simp [hσ i ⟨0, hn⟩]) y, slConjugation_diagGL_one]

theorem forall_fin_two_eq_iff (σ : Fin 2 → Bool) : (∀ i j, σ i = σ j) ↔ σ 0 = σ 1 := by
  refine ⟨fun h => h 0 1, fun h i j => ?_⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact h
  · exact h.symm
  · rfl

theorem false_of_toralDiagGL_two (h2 : (2 : k) ≠ 0) (ψ : SL(2, k) →* X) {F : Subgroup X}
    (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (htoral : ToralDiagGL 2 ψ F) : False := by
  obtain ⟨a, haF, b, hbF, ha1, hb1, hab1⟩ := exists_pair_of_card_four hcard hF2
  obtain ⟨P₀, σ₁, σ₂, hch₁, hch₂⟩ := exists_chart_of_lifts_gl (n := 2) (by norm_num) h2 ψ htoral
    haF hbF
  have hrange : (ψ.comp (MulAut.conj P₀).toMonoidHom).range = ψ.range :=
    CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hcent : ∀ (f : X) (σ : Fin 2 → Bool),
      (∀ y, f * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation 2 k (signGL k σ) y)) →
      (σ 0 = σ 1) → ∀ x ∈ ψ.range, f * x = x * f := by
    intro f σ hf hσ x hx
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    have := hf y
    rw [slConjugation_signGL_of_const ((forall_fin_two_eq_iff σ).mpr hσ) (by norm_num) y] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have hσ₁ : σ₁ 0 ≠ σ₁ 1 := fun h => hfaith a haF ha1 (hcent a σ₁ hch₁ h)
  have hσ₂ : σ₂ 0 ≠ σ₂ 1 := fun h => hfaith b hbF hb1 (hcent b σ₂ hch₂ h)
  have hch₃ : ∀ y, (a * b) * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (a * b)⁻¹ =
      (ψ.comp (MulAut.conj P₀).toMonoidHom)
        (slConjugation 2 k (signGL k (fun j => decide (σ₁ j = σ₂ j))) y) := by
    intro y
    have e : (a * b) * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (a * b)⁻¹ =
        a * (b * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * b⁻¹) * a⁻¹ := by group
    rw [e, hch₂ y, hch₁, signGL_agree, map_mul]
    rfl
  exact hfaith (a * b) (F.mul_mem haF hbF) hab1
    (hcent (a * b) _ hch₃ (decide_eq_of_ne hσ₁ hσ₂))

end Two

section Model

variable {p e : ℕ} [Fact p.Prime]

theorem deltaCore_trivial_gf {n : ℕ} (hn : 2 ≤ n) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) {X : Type}
    [Group X] [Finite X] (ψ : SL(n, GaloisField p e) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField p e)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (htoral : ToralDiagGL 2 ψ F) {d : X}
    (hd : d ∈ CFSG.ClassicalInvolution.Balance.deltaCore F) {x : X} (hx : x ∈ ψ.range) :
    d * x = x * d := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  have h2 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  by_cases h3 : 3 ≤ n
  · exact deltaCore_trivial_gl h3 h2 h4
      (CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2 h5 h3) ψ hker
      hnorm hcard hF2 htoral hd hx
  · obtain rfl : n = 2 := by omega
    exact (false_of_toralDiagGL_two h2 ψ hcard hF2 hfaith htoral).elim

end Model

end CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
