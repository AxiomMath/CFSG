module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalance
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearDiag
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalLinear

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open CFSG.ClassicalInvolution.RouteD.Gaps (LinearAutClassification slConjugation_diagGL_congr
  slConjugation_diagGL_apply diagGL coe_diagGL)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {n : ℕ} {k : Type} [Field k]

section Diagonal

theorem diagGL_mul (u v : Fin n → kˣ) : diagGL (u * v) = diagGL u * diagGL v := by
  refine Units.ext ?_
  simp [coe_diagGL, Matrix.diagonal_mul_diagonal]

theorem diagGL_one : diagGL (1 : Fin n → kˣ) = (1 : GL (Fin n) k) := by
  refine Units.ext ?_
  simp [coe_diagGL]

theorem slConjugation_diagGL_mul (u v : Fin n → kˣ) (y : SL(n, k)) :
    slConjugation n k (diagGL u) (slConjugation n k (diagGL v) y) =
      slConjugation n k (diagGL (u * v)) y := by
  rw [diagGL_mul, map_mul]
  rfl

theorem slConjugation_diagGL_comm (u v : Fin n → kˣ) (y : SL(n, k)) :
    slConjugation n k (diagGL u) (slConjugation n k (diagGL v) y) =
      slConjugation n k (diagGL v) (slConjugation n k (diagGL u) y) := by
  rw [slConjugation_diagGL_mul, slConjugation_diagGL_mul, mul_comm]

theorem slConjugation_diagGL_one (y : SL(n, k)) :
    slConjugation n k (diagGL (1 : Fin n → kˣ)) y = y := by
  rw [diagGL_one, map_one]
  rfl

end Diagonal

section Single

variable [Finite k] {X : Type} [Group X] [Finite X]

theorem act_diagonal_of_mem_involutionOddCore (hn : 3 ≤ n) (h2 : (2 : k) ≠ 0)
    (h4 : 4 ≤ Nat.card k) (hcl : LinearAutClassification k n)
    (Ψ : SL(n, k) →* X) (hker : Ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : Ψ.range.Normal)
    (f : X) (σ : Fin n → Bool)
    (hf : ∀ y, f * Ψ y * f⁻¹ = Ψ (slConjugation n k (signGL k σ) y))
    {d : X} (hd : d ∈ involutionOddCore f) :
    ∃ u : Fin n → kˣ, (∀ i j, σ i = σ j → u i = u j) ∧
      ∀ y, d * Ψ y * d⁻¹ = Ψ (slConjugation n k (diagGL u) y) := by
  have hsub : CFSG.Open.IsSubnormal Ψ.range ⊤ :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  have hdc : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSL k (coordSet σ b),
      d * Ψ s = Ψ s * d := by
    intro b hb s hs
    have hQ := isComponentOf_block_centralizer h2 h4 Ψ hker f σ hf b hb
    have hle := CFSG.ClassicalInvolution.Balance.le_centralizerLayer_of_isComponentOf hsub hQ
    exact CFSG.ClassicalInvolution.Balance.commute_of_mem_involutionOddCore_of_mem_centralizerLayer
      hd (hle ⟨s, hs, rfl⟩)
  have hdc₂ : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSL k (coordSet σ b),
      (d * d) * Ψ s = Ψ s * (d * d) := by
    intro b hb s hs
    rw [mul_assoc, hdc b hb s hs, ← mul_assoc, hdc b hb s hs, mul_assoc]
  have := hnorm
  have hkerR : Ψ.rangeRestrict.ker ≤ Subgroup.center SL(n, k) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨α, g, φ, ε, hαΨ, hαf⟩ := hcl ↥Ψ.range Ψ.rangeRestrict Ψ.rangeRestrict_surjective hkerR
    (MulAut.conjNormal d)
  have hαd : ∀ x, Ψ (α x) = d * Ψ x * d⁻¹ := by
    intro x
    have h := congrArg Subtype.val (hαΨ x)
    simpa [MulAut.conjNormal_apply] using h
  obtain ⟨g₂, hg₂⟩ := exists_sq_form α g φ ε hαf
  have hα₂d : ∀ x, Ψ (α (α x)) = (d * d) * Ψ x * (d * d)⁻¹ := by
    intro x
    rw [hαd, hαd]
    group
  have hfix : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSL k (coordSet σ b),
      (α.comp α) s = s := by
    intro b hb s hs
    have hperf : Group.IsPerfect ↥(coordBlockSL k (coordSet σ b)) :=
      ⟨(isQuasisimple_coordBlockSL hb h4).1⟩
    have hhom := CFSG.ClassicalInvolution.RouteD.Gaps.hom_eq_of_central_ker Ψ hker
      (L := ↥(coordBlockSL k (coordSet σ b)))
      ((α.comp α).comp (coordBlockSL k (coordSet σ b)).subtype)
      (coordBlockSL k (coordSet σ b)).subtype (fun l => by
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [hα₂d, hdc₂ b hb l l.2, mul_inv_cancel_right])
    exact congrArg (fun h => (h ⟨s, hs⟩ : SL(n, k))) hhom
  obtain ⟨hφ, u₂, hg₂u, hconst⟩ := diag_of_fixes_blocks hn σ (α.comp α) g₂ (φ.trans φ)
    (fun x => hg₂ x) hfix
  have hd₂act : ∀ y, (d * d) * Ψ y * (d * d)⁻¹ = Ψ (slConjugation n k (diagGL u₂) y) := by
    intro y
    rw [← hα₂d]
    congr 1
    refine Subtype.ext ?_
    rw [slConjugation_matrix]
    have hmap : (φ.trans φ).mapMatrix (y : Matrix (Fin n) (Fin n) k) = y := by
      ext i j
      exact hφ _
    have := hg₂ y
    rw [hmap, hg₂u] at this
    exact this
  obtain ⟨r, hr⟩ := odd_orderOf_of_mem_involutionOddCore hd
  have hdpow : d = (d * d) ^ (r + 1) := by
    have h1 : (d * d) ^ (r + 1) = d ^ (2 * (r + 1)) := by rw [pow_mul, sq]
    rw [h1, show 2 * (r + 1) = orderOf d + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have hpowact : ∀ j : ℕ, ∀ y, (d * d) ^ j * Ψ y * ((d * d) ^ j)⁻¹ =
      Ψ (slConjugation n k (diagGL (u₂ ^ j)) y) := by
    intro j
    induction j with
    | zero =>
      intro y
      rw [pow_zero, pow_zero, slConjugation_diagGL_one]
      group
    | succ j ih =>
      intro y
      have e1 : ∀ (e z : X), e ^ (j + 1) * z * (e ^ (j + 1))⁻¹ =
          e ^ j * (e * z * e⁻¹) * (e ^ j)⁻¹ := by
        intro e z
        rw [pow_succ, _root_.mul_inv_rev]
        simp only [mul_assoc]
      rw [e1 (d * d) (Ψ y), hd₂act, ih, slConjugation_diagGL_mul, pow_succ', mul_comm]
  refine ⟨u₂ ^ (r + 1), fun i j hij => ?_, fun y => ?_⟩
  · simp only [Pi.pow_apply, hconst i j hij]
  · conv_lhs => rw [hdpow]
    exact hpowact (r + 1) y

end Single

section Chart

variable {X : Type} [Group X]

theorem signOf_eq_signUnit (b : Bool) :
    (CFSG.ClassicalInvolution.Models.signOf k b : k) = ((signUnit k b : kˣ) : k) := by
  cases b <;> simp [CFSG.ClassicalInvolution.Models.signOf, signUnit]

theorem slConjugation_toGL (x z : SL(n, k)) :
    slConjugation n k (Matrix.SpecialLinearGroup.toGL x) z = x * z * x⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

theorem chart_of_lift {P x : SL(n, k)} {σ : Fin n → Bool} {s : k} (hs : s ≠ 0)
    (hx : (x : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) *
        Matrix.diagonal fun j => s * CFSG.ClassicalInvolution.Models.signOf k (σ j))
    (y : SL(n, k)) :
    x * (P * y * P⁻¹) * x⁻¹ = P * slConjugation n k (signGL k σ) y * P⁻¹ := by
  have hGL : Matrix.SpecialLinearGroup.toGL x = Matrix.SpecialLinearGroup.toGL P *
      diagGL (fun j => Units.mk0 s hs * signUnit k (σ j)) *
        (Matrix.SpecialLinearGroup.toGL P)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_diagGL]
    simp only [signOf_eq_signUnit] at hx
    exact hx
  have hc : slConjugation n k (diagGL fun j => Units.mk0 s hs * signUnit k (σ j)) =
      slConjugation n k (signGL k σ) := by
    exact MulEquiv.ext fun z => slConjugation_diagGL_congr _
      (fun j => signUnit k (σ j)) (Units.mk0 s hs) (fun j => rfl) z
  have hinv : (Matrix.SpecialLinearGroup.toGL P)⁻¹ = Matrix.SpecialLinearGroup.toGL P⁻¹ :=
    (map_inv _ _).symm
  have hdecomp : slConjugation n k (Matrix.SpecialLinearGroup.toGL P *
      diagGL (fun j => Units.mk0 s hs * signUnit k (σ j)) *
        Matrix.SpecialLinearGroup.toGL P⁻¹) =
      slConjugation n k (Matrix.SpecialLinearGroup.toGL P) *
        slConjugation n k (diagGL fun j => Units.mk0 s hs * signUnit k (σ j)) *
          slConjugation n k (Matrix.SpecialLinearGroup.toGL P⁻¹) := by
    rw [map_mul, map_mul]
  rw [← slConjugation_toGL x, hGL, hinv, hdecomp, hc]
  simp only [MulAut.mul_apply, slConjugation_toGL]
  have e : P⁻¹ * (P * y * P⁻¹) * P⁻¹⁻¹ = y := by group
  rw [e]

end Chart

section Pair

variable {X : Type} [Group X]

theorem exists_chart_pair (hn : 0 < n) (h2 : (2 : k) ≠ 0) (ψ : SL(n, k) →* X) {f g : X}
    {x₁ x₂ : SL(n, k)} {s₁ s₂ : k} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (hx₁ : ∀ y, f * ψ y * f⁻¹ = ψ (x₁ * y * x₁⁻¹))
    (hx₂ : ∀ y, g * ψ y * g⁻¹ = ψ (x₂ * y * x₂⁻¹))
    (hsq₁ : (x₁ : Matrix (Fin n) (Fin n) k) * x₁ = (s₁ ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    (hsq₂ : (x₂ : Matrix (Fin n) (Fin n) k) * x₂ = (s₂ ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    (hc : x₁ * x₂ = x₂ * x₁) :
    ∃ (P : SL(n, k)) (σ₁ σ₂ : Fin n → Bool),
      (∀ y, f * ψ (P * y * P⁻¹) * f⁻¹ = ψ (P * slConjugation n k (signGL k σ₁) y * P⁻¹)) ∧
      (∀ y, g * ψ (P * y * P⁻¹) * g⁻¹ = ψ (P * slConjugation n k (signGL k σ₂) y * P⁻¹)) := by
  have hii : ∀ (x : SL(n, k)) (s : k), s ≠ 0 →
      (x : Matrix (Fin n) (Fin n) k) * x = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k) →
      (s⁻¹ • (x : Matrix (Fin n) (Fin n) k)) * (s⁻¹ • (x : Matrix (Fin n) (Fin n) k)) = 1 := by
    intro x s hs hsq
    rw [Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul]
    have : s⁻¹ * s⁻¹ * s ^ 2 = 1 := by field_simp
    rw [this, one_smul]
  have hcomm : (s₁⁻¹ • (x₁ : Matrix (Fin n) (Fin n) k)) * (s₂⁻¹ • (x₂ : Matrix (Fin n) (Fin n) k)) =
      (s₂⁻¹ • (x₂ : Matrix (Fin n) (Fin n) k)) * (s₁⁻¹ • (x₁ : Matrix (Fin n) (Fin n) k)) := by
    have hc' : (x₁ : Matrix (Fin n) (Fin n) k) * x₂ = x₂ * x₁ := by
      have := congrArg (fun z : SL(n, k) => (z : Matrix (Fin n) (Fin n) k)) hc
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hc', smul_smul,
      smul_smul, mul_comm]
  obtain ⟨P, ε, hP₁, hP₂⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_sl_frame_signs h2 hn
    (hii x₁ s₁ hs₁ hsq₁) (hii x₂ s₂ hs₂ hsq₂) hcomm
  have hlift : ∀ (x : SL(n, k)) (s : k) (hs : s ≠ 0) (b : Fin n → Bool),
      (s⁻¹ • (x : Matrix (Fin n) (Fin n) k)) * (P : Matrix (Fin n) (Fin n) k) =
        (P : Matrix (Fin n) (Fin n) k) *
          Matrix.diagonal (fun j => CFSG.ClassicalInvolution.Models.signOf k (b j)) →
      (x : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) =
        (P : Matrix (Fin n) (Fin n) k) *
          Matrix.diagonal fun j => s * CFSG.ClassicalInvolution.Models.signOf k (b j) := by
    intro x s hs b h
    have e : (x : Matrix (Fin n) (Fin n) k) * P =
        s • ((s⁻¹ • (x : Matrix (Fin n) (Fin n) k)) * P) := by
      rw [Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hs, one_smul]
    rw [e, h, ← Matrix.mul_smul]
    congr 1
    ext a b'
    by_cases hab : a = b' <;> simp [hab]
  refine ⟨P, fun j => (ε j).1, fun j => (ε j).2, fun y => ?_, fun y => ?_⟩
  · rw [hx₁ (P * y * P⁻¹), chart_of_lift hs₁ (hlift x₁ s₁ hs₁ _ hP₁) y]
  · rw [hx₂ (P * y * P⁻¹), chart_of_lift hs₂ (hlift x₂ s₂ hs₂ _ hP₂) y]

end Pair

section Main

variable {X : Type} [Group X]

theorem signGL_agree (σ τ : Fin n → Bool) :
    signGL k (fun j => decide (σ j = τ j)) = signGL k σ * signGL k τ := by
  unfold signGL
  rw [← diagGL_mul]
  congr 1
  funext j
  show signUnit k (decide (σ j = τ j)) = signUnit k (σ j) * signUnit k (τ j)
  generalize σ j = a
  generalize τ j = b
  cases a <;> cases b <;> simp [signUnit]

theorem decide_eq_of_ne {a b c d : Bool} (h1 : a ≠ b) (h2 : c ≠ d) :
    decide (a = c) = decide (b = d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

omit [Field k] in
theorem ker_comp_conj_le_center {K : Type} [Group K] (ψ : K →* X)
    (hker : ψ.ker ≤ Subgroup.center K) (P₀ : K) :
    (ψ.comp (MulAut.conj P₀).toMonoidHom).ker ≤ Subgroup.center K := by
  intro y hy
  have h1 : P₀ * y * P₀⁻¹ ∈ Subgroup.center K := hker hy
  have h3 := Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center K).Normal) _ h1 P₀⁻¹
  have e1 : P₀⁻¹ * (P₀ * y * P₀⁻¹) * P₀⁻¹⁻¹ = y := by group
  rwa [e1] at h3

theorem ratio_eq_of_slConjugation_eq (u v : Fin n → kˣ)
    (h : ∀ y, slConjugation n k (diagGL u) y = slConjugation n k (diagGL v) y) {i j : Fin n}
    (hij : i ≠ j) : u i * (u j)⁻¹ = v i * (v j)⁻¹ := by
  have h1 := congrArg (fun z : SL(n, k) => (z : Matrix (Fin n) (Fin n) k) i j)
    (h (Matrix.SpecialLinearGroup.transvection hij 1))
  simp only [slConjugation_diagGL_apply, CFSG.ClassicalInvolution.RouteD.Gaps.coe_transvection_eq,
    Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.single_apply_same, zero_add, mul_one] at h1
  exact Units.ext (by simpa [Units.val_inv_eq_inv_val] using h1)

theorem exists_chart_of_lifts (hn0 : 0 < n) (h2 : (2 : k) ≠ 0) (ψ : SL(n, k) →* X)
    {F : Subgroup X} (P : Subgroup SL(n, k)) (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hact : ∀ f ∈ F, ∃ x ∈ P, (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) ∧
      ∃ s : k, s ≠ 0 ∧
        (x : Matrix (Fin n) (Fin n) k) * x = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    {f g : X} (hf : f ∈ F) (hg : g ∈ F) :
    ∃ (P₀ : SL(n, k)) (σ₁ σ₂ : Fin n → Bool),
      (∀ y, f * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * f⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation n k (signGL k σ₁) y)) ∧
      (∀ y, g * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * g⁻¹ =
        (ψ.comp (MulAut.conj P₀).toMonoidHom) (slConjugation n k (signGL k σ₂) y)) := by
  obtain ⟨x₁, hx₁P, hx₁, s₁, hs₁, hsq₁⟩ := hact f hf
  obtain ⟨x₂, hx₂P, hx₂, s₂, hs₂, hsq₂⟩ := hact g hg
  exact exists_chart_pair hn0 h2 ψ hs₁ hs₂ hx₁ hx₂ hsq₁ hsq₂ (hP x₁ hx₁P x₂ hx₂P)

variable [Finite k] [Finite X]

theorem commutator_trivial_split (hn : 3 ≤ n) (h2 : (2 : k) ≠ 0) (h4 : 4 ≤ Nat.card k)
    (hcl : LinearAutClassification k n) (ψ : SL(n, k) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (P : Subgroup SL(n, k)) (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hact : ∀ f ∈ F, ∃ x ∈ P, (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) ∧
      ∃ s : k, s ≠ 0 ∧
        (x : Matrix (Fin n) (Fin n) k) * x = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    {f : X} (hf : f ∈ F) {d : X} (hd : d ∈ involutionOddCore f) {g : X} (hg : g ∈ F)
    {x : X} (hx : x ∈ ψ.range) :
    d * g * x * (d * g)⁻¹ = g * d * x * (g * d)⁻¹ := by
  obtain ⟨P₀, σ₁, σ₂, hch₁, hch₂⟩ := exists_chart_of_lifts (by omega) h2 ψ P hP hact hf hg
  have hrange : (ψ.comp (MulAut.conj P₀).toMonoidHom).range = ψ.range :=
    CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hΨnorm : (ψ.comp (MulAut.conj P₀).toMonoidHom).range.Normal := by
    rw [hrange]
    exact hnorm
  obtain ⟨u, -, hu⟩ := act_diagonal_of_mem_involutionOddCore hn h2 h4 hcl _
    (ker_comp_conj_le_center ψ hker P₀) hΨnorm f σ₁ hch₁ hd
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  have e1 : d * g * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (d * g)⁻¹ =
      d * (g * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * g⁻¹) * d⁻¹ := by group
  have e2 : g * d * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (g * d)⁻¹ =
      g * (d * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * d⁻¹) * g⁻¹ := by group
  rw [e1, e2, hch₂ y, hu (slConjugation n k (signGL k σ₂) y), hu y,
    hch₂ (slConjugation n k (diagGL u) y)]
  exact congrArg _ (slConjugation_diagGL_comm u (fun i => signUnit k (σ₂ i)) y)

end Main

section Delta

variable {X : Type} [Group X] [Finite X] [Finite k]

theorem exists_pair_of_card_four {F : Subgroup X} (hcard : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1) :
    ∃ a ∈ F, ∃ b ∈ F, a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 := by
  obtain ⟨a, haF, ha1⟩ : ∃ a ∈ F, a ≠ 1 :=
    CFSG.ClassicalInvolution.Balance.exists_ne_one_of_card_eq_two_pow (n := 2) (by norm_num)
      (by rw [hcard]; norm_num)
  obtain ⟨b, hbF, hb1, hba⟩ : ∃ b ∈ F, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (F : Set X) ⊆ {1, a} := by
      intro z hz
      by_cases hz1 : z = 1
      · simp [hz1]
      · simp [hcon z hz hz1]
    have h1 : Nat.card F ≤ 2 := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      calc Nat.card F = (F : Set X).ncard := (Nat.card_coe_set_eq _)
        _ ≤ ({1, a} : Set X).ncard := this
        _ ≤ 2 := (Set.ncard_insert_le 1 {a}).trans (by simp)
    omega
  refine ⟨a, haF, b, hbF, ha1, hb1, fun h => hba ?_⟩
  have ha2 : a * a = 1 := hF2 a haF
  calc b = a⁻¹ * (a * b) := by group
    _ = a⁻¹ := by rw [h, mul_one]
    _ = a := inv_eq_of_mul_eq_one_right ha2

omit [Finite k] in
theorem const_of_three (σ₁ σ₂ : Fin n → Bool) (u₁ u₂ u₃ : Fin n → kˣ)
    (hc₁ : ∀ i j, σ₁ i = σ₁ j → u₁ i = u₁ j) (hc₂ : ∀ i j, σ₂ i = σ₂ j → u₂ i = u₂ j)
    (hc₃ : ∀ i j, decide (σ₁ i = σ₂ i) = decide (σ₁ j = σ₂ j) → u₃ i = u₃ j)
    (e12 : ∀ y, slConjugation n k (diagGL u₁) y = slConjugation n k (diagGL u₂) y)
    (e13 : ∀ y, slConjugation n k (diagGL u₁) y = slConjugation n k (diagGL u₃) y) :
    ∀ i j, u₁ i = u₁ j := by
  intro i j
  by_cases hij : σ₁ i = σ₁ j
  · exact hc₁ i j hij
  · have hne : i ≠ j := fun h => hij (by rw [h])
    by_cases hij₂ : σ₂ i = σ₂ j
    · have h1 := ratio_eq_of_slConjugation_eq u₁ u₂ e12 hne
      rw [hc₂ i j hij₂, mul_inv_cancel] at h1
      exact mul_inv_eq_one.mp h1
    · have hx := decide_eq_of_ne hij hij₂
      have h1 := ratio_eq_of_slConjugation_eq u₁ u₃ e13 hne
      rw [hc₃ i j hx, mul_inv_cancel] at h1
      exact mul_inv_eq_one.mp h1

theorem deltaCore_trivial_split (hn : 3 ≤ n) (h2 : (2 : k) ≠ 0) (h4 : 4 ≤ Nat.card k)
    (hcl : LinearAutClassification k n) (ψ : SL(n, k) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (P : Subgroup SL(n, k)) (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hact : ∀ f ∈ F, ∃ x ∈ P, (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) ∧
      ∃ s : k, s ≠ 0 ∧
        (x : Matrix (Fin n) (Fin n) k) * x = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    {d : X} (hd : d ∈ CFSG.ClassicalInvolution.Balance.deltaCore F) {x : X} (hx : x ∈ ψ.range) :
    d * x = x * d := by
  have hn0 : 0 < n := by omega
  obtain ⟨a, haF, b, hbF, ha1, hb1, hab1⟩ := exists_pair_of_card_four hcard hF2
  have hdmem : ∀ f ∈ F, f ≠ 1 → d ∈ involutionOddCore f := fun f hf hf1 =>
    CFSG.ClassicalInvolution.Balance.mem_deltaCore_iff.mp hd f hf hf1
  obtain ⟨P₀, σ₁, σ₂, hch₁, hch₂⟩ := exists_chart_of_lifts hn0 h2 ψ P hP hact haF hbF
  have hrange : (ψ.comp (MulAut.conj P₀).toMonoidHom).range = ψ.range :=
    CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hΨnorm : (ψ.comp (MulAut.conj P₀).toMonoidHom).range.Normal := by
    rw [hrange]
    exact hnorm
  have hΨker := ker_comp_conj_le_center ψ hker P₀
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
  have hperf : Group.IsPerfect SL(n, k) :=
    ⟨((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple n k
        (by omega) (Or.inr (by omega)) (Or.inr (by omega)))).1⟩
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

section Final

variable {X : Type} [Group X] [Finite X] [Finite k]

theorem strongConclusion_linear_split (hn : 3 ≤ n) (h2 : (2 : k) ≠ 0) (h4 : 4 ≤ Nat.card k)
    (hcl : LinearAutClassification k n) (ψ : SL(n, k) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (P : Subgroup SL(n, k)) (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hact : ∀ f ∈ F, ∃ x ∈ P, (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) ∧
      ∃ s : k, s ≠ 0 ∧
        (x : Matrix (Fin n) (Fin n) k) * x = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k)) :
    StrongConclusion ψ.range F :=
  ⟨fun _ hd _ hx => deltaCore_trivial_split hn h2 h4 hcl ψ hker hnorm hcard hF2 P hP hact hd hx,
    fun _ hf _ _ hd _ hg _ hx => commutator_trivial_split hn h2 h4 hcl ψ hker hnorm P hP hact hf
      hd hg hx⟩

end Final


section Model

variable {p e : ℕ} [Fact p.Prime]

theorem strongConclusion_gf_split {n : ℕ} (hn : 3 ≤ n) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    {X : Type} [Group X] [Finite X] (ψ : SL(n, GaloisField p e) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField p e)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (P : Subgroup SL(n, GaloisField p e)) (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hact : ∀ f ∈ F, ∃ x ∈ P, (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) ∧
      ∃ s : GaloisField p e, s ≠ 0 ∧ (x : Matrix (Fin n) (Fin n) (GaloisField p e)) * x =
        (s ^ 2) • (1 : Matrix (Fin n) (Fin n) (GaloisField p e))) :
    StrongConclusion ψ.range F := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  exact strongConclusion_linear_split hn
    (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2) h4
    (CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2 h5 hn) ψ hker hnorm
    hcard hF2 P hP hact

end Model

section RankOne

variable {k : Type} [Field k]

theorem sl2_involution_central (h2 : (2 : k) ≠ 0) {x : SL(2, k)} (hx : x * x = 1) :
    x ∈ Subgroup.center SL(2, k) := by
  have hM : (x : Matrix (Fin 2) (Fin 2) k) * x = 1 := by
    have := congrArg (fun z : SL(2, k) => (z : Matrix (Fin 2) (Fin 2) k)) hx
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this
  have hdet : (x : Matrix (Fin 2) (Fin 2) k).det = 1 := x.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
    at e00 e01 e10 e11
  set a := (x : Matrix (Fin 2) (Fin 2) k) 0 0
  set b := (x : Matrix (Fin 2) (Fin 2) k) 0 1
  set c := (x : Matrix (Fin 2) (Fin 2) k) 1 0
  set d := (x : Matrix (Fin 2) (Fin 2) k) 1 1
  have hsum : a + d ≠ 0 := by
    intro h
    have : (2 : k) = 0 := by
      have hd : d = -a := by linear_combination h
      rw [hd] at hdet
      linear_combination (-1 : k) * (hdet + e00)
    exact h2 this
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hsum
  have had : a = d := by
    have : (a - d) * (a + d) = 0 := by rw [hb, hc] at e00 e11; linear_combination e00 - e11
    have := (mul_eq_zero.mp this).resolve_right hsum
    linear_combination this
  have hxs : (x : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, hb, hc, had]
  refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hxs, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

end RankOne

section FramePSL

theorem coe_mul_self_eq_one {k : Type} [Field k] {n : ℕ} {x : SL(n, k)} (h : x * x = 1) :
    (x : Matrix (Fin n) (Fin n) k) * x = 1 := by
  have := congrArg (fun z : SL(n, k) => (z : Matrix (Fin n) (Fin n) k)) h
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this

theorem conj_eq_of_mem_center {K : Type} [Group K] {x : K} (hx : x ∈ Subgroup.center K) (y : K) :
    x * y * x⁻¹ = y := by
  rw [(Subgroup.mem_center_iff.mp hx y).symm, mul_inv_cancel_right]

open CFSG.ClassicalInvolution.ModelFacts (mul_self_eq_one_of_mem_center_longRootSet)
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem strongLocalTwoBalanceFrameAt_PSL : StrongLocalTwoBalanceFrameAt .PSL := by
  intro n p e hp _ hfund hadm hp2 h5 X _ _ ψ hker hnorm 𝓜 h𝓜 hcomm F hcard hF2 hfaith hact
  have : Fact p.Prime := ⟨hp⟩
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsq : ∀ R ∈ fundamentalSubgroups .PSL
      (modelUniv .PSL (m + 1) p e hp).D, ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r * r = 1 :=
    fun R hR r hr hrc => mul_self_eq_one_of_mem_center_longRootSet
      (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset hn hR) hr hrc
  obtain ⟨P, hP, hP2, hlift⟩ := exists_involutory_lifts_of_frameGroup .PSL (m + 1) p e hp hfund
    hadm hp2 h5 ψ hker 𝓜 h𝓜 hcomm hsq hact
  by_cases h3 : 3 ≤ m + 1
  · refine strongConclusion_gf_split h3 hp2 h5 ψ hker hnorm hcard hF2 P hP fun f hf => ?_
    obtain ⟨x, hxP, hxa⟩ := hlift f hf
    refine ⟨x, hxP, hxa, 1, one_ne_zero, ?_⟩
    rw [one_pow, one_smul]
    exact coe_mul_self_eq_one (hP2 x hxP)
  · exfalso
    obtain rfl : m = 1 := by omega
    obtain ⟨f, hfF, hf1⟩ : ∃ f ∈ F, f ≠ 1 :=
      CFSG.ClassicalInvolution.Balance.exists_ne_one_of_card_eq_two_pow (n := 2) (by norm_num)
        (by rw [hcard]; norm_num)
    obtain ⟨x, hxP, hxa⟩ := hlift f hfF
    have hcen : x ∈ Subgroup.center (modelUniv .PSL (1 + 1) p e hp).K :=
      sl2_involution_central (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2)
        (hP2 x hxP)
    refine hfaith f hfF hf1 ?_
    rintro _ ⟨y, rfl⟩
    have h1 : f * ψ y * f⁻¹ = ψ y := by
      rw [hxa y]
      congr 1
      exact conj_eq_of_mem_center hcen y
    exact mul_inv_eq_iff_eq_mul.mp h1

end FramePSL

end CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
