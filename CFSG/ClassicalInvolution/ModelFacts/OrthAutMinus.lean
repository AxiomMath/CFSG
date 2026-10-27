module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutTailB

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

section MinusFacts

variable {F : Type} [Field F] [Finite F] {n : ℕ} {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem minus_hker2 : ∀ x ∈ (spinAction (quadMinus n F b c)).ker, x * x = 1 := fun x hx => by
  rw [← ker_spinMatrix] at hx
  exact spin_mul_self_eq_one ((mem_ker_spinMatrix_quadMinus_iff hirr x).mp hx)

variable {p : ℕ} [Fact p.Prime] [CharP F p]

include hirr in
theorem minus_center_facts (hp2 : p ≠ 2) (hn : 4 ≤ n) :
    (∀ ζ ∈ Subgroup.center (spinGroup (quadMinus n F b c)), ζ ^ p = 1 → ζ = 1) ∧
    (∀ ζ ∈ Subgroup.center (spinGroup (quadMinus n F b c)),
      ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x, spinAction (quadMinus n F b c) ζ x = η • x) := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus hn hirr
  have hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadMinus n F b c))) :=
    not_dvd_card_center_spin (quadMinus n F b c) (range_spinMatrix_quadMinus hn hirr) hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadMinus_iff hirr x).mp hx)) hp2
  refine ⟨fun ζ hζ hp1 => ?_, fun ζ hζ => ?_⟩
  · by_contra hne
    have h1 : orderOf ζ ∣ p := orderOf_dvd_of_pow_eq_one hp1
    have h2 : orderOf ζ = p := by
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    exact hC (h2 ▸ Subgroup.orderOf_dvd_natCard _ hζ)
  · have hζ' : ζ ∈ (StatedScalars _ F).comap (spinMatrix (quadMinus n F b c)) := by
      rw [← hcomap, hZ]
      exact hζ
    obtain ⟨c', hc⟩ := Subgroup.mem_comap.mp hζ'
    have hact : ∀ x, spinAction (quadMinus n F b c) ζ x = (c' : F) • x := fun x => by
      rw [← spinMatrix_mulVec, ← hc]
      ext i
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
    refine ⟨(c' : F), ?_, hact⟩
    have h1 := map_spinAction (quadMinus n F b c) ζ (planeVec n planeOne)
    rw [hact, QuadraticMap.map_smul, quadMinus_planeOne] at h1
    have h2 : (c' : F) * (c' : F) = 1 := by simpa using h1
    exact mul_self_eq_one_iff.mp h2

end MinusFacts

section Lift

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {b c : F}

theorem exists_isConj_lift_minus (hp2 : p ≠ 2) {n : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type} [Group X]
    (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c))) (σ : X ≃* X)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range) :
    ∃ (α : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c))
      (g : SemiSim (quadMinus n F b c)), (∀ x, θ (α x) = σ (θ x)) ∧ IsConj α g := by
  have hσR : ∀ r ∈ θ.range, σ r ∈ θ.range := by
    rintro r ⟨k, rfl⟩
    exact hσr k
  let σR : θ.range ≃* θ.range :=
    { toFun := fun r => ⟨σ r, hσR r r.2⟩
      invFun := fun r => ⟨σ r, hσR r r.2⟩
      left_inv := fun r => Subtype.ext (hσ2 r)
      right_inv := fun r => Subtype.ext (hσ2 r)
      map_mul' := fun a b => Subtype.ext (map_mul σ (a : X) (b : X)) }
  have hkerR : θ.rangeRestrict.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c)) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨α, hα, A, φ, μ, hQ, hA⟩ := spinMinus_exists_lift_similarity hp2 hn hf hF hirr
    θ.rangeRestrict θ.rangeRestrict_surjective hkerR σR
  exact ⟨α, SemiSim.ofMatrix _ A φ μ hQ, fun x => congrArg Subtype.val (hα x),
    isConj_ofMatrix A φ μ hQ hA⟩

end Lift


section Plane

variable {F : Type} [Field F] {n : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem spinAction_twShortRoot_eq_eichler (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → F) :
    spinAction (quadMinus n F b c) (twShortRoot n hirr i s (.ofAdd p)) =
      eichler (quadMinus n F b c) (minusVec n i s) (planeVec n p) := by
  refine LinearEquiv.ext fun v => ?_
  rw [spinAction_twShortRoot, eichler_apply (quadMinus_minusVec n b c i s)
    (polar_minusVec_planeVec n b c i s p), quadMinus_planeVec']
  module

variable {p : ℕ} [Fact p.Prime] [CharP F p]

theorem IsConj.twShortRoot_eq (hp2 : p ≠ 2)
    (hker : ∀ x ∈ (spinAction (quadMinus n F b c)).ker, x * x = 1)
    {α : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c)}
    {g : SemiSim (quadMinus n F b c)} (h : IsConj α g) (lam : Fin (n - 1) → Bool → F)
    (hg : ∀ i s, g (minusVec n i s) = lam i s • minusVec n i s)
    (L : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) (hL : ∀ w, g (planeVec n w) = planeVec n (L w))
    (i : Fin (n - 1)) (s : Bool) (w : Fin 2 → F) :
    α (twShortRoot n hirr i s (.ofAdd w)) =
      twShortRoot n hirr i s (.ofAdd ((lam i s * (g.μ : F)⁻¹) • L w)) := by
  let κ' : F := lam i s * (g.μ : F)⁻¹
  let ψ : (Fin 2 → F) →+ (Fin 2 → F) := (κ' • L).toAddMonoidHom
  let f₁ : Multiplicative (Fin 2 → F) →* spinGroup (quadMinus n F b c) :=
    (α : spinGroup (quadMinus n F b c) →* spinGroup (quadMinus n F b c)).comp
      (twShortRoot n hirr i s)
  let f₂ : Multiplicative (Fin 2 → F) →* spinGroup (quadMinus n F b c) :=
    (twShortRoot n hirr i s).comp (AddMonoidHom.toMultiplicative ψ)
  have key : ∀ w' : Fin 2 → F, spinAction (quadMinus n F b c) (f₁ (.ofAdd w')) =
      spinAction (quadMinus n F b c) (f₂ (.ofAdd w')) := fun w' => by
    have hu : (quadMinus n F b c) (minusVec n i s) = 0 := quadMinus_minusVec n b c i s
    have huw : polar (quadMinus n F b c) (minusVec n i s) (planeVec n w') = 0 :=
      polar_minusVec_planeVec n b c i s w'
    have h1 := h.spinAction_eq_eichler (spinAction_twShortRoot_eq_eichler hirr i s w') hu huw
    change spinAction (quadMinus n F b c) (α (twShortRoot n hirr i s (.ofAdd w'))) =
      spinAction (quadMinus n F b c) (twShortRoot n hirr i s (.ofAdd (ψ w')))
    rw [h1, spinAction_twShortRoot_eq_eichler hirr, hg, hL]
    have huw' : polar (quadMinus n F b c) (minusVec n i s)
        (((g.μ : F)⁻¹) • planeVec n (L w')) = 0 := by
      rw [polar_smul_right, polar_minusVec_planeVec, smul_zero]
    rw [eichler_smul_left _ hu huw']
    congr 1
    change _ = planeVec n ((κ' • L) w')
    rw [LinearMap.smul_apply, planeVec_smul, smul_smul]
  have hW : ∀ w' : Fin 2 → F, p • w' = 0 := fun w' => by
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  have hfg : f₁ = f₂ := hom_eq_of_spinAction_eq hp2 hker f₁ f₂ hW
    (fun w' => key (Multiplicative.toAdd w'))
  have hc := congrArg (fun f : Multiplicative (Fin 2 → F) →* spinGroup (quadMinus n F b c) =>
    f (.ofAdd w)) hfg
  exact hc

end Plane


section PlaneMap

variable {F : Type} [Field F] {n : ℕ} {b c : F}

theorem exists_planeMap (g : SemiSim (quadMinus n F b c)) (hφ : ∀ c', g.φ c' = c')
    (hC : ∀ y : Vm n F, (∀ a r, polar (quadMinus n F b c) y (minusVec n a r) = 0) →
      ∀ a r, polar (quadMinus n F b c) (g y) (minusVec n a r) = 0) :
    ∃ L : (Fin 2 → F) →ₗ[F] (Fin 2 → F), (∀ w, g (planeVec n w) = planeVec n (L w)) ∧
      ∀ w, planeNorm b c (L w) = (g.μ : F) * planeNorm b c w := by
  let Lf : (Fin 2 → F) → (Fin 2 → F) := fun w t => (g (planeVec n w)) (.inr (.inr t))
  have hLw : ∀ w, g (planeVec n w) = planeVec n (Lf w) := fun w =>
    eq_planeVec_of_polar_minusVec n b c (hC _ (fun a r => polar_planeVec_minusVec n b c w a r))
  refine ⟨{ toFun := Lf, map_add' := ?_, map_smul' := ?_ }, hLw, ?_⟩
  · intro w w'
    apply planeVec_injective n
    calc planeVec n (Lf (w + w')) = g (planeVec n (w + w')) := (hLw _).symm
      _ = g (planeVec n w) + g (planeVec n w') := by rw [planeVec_add, g.map_add]
      _ = planeVec n (Lf w + Lf w') := by rw [hLw, hLw, planeVec_add]
  · intro r w
    apply planeVec_injective n
    calc planeVec n (Lf (r • w)) = g (planeVec n (r • w)) := (hLw _).symm
      _ = r • g (planeVec n w) := by rw [planeVec_smul, g.map_smul, hφ]
      _ = planeVec n ((RingHom.id F) r • Lf w) := by rw [hLw, RingHom.id_apply, planeVec_smul]
  · intro w
    have := g.map_Q (planeVec n w)
    rw [hLw w, quadMinus_planeVec', quadMinus_planeVec', hφ] at this
    exact this

end PlaneMap


section NoNeg

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem no_neg_square (h2 : (2 : F) ≠ 0) (L : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) {μ lam : F}
    (hμ : μ ≠ 0) (hN : ∀ w, planeNorm b c (L w) = μ * planeNorm b c w)
    (hL2 : ∀ w, L (L w) = (-μ) • w) (hlam : lam * lam = -μ) : False := by
  have hw0 : (planeOne : Fin 2 → F) ≠ 0 := planeOne_ne_zero
  have hn1 : planeNorm b c (planeOne : Fin 2 → F) = 1 := planeNorm_planeOne
  have h2μ : 2 * μ ≠ 0 := mul_ne_zero h2 hμ
  by_cases hu : L planeOne + lam • (planeOne : Fin 2 → F) = 0
  · have hL : L planeOne = (-lam) • (planeOne : Fin 2 → F) := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hu
    have h1 := hN planeOne
    rw [hL, planeNorm_smul, hn1, neg_sq, _root_.sq, hlam] at h1
    apply h2μ
    linear_combination -h1
  · have hLu : L (L planeOne + lam • (planeOne : Fin 2 → F)) =
        lam • (L planeOne + lam • (planeOne : Fin 2 → F)) := by
      rw [map_add, map_smul, hL2, smul_add, smul_smul, hlam]
      abel
    have h1 := hN (L planeOne + lam • (planeOne : Fin 2 → F))
    rw [hLu, planeNorm_smul, _root_.sq, hlam] at h1
    have h3 : (2 * μ) * planeNorm b c (L planeOne + lam • (planeOne : Fin 2 → F)) = 0 := by
      linear_combination -h1
    exact planeNorm_ne_zero hirr hu ((mul_eq_zero.mp h3).resolve_left h2μ)

end NoNeg


section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {b c : F}

omit [Finite F] [Fact p.Prime] in
theorem twShortRoot_pow_char (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (i : Fin (n - 1))
    (s : Bool) (w : Fin 2 → F) : (twShortRoot n hirr i s (.ofAdd w)) ^ p = 1 := by
  have hW : p • w = 0 := by rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  rw [← map_pow, ← ofAdd_nsmul, hW, ofAdd_zero, map_one]

structure MinusAct (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (A : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c))
    (lam : Fin (n - 1) → Bool → F) (μ : F) (L : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) : Prop where
  ne_zero : μ ≠ 0
  involutive : ∀ y, A (A y) = y
  prod : ∀ i, lam i true * lam i false = μ
  norm : ∀ w, planeNorm b c (L w) = μ * planeNorm b c w
  long : ∀ (i j : Fin (n - 1)) (hij : i ≠ j) (s t : Bool) (c' : F),
    A ((minusFrame n b c).longRoot hij s t (.ofAdd c')) =
      (minusFrame n b c).longRoot hij s t (.ofAdd ((lam j t * (μ⁻¹ * lam i s)) * c'))
  short : ∀ (i : Fin (n - 1)) (s : Bool) (w : Fin 2 → F),
    A (twShortRoot n hirr i s (.ofAdd w)) =
      twShortRoot n hirr i s (.ofAdd ((lam i s * μ⁻¹) • L w))

namespace MinusAct

variable {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {n : ℕ}
  {A : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c)}
  {lam : Fin (n - 1) → Bool → F} {μ : F} {L : (Fin 2 → F) →ₗ[F] (Fin 2 → F)}

omit [Finite F] in
theorem msq (h : MinusAct hirr A lam μ L) (i : Fin (n - 1)) (s : Bool) (w : Fin 2 → F) :
    ((lam i s * μ⁻¹) * (lam i s * μ⁻¹)) • L (L w) = w := by
  have h1 := map_sq_of_involution A h.involutive (twShortRoot n hirr i s)
    (twShortRoot_injective n hirr i s) (fun w' => (lam i s * μ⁻¹) • L w') (h.short i s) w
  simpa [map_smul, smul_smul] using h1

omit [Finite F] in
theorem lam_ne_zero (h : MinusAct hirr A lam μ L) (i : Fin (n - 1)) (s : Bool) : lam i s ≠ 0 := by
  intro h0
  have := h.prod i
  cases s
  · rw [h0, mul_zero] at this
    exact h.ne_zero this.symm
  · rw [h0, zero_mul] at this
    exact h.ne_zero this.symm

end MinusAct

omit [Fact p.Prime] [Finite F] in
theorem minus_scalar (h2 : (2 : F) ≠ 0) {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {n : ℕ} {X : Type}
    [Group X] (hZ : ∀ ζ ∈ Subgroup.center (spinGroup (quadMinus n F b c)), ζ ^ p = 1 → ζ = 1)
    (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c))) (σ : X ≃* X)
    (α A : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c))
    (κ : spinGroup (quadMinus n F b c)) (hαθ : ∀ y, θ (α y) = σ (θ y))
    (hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹) {lam : Fin (n - 1) → Bool → F} {μ : F}
    {L : (Fin 2 → F) →ₗ[F] (Fin 2 → F)} (h : MinusAct hirr A lam μ L) (ρ : F)
    (hρ : ∀ w, L w = ρ • w) :
    ∃ v : Fin (n - 1) → ZMod 2, ∀ γ : Fin (n - 1) → ℤ,
      γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅ →
      ((((minusRootGroup n hirr γ ⊔ minusRootGroup n hirr (-γ)).map
          (MulAut.conj κ).toMonoidHom).map θ).map σ.toMonoidHom =
        ((minusRootGroup n hirr γ ⊔ minusRootGroup n hirr (-γ)).map
          (MulAut.conj κ).toMonoidHom).map θ) ∧
      ((∀ y ∈ ((minusRootGroup n hirr γ ⊔ minusRootGroup n hirr (-γ)).map
          (MulAut.conj κ).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  have hp0 : (planeOne : Fin 2 → F) ≠ 0 := planeOne_ne_zero
  have hμ0 := h.ne_zero
  have hsm : ∀ r : F, r • (planeOne : Fin 2 → F) = planeOne → r = 1 := fun r h' => by
    have h'' : (r - 1) • (planeOne : Fin 2 → F) = 0 := by rw [sub_smul, h', one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h'').resolve_right hp0)
  have hρ2 : ρ * ρ = μ := by
    have h1 := h.norm planeOne
    rw [hρ, planeNorm_smul, planeNorm_planeOne] at h1
    simpa [_root_.sq] using h1
  have hlamsq : ∀ i s, lam i s * lam i s = μ := by
    intro i s
    have h1 := h.msq i s planeOne
    simp only [hρ, smul_smul] at h1
    have h3 := hsm _ h1
    rw [hρ2] at h3
    field_simp at h3
    simpa [_root_.sq] using h3
  have hM : ∀ i s, (∀ w, (fun w' : Fin 2 → F => (lam i s * μ⁻¹) • L w') w = w) ↔
      (True ∧ lam i s * (μ⁻¹ * ρ) = 1) := by
    intro i s
    constructor
    · intro h'
      refine ⟨trivial, ?_⟩
      have h1 := h' planeOne
      simp only [hρ, smul_smul] at h1
      rw [← mul_assoc]
      exact hsm _ h1
    · rintro ⟨-, h'⟩ w
      simp only [hρ, smul_smul]
      rw [← mul_assoc] at h'
      rw [h', one_smul]
  obtain ⟨v, hv⟩ := toral_tail_B h2 hZ θ hker σ α A κ hαθ hA h.involutive (minusRootGroup n hirr)
    (fun i j hij s t => (minusFrame n b c).longRoot hij s t) (fun i s => twShortRoot n hirr i s)
    (fun i j hij s t => (minusFrame n b c).longRoot_injective hij s t)
    (fun i j hij s t c' => longRoot_pow_char (minusFrame n b c).toHypFrame hij s t c')
    (fun i s => twShortRoot_injective n hirr i s) (fun i s w => twShortRoot_pow_char hirr i s w)
    (fun γ i j hij s t h' => minusRootGroup_eq_long n hirr hij s t h')
    (fun γ i s h' => minusRootGroup_eq_short n hirr i s h') lam μ ρ hμ0 hρ2 h.prod hlamsq
    h.long (fun i s w => (lam i s * μ⁻¹) • L w) h.short True hM
  refine ⟨v, fun γ hγ => ⟨(hv γ hγ).1, (hv γ hγ).2.trans ?_⟩⟩
  simp

omit [Fact p.Prime] [Finite F] in
theorem minus_nonscalar (h2 : (2 : F) ≠ 0) {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {n : ℕ}
    {X : Type} [Group X]
    (hZ : ∀ ζ ∈ Subgroup.center (spinGroup (quadMinus n F b c)), ζ ^ p = 1 → ζ = 1)
    (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c))) (σ : X ≃* X)
    (α A : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c))
    (κ : spinGroup (quadMinus n F b c)) (hαθ : ∀ y, θ (α y) = σ (θ y))
    (hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹) {lam : Fin (n - 1) → Bool → F} {μ : F}
    {L : (Fin 2 → F) →ₗ[F] (Fin 2 → F)} (h : MinusAct hirr A lam μ L) (i₀ : Fin (n - 1))
    (hS : ¬ ∃ ρ : F, ∀ w, L w = ρ • w) :
    ∃ v : Fin (n - 1) → ZMod 2, ∀ γ : Fin (n - 1) → ℤ,
      γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅ →
      ((((minusRootGroup n hirr γ ⊔ minusRootGroup n hirr (-γ)).map
          (MulAut.conj κ).toMonoidHom).map θ).map σ.toMonoidHom =
        ((minusRootGroup n hirr γ ⊔ minusRootGroup n hirr (-γ)).map
          (MulAut.conj κ).toMonoidHom).map θ) ∧
      ((∀ y ∈ ((minusRootGroup n hirr γ ⊔ minusRootGroup n hirr (-γ)).map
          (MulAut.conj κ).toMonoidHom).map θ, σ y = y) ↔
        (∑ i, (γ i : ZMod 2) * v i = 0 ∧
          ¬ ∃ (i : Fin (n - 1)) (s : Bool), toStdB (n - 1) γ = Pi.single i (boolSign s))) := by
  have hp0 : (planeOne : Fin 2 → F) ≠ 0 := planeOne_ne_zero
  have hμ0 := h.ne_zero
  have hLLne : L (L planeOne) ≠ 0 := by
    intro h0
    have h1 := h.norm (L planeOne)
    rw [h0, planeNorm_zero, h.norm planeOne, planeNorm_planeOne] at h1
    exact hμ0 (by
      have : μ * (μ * 1) = 0 := h1.symm
      rw [mul_one] at this
      exact mul_self_eq_zero.mp this)
  have hconst : ∀ i s, lam i s * lam i s = lam i₀ true * lam i₀ true := by
    intro i s
    have h3 : ((lam i s * μ⁻¹ * (lam i s * μ⁻¹)) -
        (lam i₀ true * μ⁻¹ * (lam i₀ true * μ⁻¹))) • L (L planeOne) = 0 := by
      rw [sub_smul, h.msq i s planeOne, h.msq i₀ true planeOne, sub_self]
    have h4 := (smul_eq_zero.mp h3).resolve_right hLLne
    have h5 : (lam i s * lam i s - lam i₀ true * lam i₀ true) * (μ⁻¹ * μ⁻¹) = 0 := by
      linear_combination h4
    have h6 := (mul_eq_zero.mp h5).resolve_right (mul_ne_zero (inv_ne_zero hμ0) (inv_ne_zero hμ0))
    exact sub_eq_zero.mp h6
  have hν2 : (lam i₀ true * lam i₀ true) * (lam i₀ true * lam i₀ true) = μ * μ := by
    calc _ = (lam i₀ true * lam i₀ true) * (lam i₀ false * lam i₀ false) := by
          rw [hconst i₀ false]
      _ = (lam i₀ true * lam i₀ false) * (lam i₀ true * lam i₀ false) := by ring
      _ = μ * μ := by rw [h.prod i₀]
  have hνμ : lam i₀ true * lam i₀ true = μ := by
    rcases mul_self_eq_mul_self_iff.mp hν2 with h' | h'
    · exact h'
    · exfalso
      have hL2 : ∀ w, L (L w) = (-μ) • w := by
        intro w
        have e : (-μ) * ((lam i₀ true * μ⁻¹) * (lam i₀ true * μ⁻¹)) = 1 := by
          calc _ = (-μ) * ((lam i₀ true * lam i₀ true) * (μ⁻¹ * μ⁻¹)) := by ring
            _ = 1 := by rw [h']; field_simp
        calc L (L w) = ((-μ) * ((lam i₀ true * μ⁻¹) * (lam i₀ true * μ⁻¹))) • L (L w) := by
              rw [e, one_smul]
          _ = (-μ) • (((lam i₀ true * μ⁻¹) * (lam i₀ true * μ⁻¹)) • L (L w)) := mul_smul _ _ _
          _ = (-μ) • w := by rw [h.msq i₀ true w]
      exact no_neg_square hirr h2 L hμ0 h.norm hL2 h'
  have hlamsq : ∀ i s, lam i s * lam i s = μ := fun i s => (hconst i s).trans hνμ
  have hM : ∀ i s, (∀ w, (fun w' : Fin 2 → F => (lam i s * μ⁻¹) • L w') w = w) ↔
      (False ∧ lam i s * (μ⁻¹ * lam i₀ true) = 1) := by
    intro i s
    constructor
    · intro h'
      exfalso
      have hl0 : lam i s ≠ 0 := h.lam_ne_zero i s
      have hχ0 : lam i s * μ⁻¹ ≠ 0 := mul_ne_zero hl0 (inv_ne_zero hμ0)
      exact hS ⟨(lam i s * μ⁻¹)⁻¹, fun w => by
        have hw : (lam i s * μ⁻¹) • L w = w := h' w
        calc L w = (lam i s * μ⁻¹)⁻¹ • ((lam i s * μ⁻¹) • L w) := by
              rw [smul_smul, inv_mul_cancel₀ hχ0, one_smul]
          _ = (lam i s * μ⁻¹)⁻¹ • w := by rw [hw]⟩
    · rintro ⟨h', -⟩
      exact h'.elim
  obtain ⟨v, hv⟩ := toral_tail_B h2 hZ θ hker σ α A κ hαθ hA h.involutive (minusRootGroup n hirr)
    (fun i j hij s t => (minusFrame n b c).longRoot hij s t) (fun i s => twShortRoot n hirr i s)
    (fun i j hij s t => (minusFrame n b c).longRoot_injective hij s t)
    (fun i j hij s t c' => longRoot_pow_char (minusFrame n b c).toHypFrame hij s t c')
    (fun i s => twShortRoot_injective n hirr i s) (fun i s w => twShortRoot_pow_char hirr i s w)
    (fun γ i j hij s t h' => minusRootGroup_eq_long n hirr hij s t h')
    (fun γ i s h' => minusRootGroup_eq_short n hirr i s h') lam μ (lam i₀ true) hμ0 hνμ h.prod
    hlamsq h.long (fun i s w => (lam i s * μ⁻¹) • L w) h.short False hM
  exact ⟨v, fun γ hγ => ⟨(hv γ hγ).1, (hv γ hγ).2⟩⟩


omit [Finite F] [Fact p.Prime] in
theorem minus_short_fixed_scalar
    {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {n : ℕ} {X : Type} [Group X]
    (hZ : ∀ ζ ∈ Subgroup.center (spinGroup (quadMinus n F b c)), ζ ^ p = 1 → ζ = 1)
    (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c))) (σ : X ≃* X)
    (α A : spinGroup (quadMinus n F b c) ≃* spinGroup (quadMinus n F b c))
    (k κ r : spinGroup (quadMinus n F b c)) (hαθ : ∀ y, θ (α y) = σ (θ y))
    (hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹) (hκ : κ = k * r⁻¹) {i₀ i₁ : Fin (n - 1)}
    (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)
    (hr : ∀ x, (firstFrame (minusFrame n b c).toHypFrame h01 s₀ t₀).coords x = 0 →
      spinAction (quadMinus n F b c) r x = x)
    {lam : Fin (n - 1) → Bool → F} {μ : F} {L : (Fin 2 → F) →ₗ[F] (Fin 2 → F)}
    (h : MinusAct hirr A lam μ L) (a : Fin (n - 1)) (s' : Bool) (ha0 : a ≠ i₀) (ha1 : a ≠ i₁)
    (hfix : ∀ w : Fin 2 → F, σ (θ (k * twShortRoot n hirr a s' (.ofAdd w) * k⁻¹)) =
      θ (k * twShortRoot n hirr a s' (.ofAdd w) * k⁻¹)) :
    ∃ ρ : F, ∀ w, L w = ρ • w := by
  have hμ0 := h.ne_zero
  have hl0 : lam a s' ≠ 0 := h.lam_ne_zero a s'
  have hχ0 : lam a s' * μ⁻¹ ≠ 0 := mul_ne_zero hl0 (inv_ne_zero hμ0)
  have hcen : ∀ y, σ (θ y) = θ y →
      α y * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c)) :=
    fun y hy => hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hy, mul_inv_cancel])
  have hAfix : ∀ w : Fin 2 → F, A (twShortRoot n hirr a s' (.ofAdd w)) =
      twShortRoot n hirr a s' (.ofAdd w) := by
    intro w
    have hy : (k * twShortRoot n hirr a s' (.ofAdd w) * k⁻¹) ^ p = 1 := by
      rw [conj_pow, twShortRoot_pow_char hirr, mul_one, mul_inv_cancel]
    have h1 : α (k * twShortRoot n hirr a s' (.ofAdd w) * k⁻¹) =
        k * twShortRoot n hirr a s' (.ofAdd w) * k⁻¹ :=
      eq_of_central_ambiguity hZ α hy (hcen _ (hfix w))
    have hx0 : (firstFrame (minusFrame n b c).toHypFrame h01 s₀ t₀).coords (minusVec n a s') = 0 :=
      coords_firstFrame_vec (minusFrame n b c).toHypFrame h01 s₀ t₀ ha0 ha1 s'
    have hx1 : (firstFrame (minusFrame n b c).toHypFrame h01 s₀ t₀).coords (planeVec n w) = 0 :=
      coords_eq_zero_of_orth (minusFrame n b c).toHypFrame h01 s₀ t₀
        (fun a' r' => polar_planeVec_minusVec n b c w a' r')
    have hrx : r * twShortRoot n hirr a s' (.ofAdd w) * r⁻¹ =
        twShortRoot n hirr a s' (.ofAdd w) := by
      have := conj_twShortRoot n hirr r a s' (i' := a) (s' := s') (p := w) (q := w) (r := 1)
        (by rw [hr _ hx0, one_smul]) (hr _ hx1)
      rw [this, one_smul]
    have h2' := hA (r * twShortRoot n hirr a s' (.ofAdd w) * r⁻¹)
    have h3 : κ * (r * twShortRoot n hirr a s' (.ofAdd w) * r⁻¹) * κ⁻¹ =
        k * twShortRoot n hirr a s' (.ofAdd w) * k⁻¹ := by rw [hκ]; group
    rw [h3, h1] at h2'
    have h4 : κ * (r * twShortRoot n hirr a s' (.ofAdd w) * r⁻¹) * κ⁻¹ =
        κ * A (r * twShortRoot n hirr a s' (.ofAdd w) * r⁻¹) * κ⁻¹ := by rw [h3, h2']
    have h5 := mul_left_cancel (mul_right_cancel h4)
    rw [hrx] at h5
    exact h5.symm
  refine ⟨(lam a s' * μ⁻¹)⁻¹, fun w => ?_⟩
  have h6 := Multiplicative.ofAdd.injective
    (twShortRoot_injective n hirr a s' ((h.short a s' w).symm.trans (hAfix w)))
  calc L w = (lam a s' * μ⁻¹)⁻¹ • ((lam a s' * μ⁻¹) • L w) := by
        rw [smul_smul, inv_mul_cancel₀ hχ0, one_smul]
    _ = (lam a s' * μ⁻¹)⁻¹ • w := by rw [h6]


theorem toralNormal_minus (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hq : 5 ≤ Nat.card F) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 5 ≤ n)
    {X : Type} [Group X] (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ : Fin (n - 1)} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool) (k : spinGroup (quadMinus n F b c))
    (H1 : ∀ c' : F, σ (θ (k * (minusFrame n b c).longRoot h01 s₀ t₀ (.ofAdd c') * k⁻¹)) =
      θ (k * (minusFrame n b c).longRoot h01 s₀ t₀ (.ofAdd c') * k⁻¹))
    (H1' : ∀ c' : F, σ (θ (k * (minusFrame n b c).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c') *
        k⁻¹)) = θ (k * (minusFrame n b c).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c') * k⁻¹))
    (H2 : ∀ (i j : Fin (n - 1)) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ →
      ∀ (t : Bool) (u : Fˣ), σ (θ (k * (minusFrame n b c).longTorus hij true t u * k⁻¹)) =
        θ (k * (minusFrame n b c).longTorus hij true t u * k⁻¹)) :
    (∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0)) ∨
    ((∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          (∑ i, (γ i : ZMod 2) * v i = 0 ∧
            ¬ ∃ (i : Fin (n - 1)) (s : Bool), toStdB (n - 1) γ = Pi.single i (boolSign s)))) ∧
      ¬ ∃ (a : Fin (n - 1)) (s : Bool), a ≠ i₀ ∧ a ≠ i₁ ∧ ∀ w : Fin 2 → F,
        σ (θ (k * twShortRoot n hirr a s (.ofAdd w) * k⁻¹)) =
          θ (k * twShortRoot n hirr a s (.ofAdd w) * k⁻¹)) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  have hn4 : 4 ≤ n := by omega
  obtain ⟨hZ, hcent⟩ := minus_center_facts hirr hp2 hn4
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_minus hp2 hn4 hf hF hirr θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadMinus n F b c)) := isPerfect_spinGroup_quadMinus hn4 hirr
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadMinus n F b c) →* _).comp
      (α : spinGroup (quadMinus n F b c) →* _)) (MonoidHom.id (spinGroup (quadMinus n F b c)))
      (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hcen : ∀ y, σ (θ y) = θ y →
      α y * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c)) :=
    fun y hy => hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hy, mul_inv_cancel])
  obtain ⟨u, hu1, hu2⟩ := exists_unit_ne_one_ne_neg_one hq
  obtain ⟨κ, lam, hφ, hprod, hg₂, hCpres, hdiag, r, hκ, hr⟩ := exists_diag_form_compl
    (minusFrame n b c).toHypFrame h01 s₀ t₀ (by omega) h2 hp2 (minus_hker2 hirr) hZ hcent hu1 hu2
    hα hα2 k (fun c' => hcen _ (H1 c')) (fun c' => hcen _ (H1' c'))
    (fun i j hij hi0 hi1 hj0 hj1 t => hcen _ (H2 i j hij hi0 hi1 hj0 hj1 t u))
  obtain ⟨L, hLw, hLN⟩ := exists_planeMap (g.conjSpin κ) hφ hCpres
  set A := conjTwist α κ with hAdef
  have hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹ := fun y => by
    rw [hAdef, conjTwist_apply]
    group
  have hα₂c : IsConj A (g.conjSpin κ) := hα.conjSpin κ
  have hact : MinusAct hirr A lam (g.μ : F) L :=
    { ne_zero := g.μ.ne_zero
      involutive := conjTwist_sq α hα2 κ
      prod := hprod
      norm := hLN
      long := fun i j hij s t c' => by
        have h1 := hdiag i j hij s t c'
        rw [hA] at h1
        rw [mul_left_cancel (mul_right_cancel h1)]
        congr 2
        ring
      short := fun i s w => IsConj.twShortRoot_eq hirr hp2 (minus_hker2 hirr) hα₂c lam hg₂ L hLw
        i s w }
  by_cases hS : ∃ ρ : F, ∀ w, L w = ρ • w
  · obtain ⟨ρ, hρ⟩ := hS
    obtain ⟨v, hv⟩ := minus_scalar h2 hZ θ hker σ α A κ hαθ hA hact ρ hρ
    exact Or.inl ⟨κ, v, fun γ hγ => hv γ hγ⟩
  · obtain ⟨v, hv⟩ := minus_nonscalar h2 hZ θ hker σ α A κ hαθ hA hact i₀ hS
    refine Or.inr ⟨⟨κ, v, fun γ hγ => hv γ hγ⟩, ?_⟩
    rintro ⟨a, s', ha0, ha1, hfix⟩
    exact hS (minus_short_fixed_scalar hZ θ hker σ α A k κ r hαθ hA hκ h01 s₀ t₀ hr hact a s' ha0
      ha1 hfix)

theorem toralNormal_minus_of_short (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hq : 5 ≤ Nat.card F) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 5 ≤ n)
    {X : Type} [Group X] (θ : spinGroup (quadMinus n F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ : Fin (n - 1)} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool) (k : spinGroup (quadMinus n F b c))
    (H1 : ∀ c' : F, σ (θ (k * (minusFrame n b c).longRoot h01 s₀ t₀ (.ofAdd c') * k⁻¹)) =
      θ (k * (minusFrame n b c).longRoot h01 s₀ t₀ (.ofAdd c') * k⁻¹))
    (H1' : ∀ c' : F, σ (θ (k * (minusFrame n b c).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c') *
        k⁻¹)) = θ (k * (minusFrame n b c).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c') * k⁻¹))
    (H2 : ∀ (i j : Fin (n - 1)) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ →
      ∀ (t : Bool) (u : Fˣ), σ (θ (k * (minusFrame n b c).longTorus hij true t u * k⁻¹)) =
        θ (k * (minusFrame n b c).longTorus hij true t u * k⁻¹))
    (a : Fin (n - 1)) (s : Bool) (ha0 : a ≠ i₀) (ha1 : a ≠ i₁)
    (H3 : ∀ w : Fin 2 → F, σ (θ (k * twShortRoot n hirr a s (.ofAdd w) * k⁻¹)) =
      θ (k * twShortRoot n hirr a s (.ofAdd w) * k⁻¹)) :
    ∃ (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2),
      ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
        ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  rcases toralNormal_minus hp2 hf hF hq hirr hn θ hker σ hσ2 hσr h01 s₀ t₀ k H1 H1' H2 with
    h | ⟨-, h⟩
  · exact h
  · exact absurd ⟨a, s, ha0, ha1, H3⟩ h

end Main

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
