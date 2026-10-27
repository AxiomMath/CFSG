module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.LAData
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8TwelveAux0b

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8.CoreAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

theorem vec_coeff_eq_zero {L : Type} [Field L] [IsAlgClosed L] {N : ℕ} (hN : 2 ≤ N)
    (hNL : (N : L) = 0) {ε : L} (hε : ε ≠ 0) {M : Type*} [AddCommGroup M] [Module L M]
    {ι : Type} [Fintype ι] (w : ι → M) (e : ι → ℕ) (he : Function.Injective e)
    (hlt : ∀ i, e i < N) (h : ∀ x : L, x ^ N = ε * x → ∑ i, x ^ e i • w i = 0) :
    ∀ i, w i = 0 := by
  intro i
  by_contra hw
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero L hw
  apply hf
  refine sum_coeff_eq_zero hN hNL hε (fun j => f (w j)) e he hlt (fun x hx => ?_) i
  have := congrArg f (h x hx)
  simpa [map_sum, map_smul, smul_eq_mul, mul_comm] using this

section Ops

variable {L : Type} [Field L]

@[expose] def eOp (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) :
    ((Fin Tag.E8.rank → ℤ) → L) →ₗ[L] ((Fin Tag.E8.rank → ℤ) → L) where
  toFun v ν := (a γ (ν - γ) : L) * v (ν - γ)
  map_add' v v' := by
    funext ν
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    funext ν
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem eOp_apply (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (v : (Fin Tag.E8.rank → ℤ) → L) (ν : Fin Tag.E8.rank → ℤ) :
    eOp a γ v ν = (a γ (ν - γ) : L) * v (ν - γ) :=
  rfl

theorem actFun_eq (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (t : L) (v : (Fin Tag.E8.rank → ℤ) → L) :
    actFun a γ t v = v + t • eOp a γ v := by
  funext ν
  simp only [actFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eOp_apply]
  ring

theorem eOp_single (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ μ : Fin Tag.E8.rank → ℤ) (c : L) :
    eOp a γ (Pi.single μ c : (Fin Tag.E8.rank → ℤ) → L) = Pi.single (μ + γ) ((a γ μ : L) * c) := by
  funext ν
  rw [eOp_apply]
  by_cases h : ν - γ = μ
  · have h' : ν = μ + γ := sub_eq_iff_eq_add.1 h
    subst h'
    rw [h]
    simp
  · have h' : ν ≠ μ + γ := fun e => h (sub_eq_iff_eq_add.2 e)
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    simp

@[expose] def ex8 (q Q : ℕ) : Fin 8 → ℕ := ![0, 1, q, 1 + q, Q, 1 + Q, q + Q, 1 + q + Q]

theorem ex8_injective {q Q : ℕ} (hq : 2 ≤ q) (hQ : 2 * q ≤ Q) : Function.Injective (ex8 q Q) := by
  refine StrictMono.injective (Fin.strictMono_iff_lt_succ.2 fun i => ?_)
  fin_cases i <;> simp [ex8] <;> omega

theorem ex8_lt {q Q N : ℕ} (hq : 2 ≤ q) (hQ : 2 * q ≤ Q) (hN : 2 * Q ≤ N) (i : Fin 8) :
    ex8 q Q i < N := by
  fin_cases i <;> simp [ex8] <;> omega

theorem triple_expand (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ₀ γ₁ γ₂ : Fin Tag.E8.rank → ℤ) (q : ℕ) (s₁ s₂ x : L) (z : (Fin Tag.E8.rank → ℤ) → L) :
    actFun a γ₀ x (actFun a γ₁ (s₁ * x ^ q) (actFun a γ₂ (s₂ * x ^ (q ^ 2)) z)) =
      ∑ i, x ^ ex8 q (q ^ 2) i •
        ![z, eOp a γ₀ z, s₁ • eOp a γ₁ z, s₁ • eOp a γ₀ (eOp a γ₁ z), s₂ • eOp a γ₂ z,
          s₂ • eOp a γ₀ (eOp a γ₂ z), (s₁ * s₂) • eOp a γ₁ (eOp a γ₂ z),
          (s₁ * s₂) • eOp a γ₀ (eOp a γ₁ (eOp a γ₂ z))] i := by
  simp only [actFun_eq, map_add, map_smul, Fin.sum_univ_eight, ex8]
  funext ν
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, pow_add, pow_zero, pow_one]
  ring

theorem triple_extract [IsAlgClosed L] (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    {q : ℕ} (hq : 2 ≤ q) (hqL : (q : L) = 0) (Z : Submodule L ((Fin Tag.E8.rank → ℤ) → L))
    (γ₀ γ₁ γ₂ : Fin Tag.E8.rank → ℤ) {s₁ s₂ ε : L} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0) (hε : ε ≠ 0)
    (hT : ∀ x : L, x ^ (q ^ 3) = ε * x → ∀ z ∈ Z,
      actFun a γ₀ x (actFun a γ₁ (s₁ * x ^ q) (actFun a γ₂ (s₂ * x ^ (q ^ 2)) z)) ∈ Z) :
    ∀ z ∈ Z, eOp a γ₀ z ∈ Z ∧ eOp a γ₁ z ∈ Z ∧ eOp a γ₂ z ∈ Z := by
  intro z hz
  have hQ : 2 * q ≤ q ^ 2 := by nlinarith
  have hN : 2 * q ^ 2 ≤ q ^ 3 := by nlinarith
  have hN2 : 2 ≤ q ^ 3 := by nlinarith
  have hNL : ((q ^ 3 : ℕ) : L) = 0 := by push_cast; rw [hqL]; ring
  have key := vec_coeff_eq_zero hN2 hNL hε (fun i => Z.mkQ (![z, eOp a γ₀ z, s₁ • eOp a γ₁ z,
      s₁ • eOp a γ₀ (eOp a γ₁ z), s₂ • eOp a γ₂ z, s₂ • eOp a γ₀ (eOp a γ₂ z),
      (s₁ * s₂) • eOp a γ₁ (eOp a γ₂ z), (s₁ * s₂) • eOp a γ₀ (eOp a γ₁ (eOp a γ₂ z))] i))
    (ex8 q (q ^ 2)) (ex8_injective hq hQ) (ex8_lt hq hQ hN) (fun x hx => by
      have h0 : Z.mkQ (actFun a γ₀ x (actFun a γ₁ (s₁ * x ^ q)
          (actFun a γ₂ (s₂ * x ^ (q ^ 2)) z))) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hT x hx z hz
      rw [triple_expand, map_sum] at h0
      simpa only [map_smul] using h0)
  have k1 := key 1
  have k2 := key 2
  have k4 := key 4
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Matrix.cons_val_one,
    Matrix.cons_val] at k1 k2 k4
  exact ⟨k1, (Z.smul_mem_iff hs₁).1 k2, (Z.smul_mem_iff hs₂).1 k4⟩

theorem single_extract [IsAlgClosed L] (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    {q : ℕ} (hq : 2 ≤ q) (hqL : (q : L) = 0) (Z : Submodule L ((Fin Tag.E8.rank → ℤ) → L))
    (γ : Fin Tag.E8.rank → ℤ) {ε : L} (hε : ε ≠ 0)
    (hS : ∀ x : L, x ^ q = ε * x → ∀ z ∈ Z, actFun a γ x z ∈ Z) :
    ∀ z ∈ Z, eOp a γ z ∈ Z := by
  intro z hz
  have key := vec_coeff_eq_zero hq hqL hε (fun i => Z.mkQ (![z, eOp a γ z] i)) ![0, 1]
    (by decide) (fun i => by fin_cases i <;> simp <;> omega) (fun x hx => by
      have h0 : Z.mkQ (actFun a γ x z) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hS x hx z hz
      rw [actFun_eq, map_add, map_smul] at h0
      rw [Fin.sum_univ_two]
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, pow_one, one_smul] using h0)
  have k1 := key 1
  simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero] using k1

end Ops

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8.CoreAux
