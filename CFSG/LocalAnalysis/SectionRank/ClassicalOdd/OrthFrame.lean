module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.SectionRank.ClassicalOdd

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

structure OrthData (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] where
  X : Fin 3 → ι
  Y : Fin 3 → ι
  w : ι → K
  β : (ι → K) →ₗ[K] K
  injX : Function.Injective X
  injY : Function.Injective Y
  X_ne_Y : ∀ i j, X i ≠ Y j
  w_X : ∀ i, w (X i) = 0
  w_Y : ∀ i, w (Y i) = 0
  β_X : ∀ i, β (Pi.single (X i) 1) = 0
  β_Y : ∀ i, β (Pi.single (Y i) 1) = 0
  β_w : β w = 2

namespace OrthData

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (D : OrthData ι K)

theorem Y_ne_X (i j : Fin 3) : D.Y j ≠ D.X i := (D.X_ne_Y i j).symm

@[expose] def corr (x : K × K × K × K) (v : ι → K) : ι → K :=
  Pi.single (D.X 0)
      (x.2.1 * v (D.Y 1) + x.2.2.1 * v (D.Y 2) - x.1 * D.β v - x.1 ^ 2 * v (D.Y 0)) +
    Pi.single (D.X 1) (-(x.2.1 * v (D.Y 0)) + x.2.2.2 * v (D.Y 2)) +
    Pi.single (D.X 2) (-(x.2.2.1 * v (D.Y 0)) - x.2.2.2 * v (D.Y 1)) +
    (x.1 * v (D.Y 0)) • D.w

theorem corr_add (x : K × K × K × K) (v v' : ι → K) :
    D.corr x (v + v') = D.corr x v + D.corr x v' := by
  ext k
  simp only [corr, Pi.add_apply, Pi.smul_apply, map_add, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring

theorem corr_smul (x : K × K × K × K) (r : K) (v : ι → K) :
    D.corr x (r • v) = r • D.corr x v := by
  ext k
  simp only [corr, Pi.add_apply, Pi.smul_apply, map_smul, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring

@[expose] def L (x : K × K × K × K) : (ι → K) →ₗ[K] (ι → K) where
  toFun v := v + D.corr x v
  map_add' v v' := by
    rw [D.corr_add]
    abel
  map_smul' r v := by
    rw [D.corr_smul, RingHom.id_apply, smul_add]

theorem L_apply (x : K × K × K × K) (v : ι → K) : D.L x v = v + D.corr x v := rfl

theorem β_single_X (i : Fin 3) (c : K) : D.β (Pi.single (D.X i) c) = 0 := by
  rw [show Pi.single (D.X i) c = c • Pi.single (D.X i) (1 : K) by
    ext k
    simp [Pi.single_apply], map_smul, D.β_X, smul_zero]

theorem corr_Y (x : K × K × K × K) (v : ι → K) (j : Fin 3) : D.corr x v (D.Y j) = 0 := by
  simp [corr, D.Y_ne_X, D.w_Y]

theorem β_corr (x : K × K × K × K) (v : ι → K) :
    D.β (D.corr x v) = 2 * (x.1 * v (D.Y 0)) := by
  simp only [corr, map_add, map_smul, β_single_X, D.β_w, smul_eq_mul]
  ring

theorem L_Y (x : K × K × K × K) (v : ι → K) (j : Fin 3) : D.L x v (D.Y j) = v (D.Y j) := by
  rw [L_apply, Pi.add_apply, corr_Y, add_zero]

theorem β_L (x : K × K × K × K) (v : ι → K) :
    D.β (D.L x v) = D.β v + 2 * (x.1 * v (D.Y 0)) := by
  rw [L_apply, map_add, β_corr]

theorem L_comp (x x' : K × K × K × K) : (D.L x).comp (D.L x') = D.L (x + x') := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, L_apply, L_apply, L_apply, D.corr_add]
  have h : D.corr x (D.corr x' v) =
      Pi.single (D.X 0) (-(x.1 * (2 * (x'.1 * v (D.Y 0))))) := by
    rw [corr, corr_Y, corr_Y, corr_Y, β_corr]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> ring
  rw [h]
  ext k
  simp only [corr, Pi.add_apply, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  split_ifs <;> ring

theorem L_zero : D.L 0 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [L_apply, LinearMap.id_apply, add_eq_left]
  ext k
  simp [corr]

theorem Q_L (Q : (ι → K) → K)
    (hQX : ∀ v i a, Q (v + Pi.single (D.X i) a) = Q v + a * v (D.Y i))
    (hQw : ∀ v s, Q (v + s • D.w) = Q v + s * D.β v + s ^ 2) (x : K × K × K × K)
    (v : ι → K) : Q (D.L x v) = Q v := by
  have hY : ∀ (u : ι → K) (i j : Fin 3) (a : K),
      (u + Pi.single (D.X i) a : ι → K) (D.Y j) = u (D.Y j) :=
    fun u i j a => by simp [D.Y_ne_X]
  have hYw : ∀ (s : K) (j : Fin 3), (v + s • D.w) (D.Y j) = v (D.Y j) := fun s j => by
    simp [D.w_Y]
  rw [L_apply, corr]
  set s := x.1 * v (D.Y 0)
  set a₀ := x.2.1 * v (D.Y 1) + x.2.2.1 * v (D.Y 2) - x.1 * D.β v - x.1 ^ 2 * v (D.Y 0)
  set a₁ := -(x.2.1 * v (D.Y 0)) + x.2.2.2 * v (D.Y 2)
  set a₂ := -(x.2.2.1 * v (D.Y 0)) - x.2.2.2 * v (D.Y 1)
  rw [show v + (Pi.single (D.X 0) a₀ + Pi.single (D.X 1) a₁ + Pi.single (D.X 2) a₂ + s • D.w) =
      v + s • D.w + Pi.single (D.X 0) a₀ + Pi.single (D.X 1) a₁ + Pi.single (D.X 2) a₂ by abel,
    hQX, hQX, hQX, hQw, hY, hY, hY, hYw, hYw, hYw]
  ring

@[expose] def dsign (i : Fin 3) (k : ι) : K := if k = D.X i ∨ k = D.Y i then -1 else 1

@[expose] def dL (i : Fin 3) : (ι → K) →ₗ[K] (ι → K) where
  toFun v k := D.dsign i k * v k
  map_add' v v' := by
    ext k
    simp [mul_add]
  map_smul' r v := by
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem dL_apply (i : Fin 3) (v : ι → K) (k : ι) : D.dL i v k = D.dsign i k * v k := rfl

theorem dsign_mul_self (i : Fin 3) (k : ι) : D.dsign i k * D.dsign i k = 1 := by
  rw [dsign]
  split_ifs <;> norm_num

theorem dL_dL (i : Fin 3) : (D.dL i).comp (D.dL i) = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  ext k
  rw [LinearMap.comp_apply, dL_apply, dL_apply, ← mul_assoc, dsign_mul_self, one_mul,
    LinearMap.id_apply]

theorem dsign_X (i j : Fin 3) : D.dsign i (D.X j) = if j = i then -1 else 1 := by
  simp [dsign, D.injX.eq_iff, D.X_ne_Y]

theorem dsign_Y (i j : Fin 3) : D.dsign i (D.Y j) = if j = i then -1 else 1 := by
  simp [dsign, D.injY.eq_iff, D.Y_ne_X]

theorem dL_single_X (i j : Fin 3) (c : K) :
    D.dL i (Pi.single (D.X j) c) = Pi.single (D.X j) (D.dsign i (D.X j) * c) := by
  ext k
  rw [dL_apply, Pi.single_apply, Pi.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

theorem dL_w (i : Fin 3) : D.dL i D.w = D.w := by
  ext k
  rw [dL_apply, dsign]
  split_ifs with h
  · rcases h with h | h <;> simp [h, D.w_X, D.w_Y]
  · rw [one_mul]

theorem β_dL (i : Fin 3) (v : ι → K) : D.β (D.dL i v) = D.β v := by
  have h : D.dL i v = v + (-2 * v (D.X i)) • Pi.single (D.X i) 1 +
      (-2 * v (D.Y i)) • Pi.single (D.Y i) 1 := by
    ext k
    rw [dL_apply, dsign]
    by_cases hX : k = D.X i
    · subst hX
      simp [D.X_ne_Y]
      ring
    · by_cases hY : k = D.Y i
      · subst hY
        simp [D.Y_ne_X]
        ring
      · simp [hX, hY]
  rw [h, map_add, map_add, map_smul, map_smul, D.β_X, D.β_Y, smul_zero, smul_zero, add_zero,
    add_zero]

theorem conj₀ (x : K × K × K × K) :
    (D.dL 0).comp ((D.L x).comp (D.dL 0)) = D.L (-x.1, -x.2.1, -x.2.2.1, x.2.2.2) := by
  refine LinearMap.ext fun v => ?_
  have hv : D.dL 0 (D.dL 0 v) = v := LinearMap.congr_fun (D.dL_dL 0) v
  have h10 : ((1 : Fin 3) = 0) = False := by decide
  have h20 : ((2 : Fin 3) = 0) = False := by decide
  simp only [LinearMap.comp_apply, L_apply, map_add, hv, corr, map_smul, dL_single_X, dL_w,
    dsign_X, dL_apply, dsign_Y, β_dL, h10, h20, ↓reduceIte]
  congr 1
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring

theorem conj₁ (x : K × K × K × K) :
    (D.dL 1).comp ((D.L x).comp (D.dL 1)) = D.L (x.1, -x.2.1, x.2.2.1, -x.2.2.2) := by
  refine LinearMap.ext fun v => ?_
  have hv : D.dL 1 (D.dL 1 v) = v := LinearMap.congr_fun (D.dL_dL 1) v
  have h01 : ((0 : Fin 3) = 1) = False := by decide
  have h21 : ((2 : Fin 3) = 1) = False := by decide
  simp only [LinearMap.comp_apply, L_apply, map_add, hv, corr, map_smul, dL_single_X, dL_w,
    dsign_X, dL_apply, dsign_Y, β_dL, h01, h21, ↓reduceIte]
  congr 1
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring

@[expose] noncomputable def hom : Multiplicative (K × K × K × K) →* GL ι K :=
  glOfAdd (fun x => LinearMap.toMatrix' (D.L x)) (by rw [D.L_zero, LinearMap.toMatrix'_id])
    (fun x x' => by rw [← LinearMap.toMatrix'_comp, D.L_comp])

@[expose] noncomputable def dGL (i : Fin 3) : GL ι K :=
  ⟨LinearMap.toMatrix' (D.dL i), LinearMap.toMatrix' (D.dL i),
    by rw [← LinearMap.toMatrix'_comp, D.dL_dL, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, D.dL_dL, LinearMap.toMatrix'_id]⟩

theorem hom_mulVec (x : Multiplicative (K × K × K × K)) (v : ι → K) :
    (D.hom x : Matrix ι ι K) *ᵥ v = D.L x.toAdd v := by
  rw [hom, coe_glOfAdd, LinearMap.toMatrix'_mulVec]

theorem commutator_dGL (i : Fin 3) (x y : K × K × K × K)
    (hc : (D.dL i).comp ((D.L x).comp (D.dL i)) = D.L y) :
    ⁅D.dGL i, D.hom (Multiplicative.ofAdd x)⁆ = D.hom (Multiplicative.ofAdd (y + -x)) := by
  rw [commutatorElement_def, ← map_inv]
  apply Units.ext
  simp only [Units.val_mul, hom, coe_glOfAdd, dGL, Units.inv_mk, toAdd_ofAdd, toAdd_inv]
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp,
    ← D.L_comp, ← hc]
  rfl

theorem hom_mem_omega (Q : (ι → K) → K)
    (hQX : ∀ v i a, Q (v + Pi.single (D.X i) a) = Q v + a * v (D.Y i))
    (hQw : ∀ v s, Q (v + s • D.w) = Q v + s * D.β v + s ^ 2)
    (hQd : ∀ i v, Q (D.dL i v) = Q v) (h2 : (2 : K) ≠ 0) (x : Multiplicative (K × K × K × K)) :
    D.hom x ∈ StatedOmega Q := by
  set O := Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
  have hO : ∀ y, D.hom y ∈ O := fun y => Subgroup.subset_closure fun v => by
    rw [hom_mulVec, D.Q_L Q hQX hQw]
  have hd : ∀ i, D.dGL i ∈ O := fun i => Subgroup.subset_closure fun v => by
    change Q (LinearMap.toMatrix' (D.dL i) *ᵥ v) = Q v
    rw [LinearMap.toMatrix'_mulVec, hQd]
  have : NeZero (2 : K) := ⟨h2⟩
  obtain ⟨⟨t, b₀, b₁, b₂⟩, rfl⟩ : ∃ y, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  have hsplit : Multiplicative.ofAdd (t, b₀, b₁, b₂) =
      Multiplicative.ofAdd (t, b₀, b₁, (0 : K)) *
        Multiplicative.ofAdd ((0 : K), (0 : K), (0 : K), b₂) := by
    rw [← ofAdd_add]
    simp
  have h₀ : D.hom (Multiplicative.ofAdd (t, b₀, b₁, 0)) =
      ⁅D.dGL 0, D.hom (Multiplicative.ofAdd (-t / 2, -b₀ / 2, -b₁ / 2, 0))⁆ := by
    rw [D.commutator_dGL 0 _ _ (D.conj₀ _)]
    congr 2
    simp [neg_div, add_halves]
  have h₁ : D.hom (Multiplicative.ofAdd (0, 0, 0, b₂)) =
      ⁅D.dGL 1, D.hom (Multiplicative.ofAdd (0, 0, 0, -b₂ / 2))⁆ := by
    rw [D.commutator_dGL 1 _ _ (D.conj₁ _)]
    congr 2
    simp [neg_div, add_halves]
  change _ ∈ ⁅O, O⁆
  rw [hsplit, map_mul, h₀, h₁]
  exact mul_mem (Subgroup.commutator_mem_commutator (hd 0) (hO _))
    (Subgroup.commutator_mem_commutator (hd 1) (hO _))

theorem hom_fix (x : Multiplicative (K × K × K × K)) :
    (D.hom x : Matrix ι ι K) *ᵥ Pi.single (D.X 0) 1 = Pi.single (D.X 0) 1 := by
  rw [hom_mulVec, L_apply, add_eq_left]
  ext k
  simp [corr, D.Y_ne_X, D.β_X]

theorem L_injective (h2 : (2 : K) ≠ 0) : Function.Injective D.L := by
  intro x x' h
  have hv : ∀ v, D.L x v = D.L x' v := fun v => LinearMap.congr_fun h v
  have e₁ := congrFun (hv (Pi.single (D.Y 1) 1)) (D.X 0)
  have e₂ := congrFun (hv (Pi.single (D.Y 2) 1)) (D.X 0)
  have e₃ := congrFun (hv (Pi.single (D.Y 2) 1)) (D.X 1)
  have e₄ := congrArg D.β (hv (Pi.single (D.Y 0) 1))
  rw [β_L, β_L] at e₄
  simp [L_apply, corr, D.injX.eq_iff, D.injY.eq_iff, D.X_ne_Y, D.β_Y] at e₁ e₂ e₃ e₄
  exact Prod.ext (e₄.resolve_right h2) (Prod.ext e₁ (Prod.ext e₂ e₃))

theorem hom_injective (h2 : (2 : K) ≠ 0) : Function.Injective D.hom :=
  glOfAdd_injective fun _ _ h => D.L_injective h2 (LinearMap.toMatrix'.injective h)

theorem four_mul_le_pRank [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (Q : (ι → K) → K)
    (hQX : ∀ v i a, Q (v + Pi.single (D.X i) a) = Q v + a * v (D.Y i))
    (hQw : ∀ v s, Q (v + s • D.w) = Q v + s * D.β v + s ^ 2)
    (hQd : ∀ i v, Q (D.dL i v) = Q v) :
    4 * f ≤ pRank p (⊤ : Subgroup (StatedProj (StatedOmega Q))) := by
  have := charP_of_card hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  refine le_pRank_statedProj (Fact.out : p.Prime).one_lt multiplicative_comm
    (pow_char_eq_one (K := K)) ?_ D.hom (D.hom_injective h2) (D.hom_mem_omega Q hQX hQw hQd h2)
    (v := Pi.single (D.X 0) 1) (by simp) D.hom_fix
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_prod, hK,
    ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

end OrthData

end CFSG.SectionRank.ClassicalOdd
