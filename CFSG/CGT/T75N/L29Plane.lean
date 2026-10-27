module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] {m : ℕ} {V : Type} [CommGroup V]

structure EqBij (σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V)
    (Φ : V → (Fin (m + 2) → F)) : Prop where
  equivariant : ∀ (g : SpecialLinearGroup (Fin (m + 2)) F) (v : V),
    Φ (σ g v) = (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Φ v
  bijective : Function.Bijective Φ
  map_one : Φ 1 = 0

theorem X_mulVec {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : F) (x : Fin n → F) :
    ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) *ᵥ x = x + Pi.single i (c * x j) :=
  transvection_mulVec c x

theorem single_eq_zero_iff {n : ℕ} (i : Fin n) (c : F) : (Pi.single i c : Fin n → F) = 0 ↔ c = 0 :=
  ⟨fun h => by simpa using congrFun h i, fun h => by rw [h]; exact Pi.single_zero i⟩

theorem coord_zero_of_fix_one {n : ℕ} {i : Fin n} {x : Fin n → F}
    (h : ∀ g : SpecialLinearGroup (Fin n) F,
      (g : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single i 1 : Fin n → F) = Pi.single i 1 →
        (g : Matrix (Fin n) (Fin n) F) *ᵥ x = x) :
    ∀ k, k ≠ i → x k = 0 := by
  intro k hk
  have hik : i ≠ k := Ne.symm hk
  have h1 := h (SpecialLinearGroup.transvection hik 1) (by
    rw [X_mulVec]
    simp [hk])
  rw [X_mulVec, add_eq_left, single_eq_zero_iff, one_mul] at h1
  exact h1

theorem coord_zero_of_fix_two {n : ℕ} {i j : Fin n} {x : Fin n → F}
    (h : ∀ g : SpecialLinearGroup (Fin n) F,
      (g : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single i 1 : Fin n → F) = Pi.single i 1 →
      (g : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single j 1 : Fin n → F) = Pi.single j 1 →
        (g : Matrix (Fin n) (Fin n) F) *ᵥ x = x) :
    ∀ k, k ≠ i → k ≠ j → x k = 0 := by
  intro k hki hkj
  have hik : i ≠ k := Ne.symm hki
  have h1 := h (SpecialLinearGroup.transvection hik 1) (by
    rw [X_mulVec]
    simp [hki]) (by
    rw [X_mulVec]
    simp [hkj])
  rw [X_mulVec, add_eq_left, single_eq_zero_iff, one_mul] at h1
  exact h1

section Bij

variable {σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V} {Φ : V → (Fin (m + 2) → F)}

theorem fix_of_line (h : EqBij σ Φ) {j : Fin (m + 2)} {v : V} (hv : ∀ k, k ≠ j → Φ v k = 0)
    {g : SpecialLinearGroup (Fin (m + 2)) F}
    (hg : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single j 1 : Fin (m + 2) → F) =
      Pi.single j 1) : σ g v = v := by
  apply h.bijective.1
  rw [h.equivariant]
  have hΦ : Φ v = Φ v j • (Pi.single j 1 : Fin (m + 2) → F) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk, hv k hk]
  rw [hΦ, mulVec_smul, hg]

theorem fix_of_plane (h : EqBij σ Φ) {i j : Fin (m + 2)} {v : V}
    (hv : ∀ k, k ≠ i → k ≠ j → Φ v k = 0) {g : SpecialLinearGroup (Fin (m + 2)) F}
    (hgi : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single i 1 : Fin (m + 2) → F) =
      Pi.single i 1)
    (hgj : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single j 1 : Fin (m + 2) → F) =
      Pi.single j 1) : σ g v = v := by
  apply h.bijective.1
  rw [h.equivariant]
  by_cases hij : i = j
  · subst hij
    have hΦ : Φ v = Φ v i • (Pi.single i 1 : Fin (m + 2) → F) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk, hv k hk hk]
    rw [hΦ, mulVec_smul, hgi]
  · have hΦ : Φ v = Φ v i • (Pi.single i 1 : Fin (m + 2) → F) +
        Φ v j • (Pi.single j 1 : Fin (m + 2) → F) := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [Ne.symm hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hij]
        · simp [hki, hkj, hv k hki hkj]
    rw [hΦ, mulVec_add, mulVec_smul, mulVec_smul, hgi, hgj]

theorem line_of_fixed (h : EqBij σ Φ) {j : Fin (m + 2)} {v : V}
    (hv : ∀ g : SpecialLinearGroup (Fin (m + 2)) F,
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single j 1 : Fin (m + 2) → F) =
        Pi.single j 1 → σ g v = v) : ∀ k, k ≠ j → Φ v k = 0 :=
  coord_zero_of_fix_one fun g hg => by
    rw [← h.equivariant, hv g hg]

theorem plane_of_fixed (h : EqBij σ Φ) {i j : Fin (m + 2)} {v : V}
    (hv : ∀ g : SpecialLinearGroup (Fin (m + 2)) F,
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single i 1 : Fin (m + 2) → F) =
        Pi.single i 1 →
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single j 1 : Fin (m + 2) → F) =
        Pi.single j 1 → σ g v = v) : ∀ k, k ≠ i → k ≠ j → Φ v k = 0 :=
  coord_zero_of_fix_two fun g hgi hgj => by
    rw [← h.equivariant, hv g hgi hgj]

theorem line_mul (h : EqBij σ Φ) {j : Fin (m + 2)} {v w : V} (hv : ∀ k, k ≠ j → Φ v k = 0)
    (hw : ∀ k, k ≠ j → Φ w k = 0) : ∀ k, k ≠ j → Φ (v * w) k = 0 :=
  line_of_fixed h fun g hg => by
    rw [map_mul, fix_of_line h hv hg, fix_of_line h hw hg]

end Bij

@[expose] noncomputable def X01 (m : ℕ) (t : F) : SpecialLinearGroup (Fin (m + 2)) F :=
  SpecialLinearGroup.transvection (Fin.zero_ne_one : (0 : Fin (m + 2)) ≠ 1) t

@[expose] noncomputable def Y10 (m : ℕ) (t : F) : SpecialLinearGroup (Fin (m + 2)) F :=
  SpecialLinearGroup.transvection (Fin.zero_ne_one.symm : (1 : Fin (m + 2)) ≠ 0) t

theorem X01_mulVec (m : ℕ) (t : F) (x : Fin (m + 2) → F) :
    ((X01 m t : SpecialLinearGroup (Fin (m + 2)) F) : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ x =
      x + Pi.single 0 (t * x 1) :=
  X_mulVec _ t x

theorem Y10_mulVec (m : ℕ) (t : F) (x : Fin (m + 2) → F) :
    ((Y10 m t : SpecialLinearGroup (Fin (m + 2)) F) : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ x =
      x + Pi.single 1 (t * x 0) :=
  X_mulVec _ t x

theorem X01_fix_e0 (m : ℕ) (t : F) : ((X01 m t : SpecialLinearGroup (Fin (m + 2)) F) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) =
      Pi.single 0 1 := by
  rw [X01_mulVec m]
  simp

theorem Y10_fix_e1 (m : ℕ) (t : F) : ((Y10 m t : SpecialLinearGroup (Fin (m + 2)) F) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 1 1 : Fin (m + 2) → F) =
      Pi.single 1 1 := by
  rw [Y10_mulVec m]
  simp

theorem X01_add (m : ℕ) (s t : F) : X01 m (s + t) = X01 m s * X01 m t :=
  SpecialLinearGroup.transvection_add _ s t

theorem W_mulVec (m : ℕ) {a : F} (ha : a ≠ 0) {u : Fin (m + 2) → F} (hu : ∀ k, k ≠ 1 → u k = 0)
    (k : Fin (m + 2)) :
    (((X01 m a * Y10 m (-a⁻¹) * X01 m a : SpecialLinearGroup (Fin (m + 2)) F) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ u) k = if k = 0 then a * u 1 else 0 := by
  have hu0 : u 0 = 0 := hu 0 Fin.zero_ne_one
  have hcancel : a⁻¹ * (a * u 1) = u 1 := inv_mul_cancel_left₀ ha _
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
    ← mulVec_mulVec]
  simp only [X01_mulVec, Y10_mulVec, Pi.add_apply]
  by_cases hk0 : k = 0
  · subst hk0
    simp [hu0, hcancel]
  · by_cases hk1 : k = 1
    · subst hk1
      simp [hu0, hcancel]
    · simp [hk0, hk1, hu k hk1]

@[expose] noncomputable def W1 (m : ℕ) (F : Type) [Field F] : SpecialLinearGroup (Fin (m + 2)) F :=
  X01 m 1 * Y10 m (-1) * X01 m 1

theorem W1_mulVec (hF2 : (2 : F) = 0) {u : Fin (m + 2) → F} (hu : ∀ k, k ≠ 0 → u k = 0) :
    ((W1 m F : SpecialLinearGroup (Fin (m + 2)) F) : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ u =
      u 0 • (Pi.single 1 1 : Fin (m + 2) → F) := by
  have hu1 : u 1 = 0 := hu 1 Fin.zero_ne_one.symm
  have hdbl : ∀ x : F, x + x = 0 := fun x => by rw [← two_mul, hF2, zero_mul]
  have hneg : ∀ x : F, -x = x := fun x => neg_eq_of_add_eq_zero_right (hdbl x)
  rw [W1, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
    ← mulVec_mulVec]
  simp only [X01_mulVec, Y10_mulVec]
  funext k
  by_cases hk0 : k = 0
  · subst hk0
    simp [hu1, hneg, hdbl]
  · by_cases hk1 : k = 1
    · subst hk1
      simp [hu1, hneg]
    · simp [hk0, hk1, hu k hk0]

section Quad

variable {σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V} {Φ : V → (Fin (m + 2) → F)}
  (h : EqBij σ Φ) (hV2 : ∀ v : V, v * v = 1) (hF2 : (2 : F) = 0)
include h hV2 hF2

theorem quad_aux {i j : Fin (m + 2)} (hij : i ≠ j) (t : F) {v : V}
    (hv : ∀ k, k ≠ j → Φ v k = 0) :
    ∀ k, k ≠ i → Φ (σ (SpecialLinearGroup.transvection hij t) v * v⁻¹) k = 0 := by
  set X : SpecialLinearGroup (Fin (m + 2)) F := SpecialLinearGroup.transvection hij t with hX
  set z : V := σ X v * v⁻¹ with hz
  have hΦX : Φ (σ X v) = Φ v + Pi.single i (t * Φ v j) := by
    rw [h.equivariant, hX, X_mulVec]
  have hXX : X * X = 1 := by
    rw [hX, ← SpecialLinearGroup.transvection_add, ← two_mul, hF2, zero_mul,
      SpecialLinearGroup.transvection_coeff_zero]
  have haa : σ X (σ X v) = v := by
    rw [← MulAut.mul_apply, ← map_mul, hXX, map_one, MulAut.one_apply]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (hV2 z)
  have hb : σ X z = z := by
    have h1 : σ X z = z⁻¹ := by
      rw [hz, map_mul, map_inv, haa, _root_.mul_inv_rev, inv_inv]
    rw [h1, hzinv]
  have hc : t * Φ z j = 0 := by
    have h1 : (X : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Φ z = Φ z := by
      rw [← h.equivariant, hb]
    rw [hX, X_mulVec, add_eq_left, single_eq_zero_iff] at h1
    exact h1
  have hd : ∀ k, k ≠ i → k ≠ j → Φ z k = 0 := by
    refine plane_of_fixed h fun g hgi hgj => ?_
    have hw : ∀ k, k ≠ i → k ≠ j → Φ (σ X v) k = 0 := by
      intro k hki hkj
      rw [hΦX]
      simp [hv k hkj, hki]
    rw [hz, map_mul, map_inv, fix_of_line h hv hgj, fix_of_plane h hw hgi hgj]
  intro k hk
  by_cases ht : t = 0
  · have hX1 : X = 1 := by rw [hX, ht, SpecialLinearGroup.transvection_coeff_zero]
    have hz1 : z = 1 := by rw [hz, hX1, map_one, MulAut.one_apply, mul_inv_cancel]
    rw [hz1, h.map_one]
    rfl
  · have hj : Φ z j = 0 := (mul_eq_zero.1 hc).resolve_left ht
    by_cases hkj : k = j
    · rw [hkj]; exact hj
    · exact hd k hk hkj

theorem weyl_aux {a : F} (ha : a ≠ 0) {v : V} (hv : ∀ k, k ≠ 1 → Φ v k = 0) :
    ∀ k, Φ (σ (X01 m a) v * v⁻¹) k = if k = 0 then a * Φ v 1 else 0 := by
  set z₁ : V := σ (X01 m a) v * v⁻¹ with hz₁def
  have hz₁ : ∀ k, k ≠ 0 → Φ z₁ k = 0 :=
    quad_aux h hV2 hF2 (Fin.zero_ne_one : (0 : Fin (m + 2)) ≠ 1) a hv
  have hXv : σ (X01 m a) v = z₁ * v := by rw [hz₁def, inv_mul_cancel_right]
  have hYv : σ (Y10 m (-a⁻¹)) v = v := fix_of_line h hv (Y10_fix_e1 m _)
  set z₂ : V := σ (Y10 m (-a⁻¹)) z₁ * z₁⁻¹ with hz₂def
  have hz₂ : ∀ k, k ≠ 1 → Φ z₂ k = 0 :=
    quad_aux h hV2 hF2 (Fin.zero_ne_one.symm : (1 : Fin (m + 2)) ≠ 0) (-a⁻¹) hz₁
  have hYz₁ : σ (Y10 m (-a⁻¹)) z₁ = z₂ * z₁ := by rw [hz₂def, inv_mul_cancel_right]
  have hXz₁ : σ (X01 m a) z₁ = z₁ := fix_of_line h hz₁ (X01_fix_e0 m _)
  set z₃ : V := σ (X01 m a) z₂ * z₂⁻¹ with hz₃def
  have hz₃ : ∀ k, k ≠ 0 → Φ z₃ k = 0 :=
    quad_aux h hV2 hF2 (Fin.zero_ne_one : (0 : Fin (m + 2)) ≠ 1) a hz₂
  have hXz₂ : σ (X01 m a) z₂ = z₃ * z₂ := by rw [hz₃def, inv_mul_cancel_right]
  have hz₁₁ : z₁ * z₁ = 1 := hV2 z₁
  have hW : σ (X01 m a * Y10 m (-a⁻¹) * X01 m a) v = z₃ * z₂ * v := by
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hXv, map_mul, hYv, hYz₁, map_mul,
      map_mul, hXz₁, hXz₂, hXv]
    calc z₃ * z₂ * z₁ * (z₁ * v) = z₃ * z₂ * (z₁ * z₁) * v := by group
      _ = z₃ * z₂ * v := by rw [hz₁₁, mul_one]
  have hΦW : ∀ k, Φ (σ (X01 m a * Y10 m (-a⁻¹) * X01 m a) v) k =
      if k = 0 then a * Φ v 1 else 0 := by
    intro k
    rw [h.equivariant]
    exact W_mulVec m ha hv k
  have hΦW0 : ∀ k, k ≠ 0 → Φ (σ (X01 m a * Y10 m (-a⁻¹) * X01 m a) v) k = 0 := by
    intro k hk
    rw [hΦW k]
    simp [hk]
  have hfixW : ∀ t : F, σ (X01 m t) (σ (X01 m a * Y10 m (-a⁻¹) * X01 m a) v) =
      σ (X01 m a * Y10 m (-a⁻¹) * X01 m a) v :=
    fun t => fix_of_line h hΦW0 (X01_fix_e0 m t)
  have hu : ∀ t : F, σ (X01 m t) (z₂ * v) = z₂ * v := by
    intro t
    have h1 := hfixW t
    rw [hW, map_mul, map_mul, fix_of_line h hz₃ (X01_fix_e0 m t)] at h1
    have h2 : z₃ * (σ (X01 m t) z₂ * σ (X01 m t) v) = z₃ * (z₂ * v) := by
      rw [← mul_assoc, ← mul_assoc]
      exact h1
    rw [map_mul]
    exact mul_left_cancel h2
  have hΦu : ∀ k, k ≠ 1 → Φ (z₂ * v) k = 0 := line_mul h hz₂ hv
  have hΦu1 : Φ (z₂ * v) 1 = 0 := by
    have h1 : ((X01 m (1 : F) : SpecialLinearGroup (Fin (m + 2)) F) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Φ (z₂ * v) = Φ (z₂ * v) := by
      rw [← h.equivariant, hu 1]
    rw [X01_mulVec, add_eq_left, single_eq_zero_iff, one_mul] at h1
    exact h1
  have hu1 : z₂ * v = 1 := by
    apply h.bijective.1
    rw [h.map_one]
    funext k
    by_cases hk : k = 1
    · rw [hk]; exact hΦu1
    · exact hΦu k hk
  have hz₂v : z₂ = v⁻¹ := eq_inv_of_mul_eq_one_left hu1
  have hz₃z₁ : z₃ = z₁ := by
    rw [hz₃def, hz₂v, map_inv, inv_inv, hz₁def]
    calc (σ (X01 m a) v)⁻¹ * v = (σ (X01 m a) v * v⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
      _ = σ (X01 m a) v * v⁻¹ := inv_eq_of_mul_eq_one_right (hV2 _)
  have hWz : σ (X01 m a * Y10 m (-a⁻¹) * X01 m a) v = z₁ := by
    rw [hW, hz₂v, mul_assoc, inv_mul_cancel, mul_one, hz₃z₁]
  intro k
  rw [← hWz]
  exact hΦW k

end Quad

section Plane

variable {σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V} {Φ : V → (Fin (m + 2) → F)}
  (h : EqBij σ Φ)

noncomputable def EqBij.psi (h : EqBij σ Φ) : (Fin (m + 2) → F) → V :=
  Function.surjInv h.bijective.2

theorem EqBij.phi_psi (x : Fin (m + 2) → F) : Φ (h.psi x) = x :=
  Function.surjInv_eq h.bijective.2 x

theorem EqBij.psi_phi (v : V) : h.psi (Φ v) = v :=
  h.bijective.1 (h.phi_psi _)

theorem EqBij.psi_zero : h.psi 0 = 1 := by
  have h0 : Φ (1 : V) = 0 := EqBij.map_one h
  have := h.psi_phi (1 : V)
  rwa [h0] at this

noncomputable def EqBij.lineA (h : EqBij σ Φ) (c : F) : V :=
  h.psi (c • (Pi.single 0 1 : Fin (m + 2) → F))

noncomputable def EqBij.lineB (h : EqBij σ Φ) (d : F) : V :=
  h.psi (d • (Pi.single 1 1 : Fin (m + 2) → F))

theorem EqBij.phi_lineA (c : F) : Φ (h.lineA c) = c • (Pi.single 0 1 : Fin (m + 2) → F) :=
  h.phi_psi _

theorem EqBij.phi_lineB (d : F) : Φ (h.lineB d) = d • (Pi.single 1 1 : Fin (m + 2) → F) :=
  h.phi_psi _

theorem EqBij.lineA_zero : h.lineA 0 = 1 := by
  rw [EqBij.lineA, zero_smul, h.psi_zero]

theorem EqBij.lineB_zero : h.lineB 0 = 1 := by
  rw [EqBij.lineB, zero_smul, h.psi_zero]

theorem EqBij.lineA_vanish (c : F) : ∀ k, k ≠ 0 → Φ (h.lineA c) k = 0 := fun k hk => by
  rw [h.phi_lineA]
  simp [hk]

theorem EqBij.lineB_vanish (d : F) : ∀ k, k ≠ 1 → Φ (h.lineB d) k = 0 := fun k hk => by
  rw [h.phi_lineB]
  simp [hk]

noncomputable def EqBij.pt (h : EqBij σ Φ) (c d : F) : V :=
  h.psi (c • (Pi.single 0 1 : Fin (m + 2) → F) + d • (Pi.single 1 1 : Fin (m + 2) → F))

theorem EqBij.phi_pt (c d : F) : Φ (h.pt c d) =
    c • (Pi.single 0 1 : Fin (m + 2) → F) + d • (Pi.single 1 1 : Fin (m + 2) → F) :=
  h.phi_psi _

variable (hV2 : ∀ v : V, v * v = 1) (hF2 : (2 : F) = 0)
include hV2 hF2

theorem EqBij.X_lineB (a d : F) : σ (X01 m a) (h.lineB d) = h.lineA (a * d) * h.lineB d := by
  by_cases ha : a = 0
  · subst ha
    have : X01 m (0 : F) = 1 := SpecialLinearGroup.transvection_coeff_zero _
    rw [this, _root_.map_one, MulAut.one_apply, zero_mul, h.lineA_zero, one_mul]
  · have h1 := weyl_aux h hV2 hF2 ha (v := h.lineB d) (h.lineB_vanish d)
    have h2 : σ (X01 m a) (h.lineB d) * (h.lineB d)⁻¹ = h.lineA (a * d) := by
      apply h.bijective.1
      funext k
      rw [h1 k, h.phi_lineA, h.phi_lineB]
      by_cases hk : k = 0
      · subst hk; simp
      · simp [hk]
    rw [← h2, inv_mul_cancel_right]

omit hV2 hF2 in
theorem EqBij.X_lineA (t c : F) : σ (X01 m t) (h.lineA c) = h.lineA c :=
  fix_of_line h (h.lineA_vanish c) (X01_fix_e0 m t)

theorem EqBij.lineA_add (c c' : F) : h.lineA (c + c') = h.lineA c * h.lineA c' := by
  have h1 := h.X_lineB hV2 hF2 (c + c') 1
  rw [X01_add m, map_mul, MulAut.mul_apply, h.X_lineB hV2 hF2 c' 1, map_mul, h.X_lineA,
    h.X_lineB hV2 hF2 c 1, mul_one, mul_one, mul_one] at h1
  have h2 : h.lineA (c + c') * h.lineB 1 = (h.lineA c' * h.lineA c) * h.lineB 1 := by
    rw [← h1, mul_assoc]
  rw [mul_right_cancel h2, mul_comm]

omit hV2 in
theorem EqBij.W1_lineA (c : F) : σ (W1 m F) (h.lineA c) = h.lineB c := by
  apply h.bijective.1
  rw [h.equivariant, h.phi_lineA, h.phi_lineB]
  rw [W1_mulVec hF2 (by intro k hk; simp [hk])]
  simp

theorem EqBij.lineB_add (d d' : F) : h.lineB (d + d') = h.lineB d * h.lineB d' := by
  rw [← h.W1_lineA hF2, ← h.W1_lineA hF2, ← h.W1_lineA hF2, h.lineA_add hV2 hF2, map_mul]

theorem EqBij.pt_eq (c d : F) : h.pt c d = h.lineA c * h.lineB d := by
  by_cases hd : d = 0
  · subst hd
    rw [h.lineB_zero, mul_one, EqBij.pt, EqBij.lineA, zero_smul, add_zero]
  · have h1 : σ (X01 m (c / d)) (h.lineB d) = h.pt c d := by
      apply h.bijective.1
      rw [h.equivariant, h.phi_lineB, h.phi_pt, X01_mulVec]
      funext k
      by_cases hk0 : k = 0
      · subst hk0
        simp [div_mul_cancel₀ c hd]
      · by_cases hk1 : k = 1
        · subst hk1
          simp
        · simp [hk0, hk1]
    rw [← h1, h.X_lineB hV2 hF2, div_mul_cancel₀ c hd]

include h in
theorem EqBij.plane_add {v v' : V} (hv : ∀ k, k ≠ 0 → k ≠ 1 → Φ v k = 0)
    (hv' : ∀ k, k ≠ 0 → k ≠ 1 → Φ v' k = 0) : Φ (v * v') = Φ v + Φ v' := by
  have hrep : ∀ w : V, (∀ k, k ≠ 0 → k ≠ 1 → Φ w k = 0) → w = h.pt (Φ w 0) (Φ w 1) := by
    intro w hw
    apply h.bijective.1
    rw [h.phi_pt]
    funext k
    by_cases hk0 : k = 0
    · subst hk0; simp
    · by_cases hk1 : k = 1
      · subst hk1; simp
      · simp [hk0, hk1, hw k hk0 hk1]
  have e1 := hrep v hv
  have e2 := hrep v' hv'
  have e3 : v * v' = h.pt (Φ v 0 + Φ v' 0) (Φ v 1 + Φ v' 1) := by
    rw [h.pt_eq hV2 hF2, h.lineA_add hV2 hF2, h.lineB_add hV2 hF2]
    calc v * v' = (h.lineA (Φ v 0) * h.lineB (Φ v 1)) * (h.lineA (Φ v' 0) * h.lineB (Φ v' 1)) := by
          rw [← h.pt_eq hV2 hF2, ← h.pt_eq hV2 hF2, ← e1, ← e2]
      _ = _ := mul_mul_mul_comm _ _ _ _
  rw [e3, h.phi_pt]
  funext k
  by_cases hk0 : k = 0
  · subst hk0; simp
  · by_cases hk1 : k = 1
    · subst hk1; simp
    · simp [hk0, hk1, hv k hk0 hk1, hv' k hk0 hk1]

end Plane

end CFSG.CGT.T75N
