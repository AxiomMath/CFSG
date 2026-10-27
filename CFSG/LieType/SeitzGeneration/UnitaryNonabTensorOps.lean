module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabDefs

public section

namespace CFSG.LieType.SeitzGeneration.HeisP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {σ : K ≃+* K} {n m : ℕ} {p : ℕ} [NeZero p]

namespace HeisFrameP

variable {X Y : Matrix (Fin n) (Fin n) K} {α ζ : K} (F : HeisFrameP σ p n m X Y α ζ)

@[expose] def vecw (k : Fin p) (u : Fin m → K) : Fin n → K := ∑ r, u r • F.f k r

@[expose] def vec (ξ : Fin p → K) (u : Fin m → K) : Fin n → K := ∑ k, ξ k • F.vecw k u

theorem vec_add_left (ξ ξ' : Fin p → K) (u : Fin m → K) :
    F.vec (ξ + ξ') u = F.vec ξ u + F.vec ξ' u := by
  simp only [vec, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem vec_smul_left (c : K) (ξ : Fin p → K) (u : Fin m → K) :
    F.vec (c • ξ) u = c • F.vec ξ u := by
  simp only [vec, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem vec_zero_left (u : Fin m → K) : F.vec 0 u = 0 := by simp [vec]

theorem vecw_add (k : Fin p) (u u' : Fin m → K) :
    F.vecw k (u + u') = F.vecw k u + F.vecw k u' := by
  simp only [vecw, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem vecw_smul (k : Fin p) (c : K) (u : Fin m → K) :
    F.vecw k (c • u) = c • F.vecw k u := by
  simp only [vecw, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem vec_add_right (ξ : Fin p → K) (u u' : Fin m → K) :
    F.vec ξ (u + u') = F.vec ξ u + F.vec ξ u' := by
  simp only [vec, vecw_add, smul_add, Finset.sum_add_distrib]

theorem vec_smul_right (ξ : Fin p → K) (c : K) (u : Fin m → K) :
    F.vec ξ (c • u) = c • F.vec ξ u := by
  simp only [vec, vecw_smul, smul_comm c, Finset.smul_sum]

theorem herm_f_vecw (l : Fin p) (s : Fin m) (k : Fin p) (u : Fin m → K) :
    herm σ (F.f l s) (F.vecw k u) = if l = k then u s else 0 := by
  rw [vecw, herm_sum_right]
  simp only [herm_smul_right, F.on]
  by_cases h : l = k
  · simp [h]
  · simp [h]

theorem herm_vecw_f (k : Fin p) (u : Fin m → K) (l : Fin p) (s : Fin m)
    (hσ : ∀ c, σ (σ c) = c) :
    herm σ (F.vecw k u) (F.f l s) = if k = l then σ (u s) else 0 := by
  rw [herm_conj σ hσ, F.herm_f_vecw]
  split_ifs with h1 h2 h2 <;> simp_all

theorem herm_vecw_vecw (k l : Fin p) (u u' : Fin m → K) :
    herm σ (F.vecw k u) (F.vecw l u') = if k = l then herm σ u u' else 0 := by
  have e : F.vecw k u = ∑ r, u r • F.f k r := rfl
  rw [e, herm_sum_left]
  simp only [herm_smul_left, F.herm_f_vecw]
  by_cases h : k = l
  · simp [h, herm_def]
  · simp [h]

theorem herm_vec_vec (ξ ξ' : Fin p → K) (u u' : Fin m → K) :
    herm σ (F.vec ξ u) (F.vec ξ' u') = herm σ ξ ξ' * herm σ u u' := by
  have e : F.vec ξ u = ∑ k, ξ k • F.vecw k u := rfl
  have e' : F.vec ξ' u' = ∑ k, ξ' k • F.vecw k u' := rfl
  rw [e, e', herm_sum_left]
  simp only [herm_smul_left, herm_sum_right, herm_smul_right, F.herm_vecw_vecw]
  rw [herm_def σ ξ ξ', Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

@[expose] def rho (u : Fin m → K) (v : Fin n → K) : Fin p → K := fun l => herm σ (F.vecw l u) v

theorem rho_vec (u u' : Fin m → K) (ξ : Fin p → K) :
    F.rho u (F.vec ξ u') = herm σ u u' • ξ := by
  funext l
  have e : F.vec ξ u' = ∑ k, ξ k • F.vecw k u' := rfl
  simp only [rho, e, herm_sum_right, herm_smul_right, F.herm_vecw_vecw]
  simp [mul_comm]

theorem rho_f (hσ : ∀ c, σ (σ c) = c) (u : Fin m → K) (l : Fin p) (s : Fin m) (j : Fin p) :
    F.rho u (F.f l s) j = if j = l then σ (u s) else 0 :=
  F.herm_vecw_f j u l s hσ

@[expose] def Vu (u : Fin m → K) : Matrix (Fin n) (Fin p) K := Matrix.of fun i k => F.vecw k u i

@[expose] def Ru (u : Fin m → K) : Matrix (Fin p) (Fin n) K :=
  Matrix.of fun l j => σ (F.vecw l u j)

theorem Vu_mulVec (u : Fin m → K) (ξ : Fin p → K) : F.Vu u *ᵥ ξ = F.vec ξ u := by
  funext i
  simp only [Vu, vec, mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem Ru_mulVec (u : Fin m → K) (v : Fin n → K) : F.Ru u *ᵥ v = F.rho u v := by
  funext l
  simp only [Ru, rho, mulVec, dotProduct, Matrix.of_apply, herm_def]

@[expose] def Mmat (S : Matrix (Fin p) (Fin p) K) (c : K) (u : Fin m → K) :
    Matrix (Fin n) (Fin n) K :=
  1 + c • (F.Vu u * S * F.Ru u)

theorem Mmat_mulVec (S : Matrix (Fin p) (Fin p) K) (c : K) (u : Fin m → K) (v : Fin n → K) :
    F.Mmat S c u *ᵥ v = v + c • F.vec (S *ᵥ F.rho u v) u := by
  rw [Mmat, add_mulVec, one_mulVec, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Ru_mulVec,
    Vu_mulVec]

theorem rho_vec_self {u : Fin m → K} (hu : herm σ u u = 0) (ξ : Fin p → K) :
    F.rho u (F.vec ξ u) = 0 := by
  rw [rho_vec, hu, zero_smul]

theorem herm_left_vec (u : Fin m → K) (v : Fin n → K) (ξ : Fin p → K) :
    herm σ (F.vec ξ u) v = ∑ k, σ (ξ k) * F.rho u v k := by
  have e : F.vec ξ u = ∑ k, ξ k • F.vecw k u := rfl
  rw [e, herm_sum_left]
  simp only [herm_smul_left, rho]

theorem herm_right_vec (hσ : ∀ c, σ (σ c) = c) (u : Fin m → K) (v : Fin n → K)
    (ξ : Fin p → K) : herm σ v (F.vec ξ u) = ∑ k, ξ k * σ (F.rho u v k) := by
  have e : F.vec ξ u = ∑ k, ξ k • F.vecw k u := rfl
  rw [e, herm_sum_right]
  simp only [herm_smul_right]
  exact Finset.sum_congr rfl fun k _ => congrArg (ξ k * ·) (herm_conj σ hσ (F.vecw k u) v)

theorem Mmat_isometry (hσ : ∀ c, σ (σ c) = c) {S : Matrix (Fin p) (Fin p) K}
    (hS : ∀ a b, σ (S b a) = S a b) {c : K} (hc : c + σ c = 0) {u : Fin m → K}
    (hu : herm σ u u = 0) (v w : Fin n → K) :
    herm σ (F.Mmat S c u *ᵥ v) (F.Mmat S c u *ᵥ w) = herm σ v w := by
  rw [Mmat_mulVec, Mmat_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
  have h1 : herm σ (F.vec (S *ᵥ F.rho u v) u) (F.vec (S *ᵥ F.rho u w) u) = 0 := by
    rw [herm_vec_vec, hu, mul_zero]
  rw [h1, herm_right_vec F hσ, herm_left_vec]
  have key : ∑ k, σ ((S *ᵥ F.rho u v) k) * F.rho u w k =
      ∑ k, (S *ᵥ F.rho u w) k * σ (F.rho u v k) := by
    simp only [mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hS k l]
    ring
  rw [key]
  linear_combination (∑ k, (S *ᵥ F.rho u w) k * σ (F.rho u v k)) * hc

theorem Ru_mul_Vu {u : Fin m → K} (hu : herm σ u u = 0) : F.Ru u * F.Vu u = 0 := by
  ext l k
  have h := F.herm_vecw_vecw l k u u
  rw [hu] at h
  simp only [Matrix.mul_apply, Ru, Vu, Matrix.of_apply, Matrix.zero_apply]
  have h' : ∑ j, σ (F.vecw l u j) * F.vecw k u j = herm σ (F.vecw l u) (F.vecw k u) := rfl
  rw [h', h]
  split_ifs <;> rfl

theorem Mmat_det (S : Matrix (Fin p) (Fin p) K) (c : K) {u : Fin m → K}
    (hu : herm σ u u = 0) : (F.Mmat S c u).det = 1 := by
  have h1 : F.Mmat S c u = 1 + F.Vu u * (c • S * F.Ru u) := by
    rw [Mmat]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [h1, Matrix.det_one_add_mul_comm]
  have h0 : (c • S * F.Ru u) * F.Vu u = 0 := by
    rw [Matrix.mul_assoc, F.Ru_mul_Vu hu, Matrix.mul_zero]
  rw [h0]
  simp

@[expose] noncomputable def Mel (hσ : ∀ c, σ (σ c) = c) {S : Matrix (Fin p) (Fin p) K}
    (hS : ∀ a b, σ (S b a) = S a b) {c : K} (hc : c + σ c = 0) {u : Fin m → K}
    (hu : herm σ u u = 0) : SUid σ n :=
  mkSU σ (F.Mmat S c u) (F.Mmat_det S c hu) (F.Mmat_isometry hσ hS hc hu)

theorem Mel_smul (hσ : ∀ c, σ (σ c) = c) {S : Matrix (Fin p) (Fin p) K}
    (hS : ∀ a b, σ (S b a) = S a b) {c : K} (hc : c + σ c = 0) {u : Fin m → K}
    (hu : herm σ u u = 0) (v : Fin n → K) :
    F.Mel hσ hS hc hu • v = v + c • F.vec (S *ᵥ F.rho u v) u :=
  F.Mmat_mulVec S c u v

@[expose] def FrameAct (L : Matrix (Fin n) (Fin n) K) (G : Matrix (Fin p) (Fin p) K) : Prop :=
  ∀ k r, L *ᵥ F.f k r = ∑ k', G k' k • F.f k' r

theorem act_vecw {L : Matrix (Fin n) (Fin n) K} {G : Matrix (Fin p) (Fin p) K}
    (hL : F.FrameAct L G) (k : Fin p) (u : Fin m → K) :
    L *ᵥ F.vecw k u = ∑ k', G k' k • F.vecw k' u := by
  have hL' : ∀ k r, L *ᵥ F.f k r = ∑ k', G k' k • F.f k' r := hL
  have e : ∀ k, F.vecw k u = ∑ r, u r • F.f k r := fun k => rfl
  rw [e k, mulVec_sum]
  simp only [mulVec_smul, hL', Finset.smul_sum, e]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun r _ => smul_comm _ _ _

theorem act_vec {L : Matrix (Fin n) (Fin n) K} {G : Matrix (Fin p) (Fin p) K}
    (hL : F.FrameAct L G) (ξ : Fin p → K) (u : Fin m → K) :
    L *ᵥ F.vec ξ u = F.vec (G *ᵥ ξ) u := by
  have e : F.vec ξ u = ∑ k, ξ k • F.vecw k u := rfl
  have e' : F.vec (G *ᵥ ξ) u = ∑ k', (G *ᵥ ξ) k' • F.vecw k' u := rfl
  rw [e, e', mulVec_sum]
  simp only [mulVec_smul, F.act_vecw hL, Finset.smul_sum, smul_smul, mulVec, dotProduct,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem mulVec_eq_of_frame {ι : Type*} [Fintype ι] {A B : Matrix ι (Fin n) K}
    (h : ∀ k r, A *ᵥ F.f k r = B *ᵥ F.f k r) (v : Fin n → K) : A *ᵥ v = B *ᵥ v := by
  obtain ⟨c, rfl⟩ := F.span v
  simp only [mulVec_sum, mulVec_smul, h]

theorem rho_act (hσ : ∀ c, σ (σ c) = c) {L : Matrix (Fin n) (Fin n) K}
    {G : Matrix (Fin p) (Fin p) K} (hL : F.FrameAct L G) (u : Fin m → K) (v : Fin n → K) :
    F.rho u (L *ᵥ v) = G *ᵥ F.rho u v := by
  have hL' : ∀ k r, L *ᵥ F.f k r = ∑ k', G k' k • F.f k' r := hL
  rw [← F.Ru_mulVec, ← F.Ru_mulVec, mulVec_mulVec, mulVec_mulVec]
  refine F.mulVec_eq_of_frame (fun l s => ?_) v
  have hr : ∀ l s, F.Ru u *ᵥ F.f l s = fun j => if j = l then σ (u s) else 0 := fun l s => by
    rw [F.Ru_mulVec]
    funext j
    exact F.rho_f hσ u l s j
  rw [← mulVec_mulVec, ← mulVec_mulVec, hL' l s, mulVec_sum, hr l s]
  simp only [mulVec_smul, hr]
  funext j
  simp [Finset.sum_apply, mulVec, dotProduct, mul_comm]

theorem Mmat_commute (hσ : ∀ c, σ (σ c) = c) {L : Matrix (Fin n) (Fin n) K}
    {G S : Matrix (Fin p) (Fin p) K} (hL : F.FrameAct L G) (hSG : S * G = G * S) (c : K)
    (u : Fin m → K) : F.Mmat S c u * L = L * F.Mmat S c u := by
  have key : ∀ v, F.Mmat S c u *ᵥ (L *ᵥ v) = L *ᵥ (F.Mmat S c u *ᵥ v) := by
    intro v
    rw [Mmat_mulVec, Mmat_mulVec, mulVec_add, mulVec_smul, F.act_vec hL, F.rho_act hσ hL,
      mulVec_mulVec, mulVec_mulVec, hSG]
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact key _

theorem Y_pow_frame (j : ℕ) (k : Fin p) (r : Fin m) :
    (Y ^ j) *ᵥ F.f k r = (ζ ^ (j * (k : ℕ))) • F.f k r := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mulVec_mulVec, F.hY k r, mulVec_smul, ih, smul_smul, ← pow_add]
    congr 2
    ring

theorem actY : F.FrameAct Y (Zm ζ) := by
  intro k r
  rw [F.hY k r]
  simp only [Zm, Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem act_XY_pow (j : ℕ) : F.FrameAct (X * Y ^ j) (Gj ζ α j) := by
  intro k r
  rw [← mulVec_mulVec, F.Y_pow_frame j k r, mulVec_smul, F.hX k r, smul_smul]
  rw [Finset.sum_eq_single (k + 1)]
  · congr 1
    simp [Gj]
  · intro b _ hb
    simp [Gj, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

end HeisFrameP

end CFSG.LieType.SeitzGeneration.HeisP
