module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParPk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParMat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {t : OGroup Q} (D : Om6Par Q t)

theorem Om6Par.simAct_t {x : simGroup Q} (hL : ∀ u ∈ D.L, simAct Q x u ∈ D.L)
    (hR : ∀ u ∈ D.R, simAct Q x u ∈ D.R) : simAct Q x t = t := by
  rcases D.sec5Pair.inf_eq (hL t D.sec5Pair.z_mem₁) (hR t D.sec5Pair.z_mem₂) with h | h
  · exact absurd ((MulEquiv.map_eq_one_iff _).mp h) D.ne_one
  · exact h

theorem om6par_comm_t {y : simGroup Q} (hy : simAct Q y t = t) (v : V) :
    (y : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) v) =
      (t : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) v) := by
  have h1 := congrArg (fun s : OGroup Q => (s : V ≃ₗ[ZMod 3] V)) hy
  simp only [coe_simAct] at h1
  have h2 := congrArg (fun s : V ≃ₗ[ZMod 3] V => s v) (mul_inv_eq_iff_eq_mul.mp h1)
  simpa only [LinearEquiv.mul_apply] using h2

theorem Om6Par.preserve_W (D : Om6Par Q t) {y : simGroup Q} (hy : simAct Q y t = t) :
    ∀ w ∈ commSp t, (y : V ≃ₗ[ZMod 3] V) w ∈ commSp t := by
  intro w hw
  have h := om6par_comm_t hy w
  rw [mem_commSp_iff D.htt] at hw ⊢
  rw [← h, hw, map_neg]

theorem om6par_preserve_P {y : simGroup Q} (hy : simAct Q y t = t) :
    ∀ p ∈ fixSp t, (y : V ≃ₗ[ZMod 3] V) p ∈ fixSp t := by
  intro p hp
  have h := om6par_comm_t hy p
  rw [mem_fixSp_iff] at hp ⊢
  rw [← h, hp]

theorem Om6Par.exists_sigma {y : simGroup Q} (hy : simAct Q y t = t) :
    ∃ σ : Mat2 ≃ₗ[ZMod 3] Mat2, ∀ X, (y : V ≃ₗ[ZMod 3] V) (D.iota X) = D.iota (σ X) := by
  have hy' : simAct Q y⁻¹ t = t := by
    rw [← hy, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply, hy]
  have hW := D.preserve_W hy
  have hW' := D.preserve_W hy'
  have heq : (commSp t).map ((y : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) = commSp t := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hW w hw
    · intro w hw
      exact ⟨(y : V ≃ₗ[ZMod 3] V).symm w, hW' w hw, (y : V ≃ₗ[ZMod 3] V).apply_symm_apply w⟩
  refine ⟨D.e.toLinearEquiv.trans
    (((y : V ≃ₗ[ZMod 3] V).ofSubmodules (commSp t) (commSp t) heq).trans
      D.e.toLinearEquiv.symm), fun X => ?_⟩
  simp [Om6Par.iota]

theorem Om6Par.quad_iota (X : Mat2) : Q (D.iota X) = X.det := by
  rw [← detForm_apply]
  exact D.e.map_app X

theorem Om6Par.iota_injective : Function.Injective D.iota := fun X Y h =>
  D.e.toLinearEquiv.injective (Subtype.ext h)

theorem om6par_comm_four_right : ∀ m n : Mat2, m * n = 1 →
    ((∃ s : SL2F3, ¬ ((s : Mat2) * m * ((s⁻¹ : SL2F3) : Mat2) * n) ^ 4 = 1) ↔ m.det = -1) := by
  decide +kernel

theorem Om6Par.conj_apply {x : simGroup Q} {σ : Mat2 ≃ₗ[ZMod 3] Mat2}
    (hσ : ∀ X, (x : V ≃ₗ[ZMod 3] V) (D.iota X) = D.iota (σ X)) (a : OGroup detForm) (X : Mat2) :
    ((simAct Q x⁻¹ (D.theta a) * (D.theta a)⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) (D.iota X) =
      D.iota (σ.symm (((a : OGroup detForm) : Mat2 ≃ₗ[ZMod 3] Mat2)
        (σ (((a⁻¹ : OGroup detForm) : Mat2 ≃ₗ[ZMod 3] Mat2) X)))) := by
  have hσ' : ∀ Z, (x : V ≃ₗ[ZMod 3] V).symm (D.iota Z) = D.iota (σ.symm Z) := fun Z => by
    rw [LinearEquiv.symm_apply_eq, hσ, LinearEquiv.apply_symm_apply]
  rw [← map_inv D.theta a]
  simp only [Subgroup.coe_mul, coe_simAct, Subgroup.coe_inv, LinearEquiv.mul_apply, inv_inv]
  rw [D.theta_apply_W a⁻¹ X, hσ, D.theta_apply_W a]
  exact hσ' _

theorem om6par_simAct_apply (x : simGroup Q) (u : OGroup Q) (v : V) :
    (x : V ≃ₗ[ZMod 3] V) ((u : V ≃ₗ[ZMod 3] V) v) =
      ((simAct Q x u : OGroup Q) : V ≃ₗ[ZMod 3] V) ((x : V ≃ₗ[ZMod 3] V) v) := by
  rw [coe_simAct]
  simp

theorem om6par_sigma_form {σ : Mat2 ≃ₗ[ZMod 3] Mat2} {μ : ZMod 3} (hμ : μ ≠ 0)
    (hdet : ∀ X : Mat2, (σ X).det = μ * X.det)
    (hL : ∀ A : SL2F3, ∃ A' : SL2F3, ∀ X : Mat2, σ ((A : Mat2) * X) = (A' : Mat2) * σ X) :
    ∃ G G' m m' : Mat2, G * G' = 1 ∧ G' * G = 1 ∧ m * m' = 1 ∧ m' * m = 1 ∧
      (∀ X, σ X = G * X * m) ∧ G.det * m.det = μ := by
  obtain ⟨g, hg⟩ := om6par_mat2_form σ hμ hdet hL
  have hdet1 : (σ 1).det = μ := by rw [hdet, Matrix.det_one, mul_one]
  have hu : IsUnit (σ 1).det := by rw [hdet1]; exact IsUnit.mk0 _ hμ
  refine ⟨(g : Mat2), ((g⁻¹ : Mat2ˣ) : Mat2), ((g⁻¹ : Mat2ˣ) : Mat2) * σ 1, (σ 1)⁻¹ * (g : Mat2),
    g.mul_inv, g.inv_mul, ?_, ?_, fun X => ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (σ 1), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    exact g.inv_mul
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g : Mat2), g.mul_inv, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hu]
  · rw [hg X, Matrix.mul_assoc _ _ (σ 1)]
  · rw [Matrix.det_mul, ← mul_assoc, ← Matrix.det_mul, g.mul_inv, Matrix.det_one, one_mul, hdet1]

theorem Om6Par.pow_four_iff {κ : SL2F3 →* OGroup detForm} (hκ : Function.Injective κ)
    (s : SL2F3) : (D.theta (κ s)) ^ 4 = 1 ↔ (s : Mat2) ^ 4 = 1 := by
  rw [← map_pow, ← map_pow, ← map_one D.theta, D.theta_injective.eq_iff, ← map_one κ,
    hκ.eq_iff]
  constructor
  · intro h
    simpa using congrArg (fun A : SL2F3 => (A : Mat2)) h
  · intro h
    exact Subtype.ext (by simpa using h)

theorem om6par_inv_pow_four : ∀ s : SL2F3,
    ((s⁻¹ : SL2F3) : Mat2) ^ 4 = 1 ↔ (s : Mat2) ^ 4 = 1 := by
  decide +kernel

theorem om6par_symm_form {σ : Mat2 ≃ₗ[ZMod 3] Mat2} {G G' m m' : Mat2} (hGG' : G * G' = 1)
    (hm'm : m' * m = 1) (hσ' : ∀ X, σ X = G * X * m) (Z : Mat2) : σ.symm Z = G' * Z * m' := by
  rw [LinearEquiv.symm_apply_eq, hσ']
  calc Z = (G * G') * Z * (m' * m) := by rw [hGG', hm'm, Matrix.one_mul, Matrix.mul_one]
    _ = G * (G' * Z * m') * m := by simp only [Matrix.mul_assoc]

theorem om6par_simAct_inv_mem {x : simGroup Q} {H : Subgroup (OGroup Q)}
    (hH : ∀ u : OGroup Q, simAct Q x u ∈ H ↔ u ∈ H) {u : OGroup Q} (hu : u ∈ H) :
    simAct Q x⁻¹ u ∈ H :=
  (hH _).mp (by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]; exact hu)

theorem Om6Par.sideL {x : simGroup Q} {σ : Mat2 ≃ₗ[ZMod 3] Mat2}
    (hσ : ∀ X, (x : V ≃ₗ[ZMod 3] V) (D.iota X) = D.iota (σ X))
    (hL : ∀ u : OGroup Q, simAct Q x u ∈ D.L ↔ u ∈ D.L) {G G' m m' : Mat2}
    (hGG' : G * G' = 1) (hmm' : m * m' = 1) (hm'm : m' * m = 1)
    (hσ' : ∀ X, σ X = G * X * m) :
    (∃ u ∈ D.L, ¬ (simAct Q x⁻¹ u * u⁻¹) ^ 4 = 1) ↔
      ∃ s : SL2F3, ¬ (G' * (s : Mat2) * G * ((s⁻¹ : SL2F3) : Mat2)) ^ 4 = 1 := by
  have hconj : ∀ s : SL2F3, ∃ s' : SL2F3,
      simAct Q x⁻¹ (D.theta (leftMulHom s)) * (D.theta (leftMulHom s))⁻¹ =
        D.theta (leftMulHom s') ∧ (s' : Mat2) = G' * (s : Mat2) * G * ((s⁻¹ : SL2F3) : Mat2) := by
    intro s
    have hu : D.theta (leftMulHom s) ∈ D.L := ⟨_, ⟨s, rfl⟩, rfl⟩
    obtain ⟨_, ⟨s', rfl⟩, hs'⟩ := D.L.mul_mem (om6par_simAct_inv_mem hL hu) (D.L.inv_mem hu)
    refine ⟨s', hs'.symm, ?_⟩
    have h1 := D.conj_apply hσ (leftMulHom s) 1
    rw [← hs', D.theta_apply_W] at h1
    have h2 := D.iota_injective h1
    rw [← map_inv, leftMulHom_apply, leftMulHom_apply, hσ', om6par_symm_form hGG' hm'm hσ',
      leftMulHom_apply] at h2
    calc (s' : Mat2) = (s' : Mat2) * 1 := (Matrix.mul_one _).symm
      _ = _ := h2
      _ = _ := by simp only [Matrix.mul_one, Matrix.mul_assoc, hmm']
  constructor
  · rintro ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hu⟩
    obtain ⟨s', hs', hs'm⟩ := hconj s
    refine ⟨s, fun h => hu ?_⟩
    rw [hs', D.pow_four_iff leftMulHom_injective, hs'm]
    exact h
  · rintro ⟨s, hs⟩
    obtain ⟨s', hs', hs'm⟩ := hconj s
    refine ⟨D.theta (leftMulHom s), ⟨_, ⟨s, rfl⟩, rfl⟩, fun h => hs ?_⟩
    rw [hs', D.pow_four_iff leftMulHom_injective, hs'm] at h
    exact h

theorem Om6Par.sideR {x : simGroup Q} {σ : Mat2 ≃ₗ[ZMod 3] Mat2}
    (hσ : ∀ X, (x : V ≃ₗ[ZMod 3] V) (D.iota X) = D.iota (σ X))
    (hR : ∀ u : OGroup Q, simAct Q x u ∈ D.R ↔ u ∈ D.R) {G G' m m' : Mat2}
    (hGG' : G * G' = 1) (hG'G : G' * G = 1) (hm'm : m' * m = 1)
    (hσ' : ∀ X, σ X = G * X * m) :
    (∃ u ∈ D.R, ¬ (simAct Q x⁻¹ u * u⁻¹) ^ 4 = 1) ↔
      ∃ s : SL2F3, ¬ ((s : Mat2) * m * ((s⁻¹ : SL2F3) : Mat2) * m') ^ 4 = 1 := by
  have hconj : ∀ s : SL2F3, ∃ s' : SL2F3,
      simAct Q x⁻¹ (D.theta (rightMulHom s)) * (D.theta (rightMulHom s))⁻¹ =
        D.theta (rightMulHom s') ∧
      ((s'⁻¹ : SL2F3) : Mat2) = (s : Mat2) * m * ((s⁻¹ : SL2F3) : Mat2) * m' := by
    intro s
    have hu : D.theta (rightMulHom s) ∈ D.R := ⟨_, ⟨s, rfl⟩, rfl⟩
    obtain ⟨_, ⟨s', rfl⟩, hs'⟩ := D.R.mul_mem (om6par_simAct_inv_mem hR hu) (D.R.inv_mem hu)
    refine ⟨s', hs'.symm, ?_⟩
    have h1 := D.conj_apply hσ (rightMulHom s) 1
    rw [← hs', D.theta_apply_W] at h1
    have h2 := D.iota_injective h1
    rw [← map_inv, rightMulHom_apply, rightMulHom_apply, hσ', om6par_symm_form hGG' hm'm hσ',
      rightMulHom_apply] at h2
    have key : ∀ Z : Mat2, G' * (G * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, hG'G, Matrix.one_mul]
    simp only [inv_inv, Matrix.one_mul, Matrix.mul_assoc, key] at h2 ⊢
    exact h2
  constructor
  · rintro ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hu⟩
    obtain ⟨s', hs', hs'm⟩ := hconj s
    refine ⟨s, fun h => hu ?_⟩
    rw [hs', D.pow_four_iff rightMulHom_injective, ← om6par_inv_pow_four, hs'm]
    exact h
  · rintro ⟨s, hs⟩
    obtain ⟨s', hs', hs'm⟩ := hconj s
    refine ⟨D.theta (rightMulHom s), ⟨_, ⟨s, rfl⟩, rfl⟩, fun h => hs ?_⟩
    rw [hs', D.pow_four_iff rightMulHom_injective, ← om6par_inv_pow_four, hs'm] at h
    exact h

theorem Om6Par.exists_left {x : simGroup Q} {σ : Mat2 ≃ₗ[ZMod 3] Mat2}
    (hσ : ∀ X, (x : V ≃ₗ[ZMod 3] V) (D.iota X) = D.iota (σ X))
    (hL : ∀ u : OGroup Q, simAct Q x u ∈ D.L ↔ u ∈ D.L) (A : SL2F3) :
    ∃ A' : SL2F3, ∀ X : Mat2, σ ((A : Mat2) * X) = (A' : Mat2) * σ X := by
  obtain ⟨_, ⟨A', rfl⟩, hA'⟩ := (hL (D.theta (leftMulHom A))).mpr ⟨_, ⟨A, rfl⟩, rfl⟩
  refine ⟨A', fun X => D.iota_injective ?_⟩
  have h1 := om6par_simAct_apply x (D.theta (leftMulHom A)) (D.iota X)
  rw [D.theta_apply_W, leftMulHom_apply, hσ ((A : Mat2) * X), ← hA', hσ X, D.theta_apply_W,
    leftMulHom_apply] at h1
  exact h1

theorem om6par_xor_neg_one : ∀ a b c : ZMod 3, a * b = c → c ≠ 0 →
    (Xor' (a = -1) (b = -1) ↔ c = -1) := by
  simp only [Xor']
  decide

theorem Om6Par.lhs_iff {x : simGroup Q} {c : (ZMod 3)ˣ}
    (hc : IsSimilitude Q (x : V ≃ₗ[ZMod 3] V) c)
    (hL : ∀ u : OGroup Q, simAct Q x u ∈ D.L ↔ u ∈ D.L)
    (hR : ∀ u : OGroup Q, simAct Q x u ∈ D.R ↔ u ∈ D.R) :
    Xor' (∃ u ∈ D.L, ¬ (simAct Q x⁻¹ u * u⁻¹) ^ 4 = 1)
      (∃ u ∈ D.R, ¬ (simAct Q x⁻¹ u * u⁻¹) ^ 4 = 1) ↔ (c : ZMod 3) = -1 := by
  obtain ⟨σ, hσ⟩ := D.exists_sigma
    (D.simAct_t (fun u hu => (hL u).mpr hu) (fun u hu => (hR u).mpr hu))
  have hdet : ∀ X : Mat2, (σ X).det = (c : ZMod 3) * X.det := fun X => by
    rw [← D.quad_iota, ← hσ, hc, D.quad_iota]
  obtain ⟨G, G', m, m', hGG', hG'G, hmm', hm'm, hσ', hGm⟩ :=
    om6par_sigma_form c.ne_zero hdet (D.exists_left hσ hL)
  rw [D.sideL hσ hL hGG' hmm' hm'm hσ', D.sideR hσ hR hGG' hG'G hm'm hσ',
    om6par_comm_four G G' hGG', om6par_comm_four_right m m' hmm']
  exact om6par_xor_neg_one _ _ _ hGm c.ne_zero

end CFSG.OddStandard.SmallF3.Omega
