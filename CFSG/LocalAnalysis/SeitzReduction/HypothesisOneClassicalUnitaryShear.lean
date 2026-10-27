module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryShearSupply
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadicalNode

public section

namespace CFSG.SeitzReduction

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open UnitaryShear

variable {f : ℕ} {K : Type} [Field K] {n : ℕ}

namespace UnitaryShear

theorem primeFormPsi_apply_mk {p : ℕ} (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (φ : K ≃+* K) (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
    primeFormPsi h hC ⟨A, φ⟩ (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
      ((⟨(A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹,
        conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h hC φ g.2)⟩ :
          gramSU h (C : Matrix (Fin n) (Fin n) K)) :
        primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  rw [primeFormPsi_apply, MulAut.mul_apply]
  change primeFormConjHom h _ A (primeFormFieldAut h hC φ (g : primeFormP h _)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

theorem eq_of_mk_eq_of_pow_four (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n)
    {G : Matrix (Fin n) (Fin n) K} {X Y : gramSU h G}
    (hXY : (X : primeFormP h G) = (Y : primeFormP h G)) (hX : (X : GL (Fin n) K) ^ 4 = 1)
    (hY : (Y : GL (Fin n) K) ^ 4 = 1) : X = Y := by
  have : CharP K 2 := h.charP
  obtain ⟨c, -, -, hc⟩ := QuotientGroup.eq.mp hXY
  have hYc : (Y : GL (Fin n) K) = X * GeneralLinearGroup.scalar (Fin n) c := by
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have h4 : GeneralLinearGroup.scalar (Fin n) (c ^ 4) = 1 := by
    have h2 : ((X : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c) ^ 4 =
        (X : GL (Fin n) K) ^ 4 * GeneralLinearGroup.scalar (Fin n) c ^ 4 :=
      (commute_scalar c (X : GL (Fin n) K)).mul_pow 4
    rw [← hYc, hY, hX, one_mul] at h2
    rw [map_pow]
    exact h2.symm
  have hc1 : c = 1 := by
    have h2 := congrArg (fun Z : GL (Fin n) K =>
      (Z : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) h4
    have h3 : ((c : K) ^ 4) = 1 := by
      have h5 : ((GeneralLinearGroup.scalar (Fin n) (c ^ 4) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩ = ((c ^ 4 : Kˣ) : K) := by
        rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq]
      rw [← Units.val_pow_eq_pow_val, ← h5]
      exact h2.trans (by rw [Units.val_one, one_apply_eq])
    exact Units.ext (eq_one_of_pow_four_eq_one_of_charTwo h3)
  apply Subtype.ext
  rw [hYc, hc1, map_one, mul_one]

theorem mul_map_eq_of_commutator (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 1 ≤ n) (s : gramSU h (C : Matrix (Fin n) (Fin n) K))
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
    (hβ : ∀ c : primeFormP h (C : Matrix (Fin n) (Fin n) K),
      primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩ c = c → Odd (orderOf c) →
        primeFormPsi h hC ⟨A, φ⟩ c = c)
    (r y : gramSU h (C : Matrix (Fin n) (Fin n) K))
    (hrs : (s : GL (Fin n) K) * r = r * s) (hys : (s : GL (Fin n) K) * y = y * s)
    (hy : y ^ (2 ^ f + 1) = 1)
    (hM : ((r * y * r⁻¹ * y⁻¹ : gramSU h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) ^ 4 = 1) :
    ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((r * y * r⁻¹ * y⁻¹ : gramSU h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).map φ =
      (((r * y * r⁻¹ * y⁻¹ : gramSU h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hodd : Odd (2 ^ f + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩).add_one
  have hfix : ∀ g : gramSU h (C : Matrix (Fin n) (Fin n) K),
      (s : GL (Fin n) K) * g = g * s → g ^ (2 ^ f + 1) = 1 →
        primeFormPsi h hC ⟨A, φ⟩ (g : primeFormP h _) = (g : primeFormP h _) := by
    intro g hgs hg
    refine hβ _ ?_ ?_
    · rw [primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      change (s : GL (Fin n) K) * g * (s : GL (Fin n) K)⁻¹ = g
      rw [hgs, mul_inv_cancel_right]
    · refine hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
      rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  have hc1 : Commute (s : GL (Fin n) K) (r : GL (Fin n) K) := hrs
  have hc2 : Commute (s : GL (Fin n) K) (y : GL (Fin n) K) := hys
  have h1 := hfix (r * y * r⁻¹) (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact ((hc1.mul_right hc2).mul_right hc1.inv_right).eq)
    (by rw [conj_pow, hy, mul_one, mul_inv_cancel])
  have h2 := hfix y hys hy
  have h3 : primeFormPsi h hC ⟨A, φ⟩
      ((r * y * r⁻¹ * y⁻¹ : gramSU h (C : Matrix (Fin n) (Fin n) K)) : primeFormP h _) =
      ((r * y * r⁻¹ * y⁻¹ : gramSU h (C : Matrix (Fin n) (Fin n) K)) : primeFormP h _) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, h1, h2]
  rw [primeFormPsi_apply_mk] at h3
  set M := (r * y * r⁻¹ * y⁻¹ : gramSU h (C : Matrix (Fin n) (Fin n) K)) with hMdef
  have h4 := eq_of_mk_eq_of_pow_four h hn h3 (by
    change ((A : GL (Fin n) K) * glAut φ (M : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹) ^ 4 = 1
    rw [conj_pow, ← map_pow, hM, map_one, mul_one, mul_inv_cancel]) hM
  have h5 := congrArg (fun X : gramSU h (C : Matrix (Fin n) (Fin n) K) =>
    ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h4
  simp only [Units.val_mul, coe_glAut] at h5
  calc ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ *
        ((((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    _ = ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← Matrix.mul_assoc, h5]

theorem pow_four_eq_one_of_isShear [CharP K 2] {σ : K →+* K}
    {B : (Fin n → K) →ₛₗ[σ] (Fin n → K) →ₗ[K] K} {W L : Submodule K (Fin n → K)}
    (hWL : W ≤ L) (hW : W = L.orthogonalBilin B) {w u : Fin n → K} (hw : w ∈ W) (hu : u ∈ L)
    (M : GL (Fin n) K) (hM : IsShear B W L w u ((M : Matrix (Fin n) (Fin n) K) *ᵥ ·)) :
    M ^ 4 = 1 :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_four_eq_one_of_sub_one_pow_three
      (sub_one_pow_three_eq_zero (hM.sub_one_cube hWL hW hw hu)))

end UnitaryShear

theorem involutionCriterion_primeFormConj_of_ne (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 4 ≤ n) (s : gramSU h (C : Matrix (Fin n) (Fin n) K))
    (hs2 : (s : GL (Fin n) K) * s = 1) (hs1 : (s : GL (Fin n) K) ≠ 1)
    (hsWL : LinearMap.range (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).mulVecLin ≠
      LinearMap.ker (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).mulVecLin) :
    InvolutionCriterion (primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩) := by
  have : CharP K 2 := h.charP
  intro β hβx hβc
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC (by omega) (by omega) β
  set Sm := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hSm
  set Hf := gramForm h (C : Matrix (Fin n) (Fin n) K) with hHf
  set W := LinearMap.range (Sm - 1).mulVecLin with hWdef
  set L := LinearMap.ker (Sm - 1).mulVecLin with hLdef
  have hH : Hf.IsSymm := gramForm_isSymm h (hC.barTranspose h)
  have hSiso := (mem_gramSU_iff_isometry.mp s.2).1
  have hSm2 : Sm * Sm = 1 := by rw [hSm, ← Units.val_mul, hs2, Units.val_one]
  have hSS : ∀ v, Sm *ᵥ (Sm *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hSm2, one_mulVec]
  have hNv : ∀ v, (Sm - 1) *ᵥ v = Sm *ᵥ v - v := fun v => by rw [sub_mulVec, one_mulVec]
  have hAs : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Sm.map φ =
      Sm * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h1 : primeFormPsi h hC ⟨A, φ⟩ *
        primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩ *
        (primeFormPsi h hC ⟨A, φ⟩)⁻¹ =
          primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hβx
    rw [psi_mul_conj_mul_inv] at h1
    have hs4 : (⟨s, s.2.1⟩ : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) ^ 4 = 1 := by
      apply Subtype.ext
      change (s : GL (Fin n) K) ^ 4 = 1
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hs2, one_mul]
    have h2 := eq_of_primeFormConjHom_eq h hC (by omega) h1 (by
      rw [conj_pow, ← map_pow, hs4, map_one, mul_one, mul_inv_cancel]) hs4
    have h3 := congrArg (fun X : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) =>
      ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, Units.val_mul,
      coe_glAut] at h3
    calc ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Sm.map φ =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Sm.map φ *
          ((((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = Sm * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [← Matrix.mul_assoc, h3]
  have hL : L = W.orthogonalBilin Hf :=
    SesqShear.ker_sub_one_eq_orthogonalBilin_range h (hC.barTranspose h)
      (primeFormGram_det_ne_zero C) hSiso
  have hW : W = L.orthogonalBilin Hf := by
    rw [hL, SesqShear.gramForm_orthogonalBilin_orthogonalBilin h (hC.barTranspose h)
      (primeFormGram_det_ne_zero C)]
  have hWL : W ≤ L := by
    rintro _ ⟨x, rfl⟩
    rw [hLdef, mem_ker_sub_one, Matrix.mulVecLin_apply, hNv, mulVec_sub, hSS]
    have h2 : (2 : K) • x = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    have h3 : (2 : K) • (Sm *ᵥ x) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    linear_combination (norm := module) h2 - h3
  obtain ⟨ζ, hζ, hζ1⟩ : ∃ ζ : K, h.norm ζ = 1 ∧ ζ ≠ 1 := by
    obtain ⟨r, hr⟩ := h.exists_bar_ne
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hr (map_zero _)
    refine ⟨r / h.bar r, h.norm_div_bar hr0, fun h1 => hr ?_⟩
    exact ((div_eq_one_iff_eq ((h.bar_eq_zero_iff).not.mpr hr0)).mp h1).symm
  obtain ⟨θ, hθ⟩ := h.exists_trace_ne_zero
  have hθ' : θ + h.bar θ ≠ 0 := hθ
  set P : ((Fin n → K) → Fin n → K) → Prop := fun g => ∃ M : Matrix (Fin n) (Fin n) K,
    (∀ v, g v = M *ᵥ v) ∧ ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map φ =
      M * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hP
  have hP1 : P id := ⟨1, fun v => (one_mulVec v).symm, by
    rw [Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.mul_one, Matrix.one_mul]⟩
  have hPc : ∀ g₁ g₂, P g₁ → P g₂ → P (g₁ ∘ g₂) := by
    rintro g₁ g₂ ⟨M₁, hg₁, hM₁⟩ ⟨M₂, hg₂, hM₂⟩
    refine ⟨M₁ * M₂, fun v => by rw [Function.comp_apply, hg₂, hg₁, mulVec_mulVec], ?_⟩
    rw [Matrix.map_mul, ← Matrix.mul_assoc, hM₁, Matrix.mul_assoc, hM₂, ← Matrix.mul_assoc]
  have hcomm : ∀ (r y : gramSU h (C : Matrix (Fin n) (Fin n) K)) (w u : Fin n → K), w ∈ W →
      u ∈ L → (s : GL (Fin n) K) * r = r * s → (s : GL (Fin n) K) * y = y * s →
      y ^ (2 ^ f + 1) = 1 →
      IsShear Hf W L w u
        ((((r * y * r⁻¹ * y⁻¹ : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) →
      ∃ g, P g ∧ IsShear Hf W L w u g := by
    intro r y w u hw hu hrs hys hy hsh
    exact ⟨_, ⟨_, fun v => rfl, mul_map_eq_of_commutator h hC (by omega) s A φ hβc r y hrs hys hy
      (pow_four_eq_one_of_isShear hWL hW hw hu _ hsh)⟩, hsh⟩
  have hdim : (∀ e₀ : Fin n → K, ¬L ≤ W ⊔ Submodule.span K {e₀}) ∨
      ∀ e₀ : Fin n → K, ¬(⊤ : Submodule K (Fin n → K)) ≤ L ⊔ Submodule.span K {e₀} := by
    by_contra hcon
    simp only [not_or, not_forall, not_not] at hcon
    obtain ⟨⟨e₀, he₀⟩, ⟨e₁, he₁⟩⟩ := hcon
    have hrn : Module.finrank K W + Module.finrank K L = n := by
      have := LinearMap.finrank_range_add_finrank_ker (Sm - 1).mulVecLin
      rwa [Module.finrank_fin_fun] at this
    have hsp : ∀ e : Fin n → K, Module.finrank K (Submodule.span K {e}) ≤ 1 := fun e =>
      (finrank_span_le_card ({e} : Set (Fin n → K))).trans (by simp)
    have h1 : Module.finrank K L ≤ Module.finrank K W + 1 :=
      (Submodule.finrank_mono he₀).trans ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans
        (by have := hsp e₀; omega))
    have h2 : n ≤ Module.finrank K L + 1 := by
      have := (Submodule.finrank_mono he₁).trans
        (Submodule.finrank_add_le_finrank_add_finrank L (Submodule.span K {e₁}))
      rw [finrank_top, Module.finrank_fin_fun] at this
      have := hsp e₁
      omega
    omega
  have hall : ∀ w ∈ W, ∀ u ∈ L, ∃ g, P g ∧ IsShear Hf W L w u g := by
    rcases hdim with hA | hB
    ·
      refine forall_isShear_of_le_span_right hWL hL hW hP1 hPc (X := anisotropicPairs Hf L)
        (fun x hx => hx.1) ?_ ?_
      · refine le_sup_span_anisotropicPairs (σ := h.bar) (fun a => h.bar_bar a)
          (fun x y => hH.eq x y) hθ' (fun x _ => ?_) hA
        rw [hW]
        exact Submodule.mem_orthogonalBilin
      · intro w hw x hx a
        obtain ⟨r, y, hrs, hys, hy, hsh⟩ :=
          exists_commutator_shear_right h hH s.2 hWdef hLdef hWL hL hW hζ hζ1 hw hx a
        exact hcomm r y w (a • x) hw (L.smul_mem a hx.1) hrs hys hy hsh
    ·
      have hNB : ∀ x y, Hf ((Sm - 1) *ᵥ x) y = Hf x ((Sm - 1) *ᵥ y) := fun x y => by
        rw [hNv, hNv, map_sub, map_sub, LinearMap.sub_apply, ← hSiso (Sm *ᵥ x) y, hSS]
      set βs := Hf.compl₂ (Sm - 1).mulVecLin with hβs
      have hβs_apply : ∀ x y, βs x y = Hf x ((Sm - 1) *ᵥ y) := fun x y => rfl
      have hspan : (⊤ : Submodule K (Fin n → K)) ≤
          L ⊔ Submodule.span K (anisotropicPairs βs ⊤) := by
        refine le_sup_span_anisotropicPairs (σ := h.bar) (fun a => h.bar_bar a)
          (fun x y => ?_) hθ' (fun x _ => ?_) hB
        · rw [hβs_apply, hβs_apply, hH.eq, ← hNB]
        · rw [hLdef, LinearMap.mem_ker]
          constructor
          · intro hx y _
            rw [hβs_apply, ← Matrix.mulVecLin_apply, hx, map_zero]
          · intro hx
            refine gramForm_separatingLeft h (primeFormGram_det_ne_zero C) _ fun y => ?_
            rw [← hH.eq, map_eq_zero_iff _ (h.bar.injective)]
            exact hx y (Submodule.mem_top)
      refine forall_isShear_of_le_span_left hWL hL hW hP1 hPc
        (Y := (Sm - 1).mulVecLin '' anisotropicPairs βs ⊤) ?_ ?_ ?_
      · rintro _ ⟨e, -, rfl⟩
        exact ⟨e, rfl⟩
      · rintro _ ⟨v, rfl⟩
        obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.mp (hspan (Submodule.mem_top (x := v)))
        rw [map_add, LinearMap.mem_ker.mp hl, zero_add, ← Submodule.map_span]
        exact Submodule.mem_map_of_mem hx
      · rintro _ ⟨e, ⟨-, he, e', -, he', hee'⟩, rfl⟩ a u hu
        obtain ⟨r, y, hrs, hys, hy, hsh⟩ :=
          exists_commutator_shear_left h hH s.2 hs2 hWdef hLdef hWL hL hW hζ hζ1 he he' hee' a hu
        exact hcomm r y _ u (W.smul_mem a ⟨e, rfl⟩) hu hrs hys hy hsh
  have hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ M : Matrix (Fin n) (Fin n) K,
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map φ =
        M * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      (∀ v ∈ L, M *ᵥ v = v - Hf u v • w) ∧ ∀ v, M *ᵥ v - v - Hf w v • u ∈ W := by
    intro w hw u hu
    obtain ⟨g, ⟨M, hgM, hM⟩, hg⟩ := hall w hw u hu
    refine ⟨M, hM, fun v hv => ?_, fun v => ?_⟩
    · rw [← hgM]
      exact hg.1 v hv
    · rw [← hgM]
      exact hg.2 v
  exact (primeFormPsi_sq_eq_one_of_involution_shear h hC s.2.1 hs2 hs1 hsWL A φ hAs hsh).2

end CFSG.SeitzReduction
