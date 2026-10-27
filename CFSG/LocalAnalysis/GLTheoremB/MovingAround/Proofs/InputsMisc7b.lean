module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinearAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7

namespace LinearPSL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] {n : ℕ}

theorem exists_mul_eq_smul_of_conjAut_fix {A : GL (Fin n) F} {B : SpecialLinearGroup (Fin n) F}
    (h : conjAut n F A (proj n F B) = proj n F B) :
    ∃ c : F, (A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) =
      c • ((B : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := h
  have h1 : (B : Matrix (Fin n) (Fin n) F) =
      ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A B :
        SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) * scalar (Fin n) (c : F) := by
    rw [← hc]
    show (B : Matrix (Fin n) (Fin n) F) =
      ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A B *
        ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A B)⁻¹ * B) :
          SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [mul_inv_cancel_left]
  rw [coe_slConjugation] at h1
  refine ⟨((c⁻¹ : Fˣ) : F), ?_⟩
  have hAA : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsc : ∀ M : Matrix (Fin n) (Fin n) F, M * scalar (Fin n) (c : F) = (c : F) • M := by
    intro M
    rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, mul_one]
  have key : (A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * scalar (Fin n) (c : F) *
        (A : Matrix (Fin n) (Fin n) F) =
      (c : F) • ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) := by
    rw [hsc, Matrix.smul_mul,
      Matrix.mul_assoc ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)), hAA,
      Matrix.mul_one]
  calc (A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)
      = ((c⁻¹ : Fˣ) : F) • ((c : F) • ((A : Matrix (Fin n) (Fin n) F) *
          (B : Matrix (Fin n) (Fin n) F))) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = ((c⁻¹ : Fˣ) : F) • ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * scalar (Fin n) (c : F) *
            (A : Matrix (Fin n) (Fin n) F)) := by
        rw [key]
    _ = ((c⁻¹ : Fˣ) : F) • ((B : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) := by
        rw [← h1]

theorem entry_of_mul_diagonal {A : Matrix (Fin n) (Fin n) F} {d : Fin n → F} {c : F}
    (h : A * diagonal d = c • (diagonal d * A)) (k l : Fin n) :
    A k l * d l = c * d k * A k l := by
  have := congrFun (congrFun h k) l
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc] using this

theorem exists_ne_ne (hn : 3 ≤ n) (a b : Fin n) : ∃ j : Fin n, j ≠ a ∧ j ≠ b := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b} := by
    intro x _
    by_cases hxa : x = a
    · simp [hxa]
    · simp [h x hxa]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le a ({b} : Finset (Fin n))
  rw [Finset.card_univ, Fintype.card_fin] at h1
  rw [Finset.card_singleton] at h2
  omega

theorem exists_two_ne_ne (hn : 4 ≤ n) (a b : Fin n) :
    ∃ j₁ j₂ : Fin n, j₁ ≠ j₂ ∧ j₁ ≠ a ∧ j₁ ≠ b ∧ j₂ ≠ a ∧ j₂ ≠ b := by
  obtain ⟨j₁, h1a, h1b⟩ := exists_ne_ne (by omega) a b
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, j₁} := by
    intro x _
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    by_cases hx1 : x = j₁
    · simp [hx1]
    exact absurd (h j₁ x (Ne.symm hx1) h1a h1b hxa) hxb
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le a ({b, j₁} : Finset (Fin n))
  have h3 := Finset.card_insert_le b ({j₁} : Finset (Fin n))
  rw [Finset.card_univ, Fintype.card_fin] at h1
  rw [Finset.card_singleton] at h3
  omega

@[expose] def dij (ζ : Fˣ) (i j : Fin n) : Fin n → Fˣ := Pi.mulSingle i ζ * Pi.mulSingle j ζ⁻¹

theorem dij_left (ζ : Fˣ) {i j : Fin n} (hij : i ≠ j) : dij ζ i j i = ζ := by
  simp [dij, Pi.mulSingle_apply, hij]

theorem dij_right (ζ : Fˣ) {i j : Fin n} (hij : i ≠ j) : dij ζ i j j = ζ⁻¹ := by
  simp [dij, Pi.mulSingle_apply, Ne.symm hij]

theorem dij_other (ζ : Fˣ) {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) : dij ζ i j k = 1 := by
  simp [dij, Pi.mulSingle_apply, hki, hkj]

theorem prod_dij (ζ : Fˣ) (i j : Fin n) : ∏ k, dij ζ i j k = 1 := by
  simp [dij, Finset.prod_mul_distrib]

theorem dij_mem_zpowers (ζ : Fˣ) (i j k : Fin n) : dij ζ i j k ∈ Subgroup.zpowers ζ := by
  simp only [dij, Pi.mul_apply, Pi.mulSingle_apply]
  refine mul_mem ?_ ?_
  · split_ifs
    · exact Subgroup.mem_zpowers ζ
    · exact one_mem _
  · split_ifs
    · exact inv_mem (Subgroup.mem_zpowers ζ)
    · exact one_mem _

theorem eq_of_dij_eq (ζ : Fˣ) (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1) {i j k : Fin n} (hij : i ≠ j)
    (h : dij ζ i j k = ζ) : k = i := by
  by_contra hki
  by_cases hkj : k = j
  · subst hkj
    rw [dij_right ζ hij] at h
    apply hζ2
    rw [sq]
    calc ζ * ζ = ζ * ζ⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel ζ
  · rw [dij_other ζ hki hkj] at h
    exact hζ1 h.symm

@[expose] def diagSL (d : Fin n → Fˣ) (hd : ∏ k, d k = 1) : SpecialLinearGroup (Fin n) F :=
  ⟨diagonal fun k => (d k : F), by rw [det_diagonal, ← Units.coe_prod, hd, Units.val_one]⟩

theorem coe_diagSL (d : Fin n → Fˣ) (hd : ∏ k, d k = 1) :
    ((diagSL d hd : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun k => (d k : F) := rfl

@[expose] def permSL (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    SpecialLinearGroup (Fin n) F :=
  ⟨σ.permMatrix F, by rw [det_permutation, hσ]; simp⟩

theorem coe_permSL (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    ((permSL σ hσ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = σ.permMatrix F :=
  rfl

section Monomial

variable {A : Matrix (Fin n) (Fin n) F}

theorem eq_of_ne_zero_of_ne_zero (hn : 3 ≤ n) {ζ : Fˣ} (hζ : ζ ≠ 1)
    (h : ∀ i j : Fin n, i ≠ j → ∃ c : F, A * diagonal (fun k => (dij ζ i j k : F)) =
      c • (diagonal (fun k => (dij ζ i j k : F)) * A))
    {k₁ k₂ l : Fin n} (h1 : A k₁ l ≠ 0) (h2 : A k₂ l ≠ 0) : k₁ = k₂ := by
  by_contra hk
  obtain ⟨j, hj1, hj2⟩ := exists_ne_ne hn k₁ k₂
  obtain ⟨c, hc⟩ := h k₁ j (Ne.symm hj1)
  have e1 := entry_of_mul_diagonal hc k₁ l
  have e2 := entry_of_mul_diagonal hc k₂ l
  rw [dij_left ζ (Ne.symm hj1)] at e1
  rw [dij_other ζ (Ne.symm hk) (Ne.symm hj2), Units.val_one, mul_one] at e2
  have f1 : ((dij ζ k₁ j l : Fˣ) : F) = c * ζ := by
    apply mul_left_cancel₀ h1
    rw [e1]
    ring
  have f2 : ((dij ζ k₁ j l : Fˣ) : F) = c := by
    apply mul_left_cancel₀ h2
    rw [e2]
    ring
  have hc0 : c ≠ 0 := by
    rw [← f2]
    exact Units.ne_zero _
  apply hζ
  apply Units.ext
  rw [Units.val_one]
  apply mul_left_cancel₀ hc0
  rw [← f1, f2, mul_one]

theorem exists_ne_zero_of_det_ne_zero (hA : A.det ≠ 0) (l : Fin n) : ∃ k, A k l ≠ 0 := by
  by_contra h
  push Not at h
  apply hA
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨Pi.single l 1, fun h0 => by simpa using congrFun h0 l, ?_⟩
  rw [Matrix.mulVec_single_one]
  ext k
  exact h k

theorem eq_of_rows_eq (hA : A.det ≠ 0)
    (huniq : ∀ k₁ k₂ l : Fin n, A k₁ l ≠ 0 → A k₂ l ≠ 0 → k₁ = k₂) {k l₁ l₂ : Fin n}
    (h1 : A k l₁ ≠ 0) (h2 : A k l₂ ≠ 0) : l₁ = l₂ := by
  by_contra hl
  apply hA
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨Pi.single l₁ (A k l₂) - Pi.single l₂ (A k l₁), fun h0 => ?_, ?_⟩
  · have := congrFun h0 l₁
    simp [Pi.single_apply, hl] at this
    exact h2 this
  · ext k'
    simp only [Matrix.mulVec_sub, Matrix.mulVec_single, Pi.sub_apply, Pi.zero_apply,
      Pi.smul_apply, Matrix.col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    by_cases hk' : k' = k
    · subst hk'
      ring
    · have a1 : A k' l₁ = 0 := by
        by_contra h'
        exact hk' (huniq _ _ _ h' h1)
      have a2 : A k' l₂ = 0 := by
        by_contra h'
        exact hk' (huniq _ _ _ h' h2)
      rw [a1, a2]
      ring

end Monomial

open Fin.NatCast

@[expose] def cyc (m L : ℕ) : Equiv.Perm (Fin (m * L)) :=
  (finProdFinEquiv : Fin m × Fin L ≃ Fin (m * L)).permCongr
    (Equiv.prodCongrRight fun _ => finRotate L)

theorem cyc_apply (m L : ℕ) (j : Fin m) (r : Fin L) :
    cyc m L (finProdFinEquiv (j, r)) = finProdFinEquiv (j, finRotate L r) := by
  simp [cyc, Equiv.permCongr_apply]

theorem sign_cyc (m L' : ℕ) (hL : Even L') : Equiv.Perm.sign (cyc m (L' + 1)) = 1 := by
  rw [cyc, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrRight, sign_finRotate]
  simp [hL.neg_one_pow]

theorem cyc_pow_apply (m L' : ℕ) (j : Fin m) (r : Fin (L' + 1)) (s : ℕ) :
    (cyc m (L' + 1) ^ s) (finProdFinEquiv (j, r)) = finProdFinEquiv (j, r + (s : Fin (L' + 1))) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, cyc_apply, finRotate_succ_apply, Nat.cast_succ,
      add_assoc]

theorem cyc_pow_card (m L' : ℕ) : cyc m (L' + 1) ^ (L' + 1) = 1 := by
  ext x
  obtain ⟨⟨j, r⟩, rfl⟩ := (finProdFinEquiv : Fin m × Fin (L' + 1) ≃ _).surjective x
  rw [cyc_pow_apply, Fin.natCast_self, add_zero]
  rfl

theorem cyc_apply_ne (m L' : ℕ) (hL : 1 ≤ L') (x : Fin (m * (L' + 1))) : cyc m (L' + 1) x ≠ x := by
  obtain ⟨⟨j, r⟩, rfl⟩ := (finProdFinEquiv : Fin m × Fin (L' + 1) ≃ _).surjective x
  rw [cyc_apply, finRotate_succ_apply]
  intro h
  have h2 := congrArg Prod.snd ((finProdFinEquiv : Fin m × Fin (L' + 1) ≃ _).injective h)
  simp only at h2
  have h1 : (1 : Fin (L' + 1)) = 0 := by
    have := congrArg (fun x => x - r) h2
    simpa using this
  rw [Fin.one_eq_zero_iff] at h1
  omega

theorem prod_eq_pow_of_succ {G : Type*} [CommGroup G] {L' : ℕ} (hL : Even L')
    (f : Fin (L' + 1) → G) (c : G) (h : ∀ r, f (r + 1) = c * f r) :
    ∏ r, f r = f 0 ^ (L' + 1) := by
  have hpow : ∀ s : ℕ, f (s : Fin (L' + 1)) = c ^ s * f 0 := by
    intro s
    induction s with
    | zero => simp
    | succ s ih => rw [Nat.cast_succ, h, ih, pow_succ', mul_assoc]
  have hc : c ^ (L' + 1) = 1 := by
    have h0 := hpow (L' + 1)
    rw [Fin.natCast_self] at h0
    exact mul_eq_right.mp h0.symm
  obtain ⟨w, hw⟩ := hL
  have hsum : ∑ r : Fin (L' + 1), (r : ℕ) = (L' + 1) * w := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (L' + 1)]
    have h2 := Finset.sum_range_id_mul_two (L' + 1)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    rw [h2, Nat.add_sub_cancel, hw]
    ring
  calc ∏ r, f r = ∏ r : Fin (L' + 1), c ^ (r : ℕ) * f 0 := by
        refine Finset.prod_congr rfl fun r _ => ?_
        rw [← hpow, Fin.cast_val_eq_self]
    _ = c ^ (∑ r : Fin (L' + 1), (r : ℕ)) * f 0 ^ (L' + 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
    _ = f 0 ^ (L' + 1) := by rw [hsum, pow_mul, hc, one_pow, one_mul]

theorem exists_pow_eq_prod_mem {G : Type*} [CommGroup G] {m N : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime m N) (H : Subgroup G) (τ : Fin m → G) (hτH : ∀ j, τ j ∈ H) (u : G)
    (hτ : ∀ j, τ j ^ N = u) : ∃ z ∈ H, z ^ m = ∏ j, τ j := by
  set j0 : Fin m := ⟨0, hm⟩
  set ε : G := ∏ j, τ j * (τ j0)⁻¹ with hε
  have hεH : ε ∈ H := Subgroup.prod_mem H fun j _ => mul_mem (hτH j) (inv_mem (hτH j0))
  have hεN : ε ^ N = 1 := by
    rw [hε, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [mul_pow, inv_pow, hτ, hτ, mul_inv_cancel]
  have hprod : ∏ j, τ j = τ j0 ^ m * ε := by
    rw [hε, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_comm, inv_mul_cancel_right]
  have hb : (1 : ℤ) = m * Nat.gcdA m N + N * Nat.gcdB m N := by
    have h1 := Nat.gcd_eq_gcd_ab m N
    rw [hcop.gcd_eq_one, Nat.cast_one] at h1
    exact h1
  refine ⟨τ j0 * ε ^ (Nat.gcdA m N), mul_mem (hτH j0) (zpow_mem hεH _), ?_⟩
  rw [hprod, mul_pow]
  congr 1
  rw [← zpow_natCast, ← _root_.zpow_mul]
  have h2 : ε ^ ((N : ℤ) * Nat.gcdB m N) = 1 := by
    rw [_root_.zpow_mul, zpow_natCast, hεN, _root_.one_zpow]
  calc ε ^ (Nat.gcdA m N * (m : ℤ))
      = ε ^ (Nat.gcdA m N * (m : ℤ)) * ε ^ ((N : ℤ) * Nat.gcdB m N) := by rw [h2, mul_one]
    _ = ε ^ ((m : ℤ) * Nat.gcdA m N + N * Nat.gcdB m N) := by
        rw [← _root_.zpow_add, mul_comm (Nat.gcdA m N : ℤ)]
    _ = ε := by rw [← hb, zpow_one]

theorem conjAut_mem_inner_of_det {A : GL (Fin n) F} {z : Fˣ}
    (h : (A : Matrix (Fin n) (Fin n) F).det = (z : F) ^ n) :
    conjAut n F A ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n F) := by
  set B : GL (Fin n) F := GeneralLinearGroup.scalar (Fin n) z⁻¹ * A with hBdef
  have hB : (B : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [hBdef, Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, h, ← mul_pow, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_pow]
  let g : SpecialLinearGroup (Fin n) F := ⟨B, hB⟩
  have hAB : A = GeneralLinearGroup.scalar (Fin n) z * SpecialLinearGroup.toGL g := by
    apply Units.ext
    rw [Units.val_mul]
    change (A : Matrix (Fin n) (Fin n) F) = _ * (B : Matrix (Fin n) (Fin n) F)
    rw [hBdef, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mul]
  rw [hAB, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  exact ⟨proj n F g, rfl⟩

theorem sign_eq_one_of_commute_fin_three : ∀ π τ : Equiv.Perm (Fin 3), (∀ x, τ x ≠ x) →
    π * τ = τ * π → Equiv.Perm.sign π = 1 := by
  decide

theorem sign_eq_one_of_commute_of_eq_three {n : ℕ} (h : n = 3) (π τ : Equiv.Perm (Fin n))
    (hτ : ∀ x, τ x ≠ x) (hc : π * τ = τ * π) : Equiv.Perm.sign π = 1 := by
  subst h
  exact sign_eq_one_of_commute_fin_three π τ hτ hc

theorem perm_eq_one_of_four_le (h4 : 4 ≤ n) {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1)
    (π : Equiv.Perm (Fin n))
    (hrel : ∀ i j : Fin n, i ≠ j → ∃ c : F, ∀ l, ((dij ζ i j l : Fˣ) : F) =
      c * ((dij ζ i j (π l) : Fˣ) : F)) : π = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨j, hji, -⟩ := exists_ne_ne (by omega) i i
  obtain ⟨c, hc⟩ := hrel i j (Ne.symm hji)
  have hc1 : c = 1 := by
    obtain ⟨l₁, l₂, h12, h1i, h1j, h2i, h2j⟩ := exists_two_ne_ne h4 i j
    have e1 := hc l₁
    have e2 := hc l₂
    rw [dij_other ζ h1i h1j, Units.val_one] at e1
    rw [dij_other ζ h2i h2j, Units.val_one] at e2
    by_contra hc1
    have hd : ∀ l, (1 : F) = c * ((dij ζ i j (π l) : Fˣ) : F) → π l = i ∨ π l = j := by
      intro l hl
      by_contra hlij
      push Not at hlij
      rw [dij_other ζ hlij.1 hlij.2, Units.val_one, mul_one] at hl
      exact hc1 hl.symm
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_mul] at e1
      exact one_ne_zero e1
    have hdeq : ((dij ζ i j (π l₁) : Fˣ) : F) = ((dij ζ i j (π l₂) : Fˣ) : F) :=
      mul_left_cancel₀ hc0 (e1.symm.trans e2)
    have hij : i ≠ j := Ne.symm hji
    have key : π l₁ = π l₂ := by
      rcases hd l₁ e1 with ha | ha <;> rcases hd l₂ e2 with hb | hb
      · rw [ha, hb]
      · exfalso
        rw [ha, hb, dij_left ζ hij, dij_right ζ hij] at hdeq
        have hz : ζ = ζ⁻¹ := Units.ext hdeq
        apply hζ2
        rw [sq]
        calc ζ * ζ = ζ * ζ⁻¹ := congrArg (ζ * ·) hz
          _ = 1 := mul_inv_cancel ζ
      · exfalso
        rw [ha, hb, dij_left ζ hij, dij_right ζ hij] at hdeq
        have hz : ζ = ζ⁻¹ := (Units.ext hdeq).symm
        apply hζ2
        rw [sq]
        calc ζ * ζ = ζ * ζ⁻¹ := congrArg (ζ * ·) hz
          _ = 1 := mul_inv_cancel ζ
      · rw [ha, hb]
    exact h12 (π.injective key)
  have h1 := hc (π.symm i)
  rw [hc1, one_mul, Equiv.apply_symm_apply, dij_left ζ (Ne.symm hji)] at h1
  have h' : π.symm i = i := eq_of_dij_eq ζ hζ1 hζ2 (Ne.symm hji) (Units.ext h1)
  rw [Equiv.Perm.one_apply]
  calc π i = π (π.symm i) := by rw [h']
    _ = i := Equiv.apply_symm_apply π i

open Fin.NatCast in
theorem det_eq_pow_of_matrix {p m L' : ℕ} [hp : Fact p.Prime] (hL : Even L') (hL1 : 1 ≤ L')
    (hm : ¬ p ∣ m) (hn : 3 ≤ m * (L' + 1)) {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1)
    (M : Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) (hdet : M.det ≠ 0)
    (hD' : ∀ i j : Fin (m * (L' + 1)), i ≠ j → ∃ c : F, M * diagonal (fun k => (dij ζ i j k : F)) =
      c • (diagonal (fun k => (dij ζ i j k : F)) * M))
    (hP' : ∃ c' : F, M * Equiv.Perm.permMatrix F (cyc m (L' + 1)) =
      c' • (Equiv.Perm.permMatrix F (cyc m (L' + 1)) * M))
    (hpel : ∃ (K : ℕ) (u : F), M ^ (p ^ K) = scalar (Fin (m * (L' + 1))) u) :
    ∃ (π : Equiv.Perm (Fin (m * (L' + 1)))) (t : Fin (m * (L' + 1)) → Fˣ) (z : Fˣ),
      M = diagonal (fun k => (t k : F)) * Equiv.Perm.permMatrix F π.symm ∧
      z ∈ Subgroup.closure (Set.range t) ∧ M.det = (z : F) ^ (m * (L' + 1)) := by
  set σ := cyc m (L' + 1) with hσdef
  have huniq : ∀ k₁ k₂ l, M k₁ l ≠ 0 → M k₂ l ≠ 0 → k₁ = k₂ := fun _ _ _ h1 h2 =>
    eq_of_ne_zero_of_ne_zero hn hζ1 hD' h1 h2
  choose r hr using exists_ne_zero_of_det_ne_zero hdet
  have hr_uniq : ∀ k l, M k l ≠ 0 → k = r l := fun k l h => huniq k (r l) l h (hr l)
  have hr_inj : Function.Injective r := fun l₁ l₂ h =>
    eq_of_rows_eq hdet huniq (hr l₁) (h ▸ hr l₂)
  set π : Equiv.Perm (Fin (m * (L' + 1))) :=
    Equiv.ofBijective r (Finite.injective_iff_bijective.1 hr_inj) with hπdef
  have hπ : ∀ l, π l = r l := fun _ => rfl
  have hπ0 : ∀ k l, k ≠ π l → M k l = 0 := fun k l hk => by
    by_contra h
    exact hk (hr_uniq k l h)
  set t : Fin (m * (L' + 1)) → F := fun k => M k (π.symm k) with htdef
  have ht0 : ∀ k, t k ≠ 0 := fun k => by
    have := hr (π.symm k)
    rw [← hπ, Equiv.apply_symm_apply] at this
    exact this
  have hfac : M = diagonal t * Equiv.Perm.permMatrix F π.symm := by
    ext k l
    rw [PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, id, Equiv.symm_symm, diagonal_apply]
    by_cases hk : k = π l
    · rw [if_pos hk, htdef]
      simp only
      rw [hk, Equiv.symm_apply_apply]
    · rw [if_neg hk]
      exact hπ0 k l hk
  have hrel : ∀ i j : Fin (m * (L' + 1)), i ≠ j → ∃ c : F, ∀ l, ((dij ζ i j l : Fˣ) : F) =
      c * ((dij ζ i j (π l) : Fˣ) : F) := fun i j hij => by
    obtain ⟨c, hc⟩ := hD' i j hij
    refine ⟨c, fun l => ?_⟩
    have e := entry_of_mul_diagonal hc (π l) l
    have hne : M (π l) l ≠ 0 := by rw [hπ]; exact hr l
    apply mul_left_cancel₀ hne
    rw [e]
    ring
  obtain ⟨c', hc'⟩ := hP'
  have hent : ∀ k l, M k l = c' * M (σ k) (σ l) := fun k l => by
    have := congrFun (congrFun hc' k) (σ l)
    rw [PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, id,
      Equiv.symm_apply_apply, Matrix.smul_apply, PEquiv.toMatrix_toPEquiv_mul,
      Matrix.submatrix_apply, id, smul_eq_mul] at this
    exact this
  have hcomm : ∀ k, π.symm (σ k) = σ (π.symm k) := fun k => by
    have h1 := hent k (π.symm k)
    have h2 : M (σ k) (σ (π.symm k)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact ht0 k h1
    have h3 := hr_uniq _ _ h2
    rw [← hπ] at h3
    rw [h3, Equiv.symm_apply_apply]
  have htσ : ∀ k, t k = c' * t (σ k) := fun k => by
    show M k (π.symm k) = c' * M (σ k) (π.symm (σ k))
    rw [hent k (π.symm k), hcomm k]
  have hc'0 : c' ≠ 0 := fun h0 => ht0 ⟨0, by omega⟩ (by rw [htσ, h0, zero_mul])
  set tu : Fin (m * (L' + 1)) → Fˣ := fun k => Units.mk0 (t k) (ht0 k) with htudef
  have htu : ∀ k, ((tu k : Fˣ) : F) = t k := fun k => rfl
  set cu : Fˣ := Units.mk0 c' hc'0 with hcudef
  have htuσ : ∀ k, tu k = cu * tu (σ k) := fun k => Units.ext (by
    rw [Units.val_mul, htu, htu, hcudef, Units.val_mk0]
    exact htσ k)
  set e : Fin m × Fin (L' + 1) ≃ Fin (m * (L' + 1)) := finProdFinEquiv with hedef
  set τ : Fin m → Fˣ := fun j => tu (e (j, 0)) with hτdef
  have hτH : ∀ j, τ j ∈ Subgroup.closure (Set.range tu) := fun j =>
    Subgroup.subset_closure ⟨e (j, 0), rfl⟩
  have hprod_t : ∏ k, tu k = (∏ j, τ j) ^ (L' + 1) := by
    rw [← Finset.prod_pow, ← e.prod_comp, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    refine prod_eq_pow_of_succ hL (fun r => tu (e (j, r))) cu⁻¹ fun r => ?_
    show tu (e (j, r + 1)) = cu⁻¹ * tu (e (j, r))
    have h1 := htuσ (e (j, r))
    rw [hσdef, hedef, cyc_apply, finRotate_succ_apply] at h1
    rw [h1, inv_mul_cancel_left]
  have hcase : (Equiv.Perm.sign π = 1 ∧
      ∃ z ∈ Subgroup.closure (Set.range tu), z ^ m = ∏ j, τ j) := by
    have hcases : m * (L' + 1) = 3 ∨ 4 ≤ m * (L' + 1) := by
      by_cases h3 : m * (L' + 1) = 3
      · exact Or.inl h3
      · exact Or.inr (Nat.succ_le_of_lt (lt_of_le_of_ne hn (Ne.symm h3)))
    rcases hcases with h3 | h4
    · have hL2' : 2 ≤ L' := by obtain ⟨w, hw⟩ := hL; omega
      have hm1 : m = 1 := by
        rcases m with _ | _ | m
        · simp at h3
        · rfl
        · exfalso
          nlinarith
      refine ⟨?_, ⟨∏ j, τ j, Subgroup.prod_mem _ fun j _ => hτH j,
        (congrArg (fun k => (∏ j, τ j) ^ k) hm1).trans (pow_one _)⟩⟩
      have hπσ : π * σ = σ * π := by
        ext x
        simp only [Equiv.Perm.mul_apply]
        have := hcomm (π x)
        rw [Equiv.symm_apply_apply] at this
        rw [← this, Equiv.apply_symm_apply]
      exact sign_eq_one_of_commute_of_eq_three h3 π σ (cyc_apply_ne m L' hL1) hπσ
    · have hπ1 : π = 1 := perm_eq_one_of_four_le h4 hζ1 hζ2 π hrel
      refine ⟨by rw [hπ1, map_one], ?_⟩
      obtain ⟨K, u, hu⟩ := hpel
      have hdiag : M = diagonal t := by
        rw [hfac, hπ1, show (1 : Equiv.Perm (Fin (m * (L' + 1)))).symm = 1 from rfl,
          Matrix.permMatrix_one, Matrix.mul_one]
      have hu0 : u ≠ 0 := by
        intro h0
        have h1 := congrFun (congrFun hu ⟨0, by omega⟩) ⟨0, by omega⟩
        rw [hdiag, diagonal_pow, diagonal_apply_eq, h0, scalar_apply, diagonal_apply_eq] at h1
        exact ht0 _ (pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero) |>.1 h1)
      have hpow : ∀ k, tu k ^ p ^ K = Units.mk0 u hu0 := fun k => Units.ext (by
        have h1 := congrFun (congrFun hu k) k
        rw [hdiag, diagonal_pow, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at h1
        rw [Units.val_pow_eq_pow_val, htu, Units.val_mk0]
        exact h1)
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, zero_mul] at hn
          omega
        · exact h0
      have hcop : Nat.Coprime m (p ^ K) :=
        Nat.Coprime.pow_right K (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm))
      exact exists_pow_eq_prod_mem hm0 hcop _ τ hτH _ fun j => hpow _
  obtain ⟨hsign, z, hzH, hz⟩ := hcase
  refine ⟨π, tu, z, hfac, hzH, ?_⟩
  rw [hfac, det_mul, det_diagonal, det_permutation, Equiv.Perm.sign_symm, hsign]
  have h1 : ∏ k, t k = ((∏ k, tu k : Fˣ) : F) := by
    rw [Units.coe_prod]
    rfl
  rw [h1, hprod_t, ← hz, ← pow_mul]
  simp

theorem det_eq_pow_of_fix [Finite F] {p m L' : ℕ} [hp : Fact p.Prime] (hL : Even L') (hL1 : 1 ≤ L')
    (hm : ¬ p ∣ m) (hn : 3 ≤ m * (L' + 1)) {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1)
    (A : GL (Fin (m * (L' + 1))) F)
    (hD : ∀ i j : Fin (m * (L' + 1)), i ≠ j →
      conjAut _ F A (proj _ F (diagSL (dij ζ i j) (prod_dij ζ i j))) =
        proj _ F (diagSL (dij ζ i j) (prod_dij ζ i j)))
    (hP : conjAut _ F A (proj _ F (permSL (cyc m (L' + 1)) (sign_cyc m L' hL))) =
        proj _ F (permSL (cyc m (L' + 1)) (sign_cyc m L' hL)))
    (hpel : ∃ K : ℕ, conjAut _ F A ^ p ^ K = 1) :
    ∃ z : Fˣ, (A : Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F).det =
      (z : F) ^ (m * (L' + 1)) := by
  have hdet : (A : Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hD' : ∀ i j : Fin (m * (L' + 1)), i ≠ j → ∃ c : F,
      (A : Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) *
        diagonal (fun k => (dij ζ i j k : F)) =
      c • (diagonal (fun k => (dij ζ i j k : F)) *
        (A : Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F)) := fun i j hij => by
    have := exists_mul_eq_smul_of_conjAut_fix (hD i j hij)
    rwa [coe_diagSL] at this
  have hP' := exists_mul_eq_smul_of_conjAut_fix hP
  rw [coe_permSL] at hP'
  have hpel' : ∃ (K : ℕ) (u : F), (A : Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) ^ (p ^ K) =
      scalar (Fin (m * (L' + 1))) u := by
    obtain ⟨K, hK⟩ := hpel
    have hA1 : conjAut _ F (A ^ p ^ K) * fieldAut _ F 1 = 1 := by
      rw [map_one, mul_one, map_pow, hK]
    obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 hA1
    refine ⟨K, u, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← hu, GeneralLinearGroup.coe_scalar]
  obtain ⟨-, -, z, -, -, hz⟩ := det_eq_pow_of_matrix hL hL1 hm hn hζ1 hζ2 _ hdet hD' hP' hpel'
  exact ⟨z, hz⟩

section Rsub

open CFSG.LocalAnalysis.RankThreeTheoremC (NineSubgroup.dglHom NineSubgroup.coe_dglHom)

@[expose] def permGL (σ : Equiv.Perm (Fin n)) : GL (Fin n) F :=
  ⟨σ.permMatrix F, (σ⁻¹).permMatrix F,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

theorem permMatrix_pow (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    (σ ^ k).permMatrix F = (σ.permMatrix F) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Matrix.permMatrix_mul, ih, pow_succ']

theorem permGL_pow (σ : Equiv.Perm (Fin n)) (k : ℕ) : (permGL (F := F) σ) ^ k = permGL (σ ^ k) :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; exact (permMatrix_pow σ k).symm)

theorem permGL_inv (σ : Equiv.Perm (Fin n)) : (permGL (F := F) σ)⁻¹ = permGL σ⁻¹ :=
  Units.ext rfl

theorem permGL_conj_dglHom (σ : Equiv.Perm (Fin n)) (a : Fin n → Fˣ) :
    permGL σ * NineSubgroup.dglHom n a * (permGL σ)⁻¹ = NineSubgroup.dglHom n (a ∘ σ) := by
  apply Units.ext
  change σ.permMatrix F * diagonal (fun i => (a i : F)) * (σ⁻¹).permMatrix F =
    diagonal fun i => (a (σ i) : F)
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext k l
  simp only [Matrix.submatrix_apply, id, diagonal_apply, Equiv.Perm.inv_def, Equiv.symm_symm,
    EmbeddingLike.apply_eq_iff_eq]

@[expose] noncomputable def diagZeta (ζ : Fˣ) : Subgroup (GL (Fin n) F) :=
  (Subgroup.pi Set.univ fun _ => Subgroup.zpowers ζ).map (NineSubgroup.dglHom n)

theorem isPGroup_diagZeta {p : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1) : IsPGroup p (diagZeta (n := n) ζ) := by
  refine IsPGroup.map (fun x => ⟨1, ?_⟩) _
  apply Subtype.ext
  funext i
  obtain ⟨k, hk⟩ := ((Subgroup.mem_pi Set.univ).1 x.2) i (Set.mem_univ i)
  simp only [pow_one, Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
  rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hζ,
    _root_.one_zpow]

theorem conj_mem_diagZeta (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) {g : GL (Fin n) F}
    (hg : g ∈ diagZeta ζ) : permGL σ * g * (permGL σ)⁻¹ ∈ diagZeta ζ := by
  obtain ⟨a, ha, rfl⟩ := hg
  rw [permGL_conj_dglHom]
  refine ⟨a ∘ σ, (Subgroup.mem_pi Set.univ).2 fun i _ =>
    ((Subgroup.mem_pi Set.univ).1 ha) (σ i) (Set.mem_univ _), rfl⟩

theorem permGL_mem_normalizer (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) :
    permGL σ ∈ Subgroup.normalizer (diagZeta (F := F) (n := n) ζ : Set (GL (Fin n) F)) := by
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem_diagZeta ζ σ hh, fun hh => ?_⟩
  have := conj_mem_diagZeta ζ σ⁻¹ hh
  rwa [← permGL_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one] at this

@[expose] noncomputable def Rgl (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) : Subgroup (GL (Fin n) F) :=
  diagZeta ζ ⊔ Subgroup.zpowers (permGL σ)

theorem isPGroup_Rgl {p v : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ^ (p ^ v) = 1) : IsPGroup p (Rgl (F := F) ζ σ) := by
  refine IsPGroup.to_sup_of_normal_left' (isPGroup_diagZeta hζ) ?_
    ((Subgroup.zpowers_le).2 (permGL_mem_normalizer ζ σ))
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine ⟨v, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, permGL_pow, hσ,
    show permGL (F := F) (1 : Equiv.Perm (Fin n)) = 1 from Units.ext Matrix.permMatrix_one,
    _root_.one_zpow]

@[expose] noncomputable def Rproj (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) : Subgroup (projectiveSL n F) :=
  ((Rgl (F := F) ζ σ).comap SpecialLinearGroup.toGL).map (proj n F)

theorem isPGroup_Rproj {p v : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ^ (p ^ v) = 1) : IsPGroup p (Rproj (F := F) ζ σ) :=
  ((isPGroup_Rgl hζ hσ).comap_of_injective _ SpecialLinearGroup.toGL_injective).map _

theorem proj_diagSL_mem_Rproj (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) (d : Fin n → Fˣ)
    (hd : ∏ k, d k = 1) (hdz : ∀ k, d k ∈ Subgroup.zpowers ζ) :
    proj n F (diagSL d hd) ∈ Rproj ζ σ := by
  refine ⟨diagSL d hd, ?_, rfl⟩
  show SpecialLinearGroup.toGL (diagSL d hd) ∈ Rgl ζ σ
  refine (le_sup_left : diagZeta ζ ≤ Rgl ζ σ) ⟨d, (Subgroup.mem_pi Set.univ).2 fun k _ => hdz k, ?_⟩
  exact Units.ext rfl

theorem proj_permSL_mem_Rproj (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) (hσ1 : Equiv.Perm.sign σ = 1) :
    proj n F (permSL σ hσ1) ∈ Rproj ζ σ := by
  refine ⟨permSL σ hσ1, ?_, rfl⟩
  show SpecialLinearGroup.toGL (permSL σ hσ1) ∈ Rgl ζ σ
  have : SpecialLinearGroup.toGL (permSL (F := F) σ hσ1) = permGL σ := Units.ext rfl
  rw [this]
  exact (le_sup_right : Subgroup.zpowers (permGL σ) ≤ Rgl ζ σ) (Subgroup.mem_zpowers _)

end Rsub

theorem mem_inner_of_fix_sylow_of_hom {G U : Type*} [Group G] [Finite G] [Group U] {p : ℕ}
    [Fact p.Prime] (c : U →* MulAut G) (hconj : ∀ g : G, ∃ u : U, c u = MulAut.conj g)
    {R : Subgroup G} (hR : IsPGroup p R)
    (hcore : ∀ A : U, (∃ K : ℕ, c A ^ p ^ K = 1) → (∀ x ∈ R, c A x = x) →
      c A ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G)
    (P : Sylow p G) (A : U) (hA : ∃ K : ℕ, c A ^ p ^ K = 1)
    (hfix : ∀ x ∈ (P : Subgroup G), c A x = x) :
    c A ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  obtain ⟨u, hu⟩ := hconj g
  have hB : c (u * A * u⁻¹) = MulAut.conj g * c A * (MulAut.conj g)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hu]
  have hBp : ∃ K : ℕ, c (u * A * u⁻¹) ^ p ^ K = 1 := by
    obtain ⟨K, hK⟩ := hA
    exact ⟨K, by rw [hB, conj_pow, hK, mul_one, mul_inv_cancel]⟩
  have hBfix : ∀ x ∈ R, c (u * A * u⁻¹) x = x := by
    intro x hx
    have hxS : x ∈ (S : Subgroup G) := hRS hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
    rw [hB, MulAut.mul_apply, MulAut.mul_apply]
    have h1 := hfix _ hxS
    rw [MulAut.smul_def] at h1
    rw [h1, MulAut.apply_inv_self]
  have hBin := hcore _ hBp hBfix
  have hconjg : MulAut.conj g ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := ⟨g, rfl⟩
  have hA' : c A = (MulAut.conj g)⁻¹ * c (u * A * u⁻¹) * MulAut.conj g := by
    rw [hB]
    group
  rw [hA']
  exact mul_mem (mul_mem (inv_mem hconjg) hBin) hconjg

theorem exists_decomp {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n ≠ 0) (hpn : p ∣ n) :
    ∃ m L' v : ℕ, n = m * (L' + 1) ∧ ¬ p ∣ m ∧ Even L' ∧ 1 ≤ L' ∧ L' + 1 = p ^ v := by
  set v := n.factorization p
  have hv : 0 < v := hp.factorization_pos_of_dvd hn hpn
  have hLodd : Odd (p ^ v) := (hp.odd_of_ne_two hp2).pow
  have hLp : p ≤ p ^ v := Nat.le_self_pow hv.ne' p
  refine ⟨n / p ^ v, p ^ v - 1, v, ?_, Nat.not_dvd_ordCompl hp hn, ?_, ?_, ?_⟩
  · have h1 := Nat.ordProj_mul_ordCompl_eq_self n p
    have h2 : p ^ v - 1 + 1 = p ^ v := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
      (pow_ne_zero _ hp.ne_zero))
    rw [h2, mul_comm]
    exact h1.symm
  · obtain ⟨k, hk⟩ := hLodd
    exact ⟨k, by omega⟩
  · have := hp.two_le
    have : 3 ≤ p := by omega
    omega
  · exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero))

theorem hasNormalPComplement_fixerAut_projectiveSL [Finite F] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (hpn : p ∣ n) (hpq : p ∣ Nat.card F - 1)
    (hZ : Subgroup.center (projectiveSL n F) = ⊥) (P : Sylow p (projectiveSL n F)) :
    CFSG.HasNormalPComplement p
      ↥(Input185.fixerAut (P : Subgroup (projectiveSL n F))) := by
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [Nat.card_units]; exact hpq)
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ
    exact hp.out.one_lt.ne hζ
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    have h2 := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2)
  obtain ⟨m, L', v, rfl, hm, hL, hL1, hLv⟩ := exists_decomp hp.out hp2 (by omega) hpn
  set σ := cyc m (L' + 1) with hσdef
  have hσpow : σ ^ (p ^ v) = 1 := by rw [← hLv]; exact cyc_pow_card m L'
  have hR := isPGroup_Rproj (F := F) hζp hσpow
  have hcore : ∀ A : GL (Fin (m * (L' + 1))) F, (∃ K : ℕ, conjAut _ F A ^ p ^ K = 1) →
      (∀ x ∈ Rproj ζ σ, conjAut _ F A x = x) →
        conjAut _ F A ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (projectiveSL (m * (L' + 1)) F) := by
    intro A hA hfixR
    obtain ⟨z, hz⟩ := det_eq_pow_of_fix hL hL1 hm hn hζ1 hζ2 A
      (fun i j _ => hfixR _ (proj_diagSL_mem_Rproj ζ σ _ _ (dij_mem_zpowers ζ i j)))
      (hfixR _ (proj_permSL_mem_Rproj ζ σ _)) hA
    exact conjAut_mem_inner_of_det hz
  have hAb : CFSG.HasNormalPComplement p (Abelianization (MulAut (projectiveSL (m * (L' + 1)) F))) :=
    InputsMisc5.hasNormalPComplement_of_pElements_central fun g _ =>
      Subgroup.mem_center_iff.2 fun h => mul_comm h g
  refine hasNormalPComplement_fixerAut_of_hom hZ P Abelianization.of hAb fun α hαp hα1 hαfix => ?_
  have hαc : α ∈ commutator (MulAut (projectiveSL (m * (L' + 1)) F)) := by
    rw [← Abelianization.ker_of]
    exact hα1
  obtain ⟨A, rfl⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.commutator_le_range_conjAut hn hαc
  refine mem_inner_of_fix_sylow_of_hom (conjAut _ F) (fun g => ?_) hR hcore P A hαp hαfix
  obtain ⟨g', rfl⟩ := proj_surjective _ F g
  exact ⟨SpecialLinearGroup.toGL g', conjAut_toGL g'⟩

end LinearPSL

namespace UnitaryPSU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag LinearPSL
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.RankThreeTheoremC (NineSubgroup.dglHom NineSubgroup.coe_dglHom)

variable {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F) {n : ℕ}

theorem exists_mul_eq_smul_of_fix {C : Matrix (Fin n) (Fin n) F} {A : primeFormUnitary h C}
    {g : gramSU h C}
    (hfix : primeFormConjHom h C A (g : primeFormP h C) = (g : primeFormP h C)) :
    ∃ c : F, ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      c • (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  rw [primeFormConjHom_mk, QuotientGroup.eq] at hfix
  obtain ⟨c, -, -, hc⟩ := hfix
  set x : gramSU h C := ⟨(A : GL (Fin n) F) * g * (A : GL (Fin n) F)⁻¹,
    conj_mem_gramSU h C A.2 g.2⟩ with hxdef
  have h1 : (g : GL (Fin n) F) = (x : GL (Fin n) F) * GeneralLinearGroup.scalar (Fin n) c := by
    rw [← hc, ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hs : GeneralLinearGroup.scalar (Fin n) c * (A : GL (Fin n) F) =
      (A : GL (Fin n) F) * GeneralLinearGroup.scalar (Fin n) c :=
    ((commute_scalar c (A : GL (Fin n) F)).eq).symm
  have h2 : (A : GL (Fin n) F) * g =
      g * (A : GL (Fin n) F) * GeneralLinearGroup.scalar (Fin n) c⁻¹ := by
    rw [map_inv]
    calc (A : GL (Fin n) F) * g = ((A : GL (Fin n) F) * g * (A : GL (Fin n) F)⁻¹) *
          (A : GL (Fin n) F) := by group
      _ = (x : GL (Fin n) F) * (A : GL (Fin n) F) := rfl
      _ = (x : GL (Fin n) F) * GeneralLinearGroup.scalar (Fin n) c * (A : GL (Fin n) F) *
          (GeneralLinearGroup.scalar (Fin n) c)⁻¹ := by
        rw [mul_assoc (x : GL (Fin n) F), hs]
        group
      _ = g * (A : GL (Fin n) F) * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ := by rw [← h1]
  refine ⟨((c⁻¹ : Fˣ) : F), ?_⟩
  have h3 := congrArg (fun y : GL (Fin n) F => (y : Matrix (Fin n) (Fin n) F)) h2
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h3
  rw [h3, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem dglHom_mem_gramSU {d : Fin n → Fˣ} (hd : ∏ k, d k = 1) (hN : ∀ k, h.norm (d k : F) = 1) :
    NineSubgroup.dglHom n d ∈ gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_one, Matrix.mul_one, NineSubgroup.coe_dglHom, diagonal_map (map_zero _),
      diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    have := hN k
    rw [UnitaryFieldData.norm] at this
    rw [mul_comm]
    exact this
  · rw [NineSubgroup.coe_dglHom, det_diagonal, ← Units.coe_prod, hd, Units.val_one]

theorem permGL_mem_gramSU (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    permGL σ ∈ gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  have hmap : (σ.permMatrix F).map h.bar = σ.permMatrix F := by
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · change ((σ.permMatrix F).map h.bar)ᵀ * ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      σ.permMatrix F = ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [hmap, Units.val_one, Matrix.mul_one, transpose_permMatrix, ← Matrix.permMatrix_mul,
      mul_inv_cancel, Matrix.permMatrix_one]
  · change (σ.permMatrix F).det = 1
    rw [det_permutation, hσ]
    simp

theorem primeFormConjHom_scalar {C : Matrix (Fin n) (Fin n) F} (c : Fˣ)
    (hc : GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h C) :
    primeFormConjHom h C ⟨GeneralLinearGroup.scalar (Fin n) c, hc⟩ = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change GeneralLinearGroup.scalar (Fin n) c * (g : GL (Fin n) F) *
    (GeneralLinearGroup.scalar (Fin n) c)⁻¹ = g
  rw [← (commute_scalar c (g : GL (Fin n) F)).eq, mul_inv_cancel_right]

theorem primeFormConjHom_mem_inner_of_det
    {A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)} {z : Fˣ}
    (hz : h.norm (z : F) = 1)
    (hdet : (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).det = (z : F) ^ n) :
    primeFormConjHom h _ A ∈ inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  have hzi : h.norm ((z⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hz, inv_one]
  have hsz := scalar_mem_primeFormUnitary_one (n := n) h hz
  have hszi := scalar_mem_primeFormUnitary_one (n := n) h hzi
  set B : GL (Fin n) F := GeneralLinearGroup.scalar (Fin n) z⁻¹ * A with hBdef
  have hBU : B ∈ primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    mul_mem hszi A.2
  have hBdet : (B : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [hBdef, Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, hdet, ← mul_pow, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_pow]
  set s : gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := ⟨B, hBU, hBdet⟩ with hsdef
  have hA : A = ⟨GeneralLinearGroup.scalar (Fin n) z, hsz⟩ * ⟨(s : GL (Fin n) F), s.2.1⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    change (A : GL (Fin n) F) = GeneralLinearGroup.scalar (Fin n) z * B
    rw [hBdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hA, map_mul, primeFormConjHom_scalar, one_mul, primeFormConjHom_eq_conj]
  exact ⟨_, rfl⟩

theorem norm_eq_one_of_monomial {A : GL (Fin n) F}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    {π : Equiv.Perm (Fin n)} {t : Fin n → Fˣ}
    (hM : (A : Matrix (Fin n) (Fin n) F) = diagonal (fun k => (t k : F)) *
      Equiv.Perm.permMatrix F π.symm) (k : Fin n) : h.norm (t k : F) = 1 := by
  have hent : ∀ j l, (A : Matrix (Fin n) (Fin n) F) j l = if j = π l then (t j : F) else 0 := by
    intro j l
    rw [hM, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, id, Equiv.symm_symm,
      diagonal_apply]
  have hU0 := mem_primeFormUnitary.1 hA
  rw [Units.val_one, Matrix.mul_one] at hU0
  have hU := congrFun (congrFun hU0 (π.symm k)) (π.symm k)
  rw [Matrix.one_apply_eq, Matrix.mul_apply] at hU
  rw [Finset.sum_eq_single k] at hU
  · rw [Matrix.transpose_apply, Matrix.map_apply, hent, Equiv.apply_symm_apply, if_pos rfl] at hU
    rw [UnitaryFieldData.norm, mul_comm]
    exact hU
  · intro j _ hjk
    rw [hent j (π.symm k), Equiv.apply_symm_apply, if_neg hjk, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

@[expose] noncomputable def RprojU (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) :
    Subgroup (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
  ((Rgl ζ σ).comap (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).subtype).map
    (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n))

theorem isPGroup_RprojU {p v : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ^ (p ^ v) = 1) : IsPGroup p (RprojU h ζ σ) :=
  ((isPGroup_Rgl hζ hσ).comap_of_injective _ (Subgroup.subtype_injective _)).map _

theorem mk_dglHom_mem_RprojU (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) (d : Fin n → Fˣ)
    (hd : ∏ k, d k = 1) (hN : ∀ k, h.norm (d k : F) = 1) (hdz : ∀ k, d k ∈ Subgroup.zpowers ζ) :
    ((⟨NineSubgroup.dglHom n d, dglHom_mem_gramSU h hd hN⟩ :
      gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
        primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) ∈ RprojU h ζ σ :=
  ⟨⟨_, dglHom_mem_gramSU h hd hN⟩, (le_sup_left : diagZeta ζ ≤ Rgl ζ σ)
    ⟨d, (Subgroup.mem_pi Set.univ).2 fun k _ => hdz k, rfl⟩, rfl⟩

theorem mk_permGL_mem_RprojU (ζ : Fˣ) (σ : Equiv.Perm (Fin n)) (hσ1 : Equiv.Perm.sign σ = 1) :
    ((⟨permGL σ, permGL_mem_gramSU h σ hσ1⟩ :
      gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
        primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) ∈ RprojU h ζ σ :=
  ⟨⟨_, permGL_mem_gramSU h σ hσ1⟩,
    (le_sup_right : Subgroup.zpowers (permGL σ) ≤ Rgl ζ σ) (Subgroup.mem_zpowers _), rfl⟩

theorem hasNormalPComplement_fixerAut_primeFormP {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hpn : p ∣ n) (hpq : p ∣ ℓ ^ f + 1)
    (hZ : Subgroup.center (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = ⊥)
    (P : Sylow p (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))) :
    CFSG.HasNormalPComplement p ↥(Input185.fixerAut
      (P : Subgroup (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))) := by
  haveI := h.finite
  obtain ⟨ζ', hζ'⟩ := exists_prime_orderOf_dvd_card' (G := (Units.map h.normHom).ker) p
    (by rw [(unitary_field_norm h).2.2.1]; exact hpq)
  set ζ : Fˣ := (ζ' : Fˣ) with hζdef
  have hζ : orderOf ζ = p := by rw [hζdef, Subgroup.orderOf_coe, hζ']
  have hzN : ∀ x ∈ Subgroup.zpowers ζ, h.norm (x : F) = 1 := fun x hx =>
    (h.mem_ker_normUnits).1 ((Subgroup.zpowers_le.2 ζ'.2) hx)
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact hp.out.one_lt.ne hζ
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζ] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h3)
  obtain ⟨m, L', v, rfl, hm, hL, hL1, hLv⟩ := exists_decomp hp.out hp2 (by omega) hpn
  set σ := cyc m (L' + 1) with hσdef
  have hσpow : σ ^ (p ^ v) = 1 := by rw [← hLv]; exact cyc_pow_card m L'
  have hR := isPGroup_RprojU h hζp hσpow
  set c := primeFormConjHom h ((1 : GL (Fin (m * (L' + 1))) F) :
    Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) with hcdef
  have hconj : ∀ g : primeFormP h ((1 : GL (Fin (m * (L' + 1))) F) :
      Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F), ∃ u, c u = MulAut.conj g := by
    intro g
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨⟨s, s.2.1⟩, primeFormConjHom_eq_conj h _ s⟩
  have hcore : ∀ A, (∃ K : ℕ, c A ^ p ^ K = 1) → (∀ x ∈ RprojU h ζ σ, c A x = x) →
      c A ∈ inner (primeFormP h ((1 : GL (Fin (m * (L' + 1))) F) :
        Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F)) := by
    intro A hA hfixR
    have hdet : (((A : GL (Fin (m * (L' + 1))) F) :
        Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F)).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    have hD' : ∀ i j : Fin (m * (L' + 1)), i ≠ j → ∃ c₀ : F,
        ((A : GL (Fin (m * (L' + 1))) F) : Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) *
          diagonal (fun k => (dij ζ i j k : F)) =
        c₀ • (diagonal (fun k => (dij ζ i j k : F)) *
          ((A : GL (Fin (m * (L' + 1))) F) :
            Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F)) := fun i j _ => by
      have hN : ∀ k, h.norm (dij ζ i j k : F) = 1 := fun k => hzN _ (dij_mem_zpowers ζ i j k)
      have := exists_mul_eq_smul_of_fix h
        (hfixR _ (mk_dglHom_mem_RprojU h ζ σ (dij ζ i j) (prod_dij ζ i j) hN (dij_mem_zpowers ζ i j)))
      exact this
    have hP' := exists_mul_eq_smul_of_fix h (hfixR _ (mk_permGL_mem_RprojU h ζ σ (sign_cyc m L' hL)))
    have hpel : ∃ (K : ℕ) (u : F), ((A : GL (Fin (m * (L' + 1))) F) :
        Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) ^ (p ^ K) =
          scalar (Fin (m * (L' + 1))) u := by
      obtain ⟨K, hK⟩ := hA
      have h1 : c (A ^ p ^ K) = 1 := by rw [map_pow, hK]
      obtain ⟨u, -, hu⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn h1
      refine ⟨K, u, ?_⟩
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hu, GeneralLinearGroup.coe_scalar]
    obtain ⟨π, t, z, hfac, hzH, hz⟩ := det_eq_pow_of_matrix hL hL1 hm hn hζ1 hζ2 _ hdet hD' hP' hpel
    have htN : ∀ k, t k ∈ (Units.map h.normHom).ker := fun k =>
      (h.mem_ker_normUnits).2 (norm_eq_one_of_monomial h A.2 hfac k)
    have hzN' : h.norm (z : F) = 1 :=
      (h.mem_ker_normUnits).1 ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 htN) hzH)
    exact primeFormConjHom_mem_inner_of_det h hzN' hz
  have hAb : CFSG.HasNormalPComplement p (Abelianization (MulAut (primeFormP h
      ((1 : GL (Fin (m * (L' + 1))) F) : Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F)))) :=
    InputsMisc5.hasNormalPComplement_of_pElements_central fun g _ =>
      Subgroup.mem_center_iff.2 fun x => mul_comm x g
  refine hasNormalPComplement_fixerAut_of_hom hZ P Abelianization.of hAb fun α hαp hα1 hαfix => ?_
  have hαc : α ∈ commutator (MulAut (primeFormP h ((1 : GL (Fin (m * (L' + 1))) F) :
      Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F))) := by
    rw [← Abelianization.ker_of]
    exact hα1
  obtain ⟨A, rfl⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.commutator_le_primeFormD h hn hq hαc
  exact mem_inner_of_fix_sylow_of_hom c hconj hR hcore P A hαp hαfix

end UnitaryPSU

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem resOddPSL_holds : ResOddPSL := by
  intro K _ _ hs hnab n ℓ f hcl p hp hp2 hpn hpq P hP _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hcl⟩ : CFSG.Blueprint.LieModel K .PSL n ℓ f)
  haveI : Finite (projectiveSL n F) := Finite.of_equiv K e.toEquiv
  have hn2 : 2 ≤ n := hcl.1.2.2.1
  have hn : 3 ≤ n := by
    have hle := Nat.le_of_dvd (by omega) hpn
    have h2 := hp.two_le
    omega
  have hZ : Subgroup.center (projectiveSL n F) = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e,
      InputsMisc5.center_eq_bot_of_simple hs hnab, Subgroup.map_bot]
  have hP' := InputsMisc5.fusionIsSylowIn_map_of_surjective (f := (e : K →* projectiveSL n F))
    e.surjective hP
  let S : Sylow p (projectiveSL n F) :=
    ⟨P.map (e : K →* projectiveSL n F), hP'.2.1, fun {Q} hQ hle => hP'.2.2 Q le_top hQ hle⟩
  refine hasNormalPComplement_fixerAut_of_mulEquiv e P ?_
  exact LinearPSL.hasNormalPComplement_fixerAut_projectiveSL hp2 hn hpn (by rw [hF]; exact hpq) hZ S

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem resOddPSU_holds : ResOddPSU := by
  intro K _ _ hs hnab n ℓ f hcl p hp hp2 hpn hpq P hP _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, F, _, _, hF, ⟨e₀⟩⟩ := hcl
  have h : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨e₁⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n) (K := F))
  let e : K ≃* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    e₀.trans ((CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm.trans e₁.symm)
  haveI : Finite (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    Finite.of_equiv K e.toEquiv
  have hZ : Subgroup.center (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e,
      InputsMisc5.center_eq_bot_of_simple hs hnab, Subgroup.map_bot]
  have hP' := InputsMisc5.fusionIsSylowIn_map_of_surjective
    (f := (e : K →* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))) e.surjective hP
  let S : Sylow p (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    ⟨P.map (e : K →* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)), hP'.2.1,
      fun {Q} hQ hle => hP'.2.2 Q le_top hQ hle⟩
  refine hasNormalPComplement_fixerAut_of_mulEquiv e P ?_
  exact UnitaryPSU.hasNormalPComplement_fixerAut_primeFormP h hp2 hn3
    (fun ⟨h3, h2⟩ => hq (by rw [h3, h2])) hpn hpq hZ S

section AssemblyNonab

theorem input7_10_1ResOddNonab_of_exceptional (hE6 : ResOddE6) (hTwE6 : ResOddTwE6)
    (hD4 : ResOddD4) : InputsMisc5.Input7_10_1ResOddNonab :=
  input7_10_1ResOddNonab_of_residues resOddPSL_holds resOddPSU_holds hE6 hTwE6 hD4

theorem input7_10_1ResOdd_of_exceptional (hE6 : ResOddE6) (hTwE6 : ResOddTwE6) (hD4 : ResOddD4)
    (hLie : ResOddTrivialLie) : InputsMisc5.Input7_10_1ResOdd :=
  input7_10_1ResOdd_of_nonab (input7_10_1ResOddNonab_of_exceptional hE6 hTwE6 hD4)
    (resOddTrivial_of_lie hLie)

end AssemblyNonab

section Assembly

theorem input7_10_1_of_exceptional (hE6 : ResOddE6) (hTwE6 : ResOddTwE6) (hD4 : ResOddD4)
    (hLie : ResOddTrivialLie) : Input185.Input7_10_1 :=
  InputsMisc5.input7_10_1_of_res
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.kFactInnerAction_holds
    input7_10_1ResTwo_holds (input7_10_1ResOdd_of_exceptional hE6 hTwE6 hD4 hLie)

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7
