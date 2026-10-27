module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSigMat
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeX
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial (LinearFlag.unitriangular)

section Matrices

variable {F : Type*} [Field F]

theorem sigSL_ext {n : ℕ} {R : Type*} [CommRing R] {A B : SpecialLinearGroup (Fin n) R}
    (h : (A : Matrix (Fin n) (Fin n) R) = (B : Matrix (Fin n) (Fin n) R)) : A = B :=
  Subtype.ext h

theorem apply_last_castSucc_eq_zero_of_isColRadical {M R : Matrix (Fin 4) (Fin 4) F} (j : Fin 3)
    (hR : IsColRadical R) (h : R * M = M * colRadMat (Pi.single j 1)) :
    M (Fin.last 3) j.castSucc = 0 := by
  have h1 := congrFun (congrFun h (Fin.last 3)) (Fin.last 3)
  have hL : (R * M) (Fin.last 3) (Fin.last 3) = M (Fin.last 3) (Fin.last 3) := by
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [hR.lastRow, zero_mul, Finset.sum_const_zero, hR.2, one_mul, zero_add]
  have hE := isColRadical_colRadMat (F := F) (Pi.single j 1)
  have hEv := colRadVec_colRadMat (F := F) (Pi.single j 1)
  have hRr : (M * colRadMat (Pi.single j 1) : Matrix (Fin 4) (Fin 4) F) (Fin.last 3)
      (Fin.last 3) =
      M (Fin.last 3) j.castSucc + M (Fin.last 3) (Fin.last 3) := by
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, hE.2, mul_one]
    congr 1
    have h2 : ∀ k : Fin 3, colRadMat (F := F) (Pi.single j 1) k.castSucc (Fin.last 3) =
        (Pi.single j (1 : F) : Fin 3 → F) k := fun k => congrFun hEv k
    simp only [h2, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  rw [hL, hRr] at h1
  linear_combination -h1

theorem smul_colRadVec_of_mul_eq_map (σ : F →+* F) {M c : Matrix (Fin 4) (Fin 4) F}
    (hM : IsColRadical M) (h : M * c = c * M.map σ) :
    c (Fin.last 3) (Fin.last 3) • colRadVec M =
      c.submatrix Fin.castSucc Fin.castSucc *ᵥ fun i => σ (colRadVec M i) := by
  funext i
  have h2 : ∀ x' : Fin 3, (i.castSucc = x'.castSucc) = (i = x') :=
    fun x' => propext Fin.castSucc_inj
  have h1 := congrFun (congrFun h i.castSucc) (Fin.last 3)
  have hL : (M * c) i.castSucc (Fin.last 3) =
      c i.castSucc (Fin.last 3) + colRadVec M i * c (Fin.last 3) (Fin.last 3) := by
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [hM.1, one_apply, ite_mul, one_mul, zero_mul, h2, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rfl
  have hR : (c * M.map σ) i.castSucc (Fin.last 3) =
      (c.submatrix Fin.castSucc Fin.castSucc *ᵥ fun i => σ (colRadVec M i)) i +
        c i.castSucc (Fin.last 3) := by
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.map_apply, hM.2, map_one, mul_one]
    rfl
  rw [hL, hR] at h1
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination h1

theorem corner_eq_one_of_mul_eq_map (σ : F →+* F) (hσ : ∀ x, σ x = x ^ 2)
    {M c : Matrix (Fin 4) (Fin 4) F} (hM : ∀ j : Fin 3, M (Fin.last 3) j.castSucc = 0)
    (hc : ∀ j : Fin 3, c (Fin.last 3) j.castSucc = 0) (hc0 : c (Fin.last 3) (Fin.last 3) ≠ 0)
    (hM0 : M (Fin.last 3) (Fin.last 3) ≠ 0) (h : M * c = c * M.map σ) :
    M (Fin.last 3) (Fin.last 3) = 1 := by
  have h1 := congrFun (congrFun h (Fin.last 3)) (Fin.last 3)
  rw [mul_apply_last_last hM, mul_apply_last_last hc, Matrix.map_apply, hσ] at h1
  have h2 : c (Fin.last 3) (Fin.last 3) * M (Fin.last 3) (Fin.last 3) *
      (M (Fin.last 3) (Fin.last 3) - 1) = 0 := by linear_combination -h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero hc0 hM0)
  · linear_combination h3

theorem map_mem_unitriangular {n : ℕ} (σ : F →+* F) {u : SpecialLinearGroup (Fin n) F}
    (hu : u ∈ LinearFlag.unitriangular n F) :
    Matrix.SpecialLinearGroup.map σ u ∈ LinearFlag.unitriangular n F :=
  ⟨fun i j hij => by
      change σ ((u : Matrix (Fin n) (Fin n) F) i j) = 0
      rw [hu.1 i j hij, map_zero],
    fun i => by
      change σ ((u : Matrix (Fin n) (Fin n) F) i i) = 1
      rw [hu.2 i, map_one]⟩

end Matrices

section Embed

variable {F : Type} [Field F]

theorem leviEmbed_mem_unitriangular {A : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ LinearFlag.unitriangular 3 F) : leviEmbed F A ∈ LinearFlag.unitriangular 4 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases with
    | last => rw [leviEmbed_apply_last_left, one_apply_ne (ne_of_gt hij)]
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
      | cast j =>
        rw [leviEmbed_apply_castSucc]
        exact hA.1 i j (Fin.castSucc_lt_castSucc_iff.1 hij)
  · induction i using Fin.lastCases with
    | last => rw [leviEmbed_apply_last_left, one_apply_eq]
    | cast i => rw [leviEmbed_apply_castSucc, hA.2 i]

theorem map_leviEmbed (σ : F →+* F) (A : SpecialLinearGroup (Fin 3) F) :
    Matrix.SpecialLinearGroup.map σ (leviEmbed F A) =
      leviEmbed F (Matrix.SpecialLinearGroup.map σ A) := by
  ext i j
  change σ ((leviEmbed F A : Matrix (Fin 4) (Fin 4) F) i j) =
    (leviEmbed F (Matrix.SpecialLinearGroup.map σ A) : Matrix (Fin 4) (Fin 4) F) i j
  induction i using Fin.lastCases with
  | last =>
    rw [leviEmbed_apply_last_left, leviEmbed_apply_last_left, one_apply]
    split_ifs <;> simp
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [leviEmbed_apply_last_right, leviEmbed_apply_last_right, one_apply]
      split_ifs <;> simp
    | cast j =>
      rw [leviEmbed_apply_castSucc, leviEmbed_apply_castSucc]
      rfl

theorem map_self_transvection_one {n : ℕ} (σ : F →+* F) {i j : Fin n} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.transvection hij (1 : F)) =
      Matrix.SpecialLinearGroup.transvection hij 1 := by
  ext k l
  change σ (((Matrix.SpecialLinearGroup.transvection hij (1 : F) : SpecialLinearGroup (Fin n) F) :
    Matrix (Fin n) (Fin n) F) k l) = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp

end Embed

section Twist

variable {G : Type*} [Group G] {F : Type} [Field F]
variable {N W₁ S₀ : Subgroup G} {p : G → SpecialLinearGroup (Fin 4) F} {b : G → Fin 4 → F}

theorem IsFieldModuleData.twist_mul_map_eq_one (h : IsFieldModuleData N W₁ S₀ p b)
    {σ : F →+* F} (hσσ : ∀ x, σ (σ x) = x) {t : G} (ht2 : t * t = 1)
    (htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁) {c : SpecialLinearGroup (Fin 4) F}
    (hbt : ∀ w ∈ W₁, b (t * w * t⁻¹) =
      (fun k => σ (b w k)) ᵥ* ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    (c : Matrix (Fin 4) (Fin 4) F) * (c : Matrix (Fin 4) (Fin 4) F).map σ = 1 := by
  have hcic : ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (c : Matrix (Fin 4) (Fin 4) F) = 1 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_inv_mul_coe c
  have hcci : (c : Matrix (Fin 4) (Fin 4) F) *
      ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  generalize ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = ci at hbt hcic hcci
  have hσv : ∀ v : Fin 4 → F, (fun k => σ (σ (v k))) = v := fun v => funext fun k => hσσ _
  have hr : ∀ r : Fin 4 → F, r ᵥ* (ci.map σ * ci) = r := by
    intro r
    obtain ⟨w, hw, rfl⟩ := h.surjB r
    have hw' := htW₁ w hw
    have h1 := hbt _ hw'
    have htt : t * (t * w * t⁻¹) * t⁻¹ = w := by
      calc t * (t * w * t⁻¹) * t⁻¹ = (t * t) * w * (t * t)⁻¹ := by group
        _ = w := by rw [ht2]; group
    rw [htt, hbt w hw] at h1
    have h2 : (fun k => σ (((fun k => σ (b w k)) ᵥ* ci) k)) =
        (fun k => σ (σ (b w k))) ᵥ* ci.map σ := by
      funext k
      exact RingHom.map_vecMul σ ci _ k
    rw [h2, hσv, vecMul_vecMul] at h1
    exact h1.symm
  have hM : ci.map σ * ci = 1 := by
    ext i j
    have h1 := congrFun (hr (Pi.single i 1)) j
    rw [single_one_vecMul] at h1
    rw [show (ci.map σ * ci) i j = (ci.map σ * ci).row i j from rfl, h1, Pi.single_apply,
      one_apply]
    simp only [eq_comm]
  have h1 : ci.map σ = c := by
    calc ci.map σ = ci.map σ * (ci * (c : Matrix (Fin 4) (Fin 4) F)) := by
          rw [hcic, Matrix.mul_one]
      _ = (ci.map σ * ci) * c := by rw [Matrix.mul_assoc]
      _ = c := by rw [hM, Matrix.one_mul]
  have h2 : (c : Matrix (Fin 4) (Fin 4) F).map σ = ci := by
    rw [← h1, Matrix.map_map]
    ext i j
    exact hσσ _
  rw [h2, hcci]

theorem IsFieldModuleData.conj_mem_unitriangular_of_twist (h : IsFieldModuleData N W₁ S₀ p b)
    {σ : F →+* F} {t : G} (htS₀ : t ∈ normalizer (S₀ : Set G)) {c : SpecialLinearGroup (Fin 4) F}
    (hpt : ∀ x ∈ N, t * x * t⁻¹ ∈ N → (p (t * x * t⁻¹) : Matrix (Fin 4) (Fin 4) F) =
      (c : Matrix (Fin 4) (Fin 4) F) * (p x : Matrix (Fin 4) (Fin 4) F).map σ *
        ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    {u : SpecialLinearGroup (Fin 4) F} (hu : u ∈ LinearFlag.unitriangular 4 F)
    (huσ : Matrix.SpecialLinearGroup.map σ u = u) :
    c * u * c⁻¹ ∈ LinearFlag.unitriangular 4 F ∧ c⁻¹ * u * c ∈ LinearFlag.unitriangular 4 F := by
  obtain ⟨s, hs, hsu⟩ := h.exists_mem_sZero hu
  have hsN := h.sZero_le hs
  have huσ' : (u : Matrix (Fin 4) (Fin 4) F).map σ = u := congrArg Subtype.val huσ
  constructor
  · have hts : t * s * t⁻¹ ∈ S₀ := (mem_normalizer_iff.1 htS₀ s).1 hs
    have h1 := hpt s hsN (h.sZero_le hts)
    have h2 : p (t * s * t⁻¹) = c * u * c⁻¹ := by
      apply sigSL_ext
      rw [h1, hsu, huσ', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [← h2]
    exact (h.mem_sZero_iff _ (h.sZero_le hts)).1 hts
  · have hts : t⁻¹ * s * t⁻¹⁻¹ ∈ S₀ := (mem_normalizer_iff.1 (inv_mem htS₀) s).1 hs
    rw [inv_inv] at hts
    have htt : t * (t⁻¹ * s * t) * t⁻¹ = s := by group
    have h1 := hpt (t⁻¹ * s * t) (h.sZero_le hts) (by rw [htt]; exact hsN)
    rw [htt, hsu] at h1
    have h2 : c⁻¹ * u * c = Matrix.SpecialLinearGroup.map σ (p (t⁻¹ * s * t)) := by
      apply sigSL_ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1]
      change _ = (p (t⁻¹ * s * t) : Matrix (Fin 4) (Fin 4) F).map σ
      have hcic : ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (c : Matrix (Fin 4) (Fin 4) F) = 1 :=
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_inv_mul_coe c
      simp only [← Matrix.mul_assoc, hcic, Matrix.one_mul]
      rw [Matrix.mul_assoc, hcic, Matrix.mul_one]
    rw [h2]
    exact map_mem_unitriangular σ ((h.mem_sZero_iff _ (h.sZero_le hts)).1 hts)

end Twist

section Untwist

variable {G : Type*} [Group G] [Finite G] {F : Type} [Field F]
variable {N W₁ W₂ S₀ : Subgroup G} {p : G → Matrix.SpecialLinearGroup (Fin 4) F}
  {b : G → Fin 4 → F}

theorem leviBlock_apply_of_mem_unitriangular {v : Matrix.SpecialLinearGroup (Fin 4) F}
    (hv : v ∈ LinearFlag.unitriangular 4 F) {i j : Fin 3} (hji : j ≤ i) :
    (v : Matrix (Fin 4) (Fin 4) F) i.castSucc j.castSucc = (1 : Matrix (Fin 3) (Fin 3) F) i j := by
  rcases hji.lt_or_eq with h | h
  · rw [hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 h), one_apply_ne (ne_of_gt h)]
  · subst h
    rw [hv.2, one_apply_eq]

theorem frob_facts_of_card_four (hF : Nat.card F = 4) {σ : F →+* F} (hσ : ∀ x, σ x = x ^ 2) :
    (∀ x, σ (σ x) = x) ∧ (∃ x, σ x ≠ x) ∧ ∀ x, σ x = x → x = 0 ∨ x = 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  refine ⟨fun x => ?_, ?_, fun x hx => ?_⟩
  · rw [hσ, hσ, ← pow_mul]
    have h := FiniteField.pow_card x
    rw [hq] at h
    exact h
  · obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_of_card_four hF
    refine ⟨ω, fun h => ?_⟩
    rw [hσ] at h
    have h2 : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hω0 h3
    · exact hω1 (by linear_combination h3)
  · rw [hσ] at hx
    have h2 : x * (x - 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (by linear_combination h3)

theorem IsFieldModuleData.exists_untwist (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) {σ : F →+* F}
    (hσ : ∀ x, σ x = x ^ 2) {t : G} (ht2 : t * t = 1) (htS₀ : t ∈ normalizer (S₀ : Set G))
    (htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁) (htW₂ : ∀ w ∈ W₂, t * w * t⁻¹ ∈ W₂)
    {c : Matrix.SpecialLinearGroup (Fin 4) F}
    (hpt : ∀ x ∈ N, t * x * t⁻¹ ∈ N → (p (t * x * t⁻¹) : Matrix (Fin 4) (Fin 4) F) =
      (c : Matrix (Fin 4) (Fin 4) F) * (p x : Matrix (Fin 4) (Fin 4) F).map σ *
        ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hbt : ∀ w ∈ W₁, b (t * w * t⁻¹) = (fun k => σ (b w k)) ᵥ*
      ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    (∀ j : Fin 3, (c : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0) ∧
      (c : Matrix (Fin 4) (Fin 4) F) * (c : Matrix (Fin 4) (Fin 4) F).map σ = 1 ∧
      (c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc *
          ((c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc).map σ = 1 ∧
      ∃ A Ai : Matrix (Fin 3) (Fin 3) F, A.IsUpperTriangular ∧ A * Ai = 1 ∧
        A = (c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc * A.map σ := by
  obtain ⟨hσσ, hσ1, -⟩ := frob_facts_of_card_four hF hσ
  have htZ : ∀ z ∈ W₁ ⊓ W₂, t * z * t⁻¹ ∈ W₁ ⊓ W₂ := fun z hz =>
    mem_inf.2 ⟨htW₁ z (mem_inf.1 hz).1, htW₂ z (mem_inf.1 hz).2⟩
  have hc : ∀ j : Fin 3, (c : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0 :=
    h.lastRow_of_twist hF hW₂S₀ hS₀W₂ hW₂c hZ hbt htZ
  have hcσ := h.twist_mul_map_eq_one hσσ ht2 htW₁ hbt
  set ci : Matrix (Fin 4) (Fin 4) F :=
    ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hcidef
  have hcci : (c : Matrix (Fin 4) (Fin 4) F) * ci = 1 := by
    rw [hcidef, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hcic : ci * (c : Matrix (Fin 4) (Fin 4) F) = 1 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_inv_mul_coe c
  have hci : ∀ j : Fin 3, ci (Fin.last 3) j.castSucc = 0 := (lastRow_of_mul_eq_one hcci hc).1
  set B := (c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc with hBdef
  set Bi := ci.submatrix Fin.castSucc Fin.castSucc with hBidef
  have hBBi : B * Bi = 1 := by
    rw [hBdef, hBidef, ← submatrix_castSucc_mul_of_lastRow hci, hcci, submatrix_castSucc_one]
  have hcσP : ∀ j : Fin 3, ((c : Matrix (Fin 4) (Fin 4) F).map σ) (Fin.last 3) j.castSucc = 0 :=
    fun j => by rw [Matrix.map_apply, hc j, map_zero]
  have hBσ : B * B.map σ = 1 := by
    rw [hBdef, ← Matrix.submatrix_map, ← submatrix_castSucc_mul_of_lastRow hcσP, hcσ,
      submatrix_castSucc_one]
  have hconj : ∀ (i j : Fin 3) (hij : i < j),
      c * leviEmbed F (Matrix.SpecialLinearGroup.transvection hij.ne (1 : F)) * c⁻¹ ∈
          LinearFlag.unitriangular 4 F ∧
        c⁻¹ * leviEmbed F (Matrix.SpecialLinearGroup.transvection hij.ne (1 : F)) * c ∈
          LinearFlag.unitriangular 4 F := by
    intro i j hij
    refine h.conj_mem_unitriangular_of_twist htS₀ hpt (leviEmbed_mem_unitriangular
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.transvection_mem_unitriangular hij 1)) ?_
    rw [map_leviEmbed, map_self_transvection_one]
  have hblock : ∀ (i j : Fin 3) (hij : i < j),
      ((c * leviEmbed F (Matrix.SpecialLinearGroup.transvection hij.ne (1 : F)) * c⁻¹ :
          Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).submatrix
            Fin.castSucc Fin.castSucc = B * transvection i j (1 : F) * Bi ∧
      ((c⁻¹ * leviEmbed F (Matrix.SpecialLinearGroup.transvection hij.ne (1 : F)) * c :
          Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).submatrix
            Fin.castSucc Fin.castSucc = Bi * transvection i j (1 : F) * B := by
    intro i j hij
    have hu := leviEmbed_mem_leviQ (F := F) (Matrix.SpecialLinearGroup.transvection hij.ne (1 : F))
    have hub := leviBlock_leviEmbed (F := F) (Matrix.SpecialLinearGroup.transvection hij.ne (1 : F))
    rw [Matrix.SpecialLinearGroup.transvection_coe] at hub
    constructor
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        submatrix_castSucc_mul_of_lastRow hci, submatrix_castSucc_mul_of_lastRow hu.1, hub]
      rfl
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        submatrix_castSucc_mul_of_lastRow hc, submatrix_castSucc_mul_of_lastRow hu.1, hub]
      rfl
  have hBu : B.IsUpperTriangular := by
    refine isUpperTriangular_of_conj_transvection hBBi (fun i => ?_) (fun i => ?_) (fun j => ?_)
    · rw [← (hblock 0 1 (by decide)).2, submatrix_apply]
      exact leviBlock_apply_of_mem_unitriangular (hconj 0 1 (by decide)).2 (Fin.zero_le i)
    · rw [← (hblock 1 2 (by decide)).2, submatrix_apply]
      exact leviBlock_apply_of_mem_unitriangular (hconj 1 2 (by decide)).2 (Fin.zero_le i)
    · rw [← (hblock 1 2 (by decide)).1, submatrix_apply]
      by_cases hj : j = 2
      · subst hj
        exact leviBlock_apply_of_mem_unitriangular (hconj 1 2 (by decide)).1 le_rfl
      · have hj2 : j < 2 := lt_of_le_of_ne (Fin.le_last j) hj
        rw [(hconj 1 2 (by decide)).1.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hj2),
          one_apply_ne (ne_of_gt hj2)]
  obtain ⟨A, Ai, hAu, hAAi, -, hA⟩ := exists_isUpperTriangular_eq_mul_map σ hσσ hσ1 hBu hBσ
  exact ⟨hc, hcσ, hBσ, A, Ai, hAu, hAAi, hA⟩

end Untwist

section Image

variable {G : Type*} [Group G] [Finite G] {F : Type} [Field F] [CharP F 2]
variable {N W₁ W₂ S₀ : Subgroup G} {p : G → Matrix.SpecialLinearGroup (Fin 4) F}
  {b : G → Fin 4 → F}

theorem IsFieldModuleData.exists_mem_of_map_eq (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) {σ : F →+* F}
    (hσ : ∀ x, σ x = x ^ 2) {t : G} {c : Matrix.SpecialLinearGroup (Fin 4) F}
    (hpt : ∀ x ∈ N, t * x * t⁻¹ ∈ N → (p (t * x * t⁻¹) : Matrix (Fin 4) (Fin 4) F) =
      (c : Matrix (Fin 4) (Fin 4) F) * (p x : Matrix (Fin 4) (Fin 4) F).map σ *
        ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hc : ∀ j : Fin 3, (c : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0)
    (hBσ : (c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc *
      ((c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc).map σ = 1)
    {A Ai : Matrix (Fin 3) (Fin 3) F} (hAAi : A * Ai = 1)
    (hA : A = (c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc * A.map σ)
    {F₀ : Subgroup G} (hF₀N : F₀ ≤ N) (hF₀W₂ : F₀ ≤ normalizer (W₂ : Set G))
    (hF₀t : ∀ x ∈ F₀, t * x * t⁻¹ = x) (hF₀W₁ : ∀ x ∈ F₀, x ∈ W₁ → x = 1)
    (hF₀c : 1344 ≤ Nat.card F₀) :
    (∀ x ∈ F₀, p x ∈ leviQ F) ∧
      ∀ M₀ : Matrix (Fin 3) (Fin 3) F, M₀.map σ = M₀ → M₀.det = 1 →
        ∃ x ∈ F₀, (p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc =
          A * M₀ * Ai := by
  obtain ⟨hσσ, -, hfix⟩ := frob_facts_of_card_four hF hσ
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  set B := (c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc with hBdef
  have hcic : ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (c : Matrix (Fin 4) (Fin 4) F) = 1 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_inv_mul_coe c
  have hcci : (c : Matrix (Fin 4) (Fin 4) F) *
      ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hc0 : (c : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) (Fin.last 3) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (lastRow_of_mul_eq_one hcci hc).2
  have hxF : ∀ x ∈ F₀, (∀ j : Fin 3, (p x : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0) ∧
      (p x : Matrix (Fin 4) (Fin 4) F) * c = c * (p x : Matrix (Fin 4) (Fin 4) F).map σ := by
    intro x hx
    have hxN := hF₀N hx
    have hxZ : ∀ z ∈ W₁ ⊓ W₂, x * z * x⁻¹ ∈ W₁ ⊓ W₂ := fun z hz => mem_inf.2
      ⟨(mem_normalizer_iff.1 (h.le_normalizer hxN) z).1 (mem_inf.1 hz).1,
        (mem_normalizer_iff.1 (hF₀W₂ hx) z).1 (mem_inf.1 hz).2⟩
    refine ⟨h.lastRow_of_conj hF hW₂S₀ hS₀W₂ hW₂c hZ hxN hxZ, ?_⟩
    have h1 := hpt x hxN (by rw [hF₀t x hx]; exact hxN)
    rw [hF₀t x hx] at h1
    calc (p x : Matrix (Fin 4) (Fin 4) F) * c =
          (c : Matrix (Fin 4) (Fin 4) F) * (p x : Matrix (Fin 4) (Fin 4) F).map σ *
            ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * c := by
          rw [← h1]
      _ = c * (p x : Matrix (Fin 4) (Fin 4) F).map σ := by
          rw [Matrix.mul_assoc _ _ (c : Matrix (Fin 4) (Fin 4) F), hcic, Matrix.mul_one]
  have hQ : ∀ x ∈ F₀, p x ∈ leviQ F := by
    intro x hx
    obtain ⟨hP, hE⟩ := hxF x hx
    refine ⟨hP, corner_eq_one_of_mul_eq_map σ hσ hP hc hc0 (fun h0 => ?_) hE⟩
    have hdet := det_eq_of_lastRow hP
    rw [h0, zero_mul, (p x).2] at hdet
    exact one_ne_zero hdet
  have hlevi : ∀ x ∈ F₀,
      (p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc * B =
        B * ((p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc).map σ := by
    intro x hx
    obtain ⟨hP, hE⟩ := hxF x hx
    have hPσ : ∀ j : Fin 3, ((p x : Matrix (Fin 4) (Fin 4) F).map σ) (Fin.last 3) j.castSucc =
        0 := fun j => by rw [Matrix.map_apply, hP j, map_zero]
    rw [hBdef, ← submatrix_castSucc_mul_of_lastRow hc, hE, submatrix_castSucc_mul_of_lastRow hPσ,
      Matrix.submatrix_map]
  let φ₀ : F₀ →* Matrix.SpecialLinearGroup (Fin 3) F :=
    { toFun := fun x => ⟨(p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc,
        det_leviBlock (hQ x x.2)⟩
      map_one' := sigSL_ext (by
        change (p 1 : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1
        rw [h.map_one, Matrix.SpecialLinearGroup.coe_one, submatrix_castSucc_one])
      map_mul' := fun x y => sigSL_ext (by
        change (p (x * y : G) : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc =
          (p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc *
            (p y : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc
        rw [h.map_mul _ (hF₀N x.2) _ (hF₀N y.2)]
        exact leviBlock_mul (hQ y y.2)) }
  have hφ₀ : ∀ x : F₀, ((φ₀ x : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc := fun x => rfl
  have hker : Nat.card φ₀.ker ≤ 8 := by
    have hcol : ∀ x : φ₀.ker, IsColRadical (p ((x : F₀) : G) : Matrix (Fin 4) (Fin 4) F) := by
      intro x
      refine isColRadical_of_mem_leviQ (hQ _ (x : F₀).2) ?_
      have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) F =>
        (M : Matrix (Fin 3) (Fin 3) F)) (MonoidHom.mem_ker.1 x.2)
      simp only [hφ₀, Matrix.SpecialLinearGroup.coe_one] at h1
      exact h1
    refine card_le_eight_of_twist σ hσ hAAi hA (μ := (c : Matrix (Fin 4) (Fin 4) F) (Fin.last 3)
      (Fin.last 3)) (fun x : φ₀.ker => colRadVec (p ((x : F₀) : G) : Matrix (Fin 4) (Fin 4) F))
      (fun x y hxy => ?_) (fun x => smul_colRadVec_of_mul_eq_map σ (hcol x) (hxF _ (x : F₀).2).2)
    have hxN := hF₀N (x : F₀).2
    have hyN := hF₀N (y : F₀).2
    have h1 : p ((x : F₀) : G) = p ((y : F₀) : G) := sigSL_ext ((hcol x).ext (hcol y) hxy)
    have h2 : ((x : F₀) : G) * ((y : F₀) : G)⁻¹ ∈ W₁ := by
      rw [← h.eq_one_iff _ (mul_mem hxN (inv_mem hyN)), h.map_mul _ hxN _ (inv_mem hyN),
        h.map_inv hyN, h1, mul_inv_cancel]
    have h3 := hF₀W₁ _ (mul_mem (x : F₀).2 (inv_mem (y : F₀).2)) h2
    exact Subtype.ext (Subtype.ext (mul_inv_eq_one.1 h3))
  set T := {M : Matrix.SpecialLinearGroup (Fin 3) F |
    (M : Matrix (Fin 3) (Fin 3) F) * B = B * (M : Matrix (Fin 3) (Fin 3) F).map σ} with hTdef
  have hT : T.ncard ≤ 168 := ncard_twistFixed_le σ hσσ hfix hAAi hA hBσ
  have hRT : (φ₀.range : Set (Matrix.SpecialLinearGroup (Fin 3) F)) ⊆ T := by
    rintro _ ⟨x, rfl⟩
    change ((φ₀ x : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * B =
      B * ((φ₀ x : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ
    rw [hφ₀]
    exact hlevi x x.2
  have hRc : 168 ≤ Nat.card φ₀.range := by
    have h1 := Subgroup.card_ker_mul_card_range φ₀
    have h2 : Nat.card φ₀.ker * Nat.card φ₀.range ≤ 8 * Nat.card φ₀.range :=
      Nat.mul_le_mul_right _ hker
    omega
  have hRT' : (φ₀.range : Set (Matrix.SpecialLinearGroup (Fin 3) F)) = T := by
    refine Set.eq_of_subset_of_ncard_le hRT ?_ (Set.toFinite T)
    rw [← Nat.card_coe_set_eq (φ₀.range : Set (Matrix.SpecialLinearGroup (Fin 3) F))]
    exact hT.trans hRc
  refine ⟨hQ, fun M₀ hM₀ hM₀d => ?_⟩
  have hAiA : Ai * A = 1 := mul_eq_one_comm.mp hAAi
  have hdetA : (A * M₀ * Ai).det = 1 := by
    rw [det_mul, det_mul, hM₀d, mul_one, mul_comm, ← det_mul, hAiA, det_one]
  have hN'T : (⟨A * M₀ * Ai, hdetA⟩ : Matrix.SpecialLinearGroup (Fin 3) F) ∈ T :=
    conj_mul_eq_of_map_eq σ hσσ hAAi hA hBσ hM₀
  rw [← hRT'] at hN'T
  obtain ⟨x, hx'⟩ := hN'T
  refine ⟨x, x.2, ?_⟩
  rw [← hφ₀, hx']

end Image

section Main

variable {G : Type*} [Group G] [Finite G] {F : Type} [Field F] [CharP F 2]
variable {N W₁ W₂ S₀ : Subgroup G} {p : G → Matrix.SpecialLinearGroup (Fin 4) F}
  {b : G → Fin 4 → F}

omit [CharP F 2] in
theorem IsFieldModuleData.perfectCore_le_leviPre (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) :
    CFSG.Quasithin.perfectCore (N ⊓ normalizer ((W₁ ⊔ W₂ : Subgroup G) : Set G)) ≤ h.leviPre := by
  set K := CFSG.Quasithin.perfectCore (N ⊓ normalizer ((W₁ ⊔ W₂ : Subgroup G) : Set G)) with hK
  have hKN : K ≤ N := (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  have hKW : K ≤ normalizer ((W₁ ⊔ W₂ : Subgroup G) : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  obtain ⟨hall, -, -⟩ := h.wTwo_count hF hW₂S₀ hS₀W₂ hW₂c hZ
  have hrow : ∀ x ∈ K, ∀ j : Fin 3,
      (p x : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0 := by
    intro x hx j
    obtain ⟨w, hw, hwv⟩ := hall (Pi.single j 1)
    have hwN : w ∈ N := h.sZero_le (hW₂S₀ hw)
    have hxN := hKN hx
    have hpw : (p w : Matrix (Fin 4) (Fin 4) F) = colRadMat (Pi.single j 1) :=
      (h.isColRadical hF hW₂S₀ hS₀W₂ hZ hw).ext (isColRadical_colRadMat _)
        (by rw [hwv, colRadVec_colRadMat])
    have hxw : x * w * x⁻¹ ∈ W₁ ⊔ W₂ := (mem_normalizer_iff.1 (hKW hx) w).1 (mem_sup_right hw)
    have hxwN : x * w * x⁻¹ ∈ N := mul_mem (mul_mem hxN hwN) (inv_mem hxN)
    have hR := (h.mem_sup_iff hF hW₂S₀ hS₀W₂ hW₂c hZ hxwN).1 hxw
    refine apply_last_castSucc_eq_zero_of_isColRadical j hR ?_
    rw [← hpw, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      ← h.map_mul _ hxwN _ hxN, ← h.map_mul _ hxN _ hwN]
    congr 2
    group
  have hKp : ⁅K, K⁆ = K := CFSG.Quasithin.perfectCore_perfect _
  let χ : K →* F :=
    { toFun := fun y => (p y : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) (Fin.last 3)
      map_one' := by
        change (p 1 : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) (Fin.last 3) = 1
        rw [h.map_one, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
      map_mul' := fun y z => by
        change (p (y * z : G) : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) (Fin.last 3) = _
        rw [h.map_mul _ (hKN y.2) _ (hKN z.2), Matrix.SpecialLinearGroup.coe_mul,
          mul_apply_last_last (hrow y y.2)] }
  intro x hx
  have hχ := congrArg Units.val (eq_one_of_commutator_eq_self hKp χ.toHomUnits ⟨x, hx⟩)
  exact ⟨hKN hx, hrow x hx, hχ⟩

theorem IsFieldModuleData.perfectCore_le_normalizer_of_twist (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) {σ : F →+* F}
    (hσ : ∀ x, σ x = x ^ 2) {t : G} (ht2 : t * t = 1) (htS₀ : t ∈ normalizer (S₀ : Set G))
    (htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁) (htW₂ : ∀ w ∈ W₂, t * w * t⁻¹ ∈ W₂)
    {c : Matrix.SpecialLinearGroup (Fin 4) F}
    (hpt : ∀ x ∈ N, t * x * t⁻¹ ∈ N → (p (t * x * t⁻¹) : Matrix (Fin 4) (Fin 4) F) =
      (c : Matrix (Fin 4) (Fin 4) F) * (p x : Matrix (Fin 4) (Fin 4) F).map σ *
        ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hbt : ∀ w ∈ W₁, b (t * w * t⁻¹) = (fun k => σ (b w k)) ᵥ*
      ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    {F₀ : Subgroup G} (hF₀N : F₀ ≤ N) (hF₀W₂ : F₀ ≤ normalizer (W₂ : Set G))
    (hF₀t : ∀ x ∈ F₀, t * x * t⁻¹ = x) (hF₀W₁ : ∀ x ∈ F₀, x ∈ W₁ → x = 1)
    (hF₀c : 1344 ≤ Nat.card F₀) :
    CFSG.Quasithin.perfectCore (N ⊓ normalizer ((W₁ ⊔ W₂ : Subgroup G) : Set G)) ≤
      normalizer (W₂ : Set G) := by
  obtain ⟨hc, -, hBσ, A, Ai, hAu, hAAi, hA⟩ :=
    h.exists_untwist hF hW₂S₀ hS₀W₂ hW₂c hZ hσ ht2 htS₀ htW₁ htW₂ hpt hbt
  obtain ⟨hQ, hsw⟩ := h.exists_mem_of_map_eq hF hW₂S₀ hS₀W₂ hW₂c hZ hσ hpt hc hBσ hAAi hA hF₀N
    hF₀W₂ hF₀t hF₀W₁ hF₀c
  set Y := h.leviPre with hYdef
  set H := S₀ ⊔ F₀ with hHdef
  have hS₀Y : S₀ ≤ Y := fun s hs => ⟨h.sZero_le hs,
    mem_leviQ_of_mem_unitriangular ((h.mem_sZero_iff s (h.sZero_le hs)).1 hs)⟩
  have hF₀Y : F₀ ≤ Y := fun x hx => ⟨hF₀N hx, hQ x hx⟩
  have hHW₂ : H ≤ normalizer (W₂ : Set G) := sup_le hS₀W₂ hF₀W₂
  have hW₁S₀ : W₁ ≤ S₀ := fun w hw => (h.mem_sZero_iff w (h.wOne_le hw)).2
    (by rw [(h.eq_one_iff w (h.wOne_le hw)).2 hw]; exact one_mem _)
  let levY : Y →* Matrix.SpecialLinearGroup (Fin 3) F :=
    { toFun := fun y => ⟨(p y : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc,
        det_leviBlock y.2.2⟩
      map_one' := sigSL_ext (by
        change (p 1 : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1
        rw [h.map_one, Matrix.SpecialLinearGroup.coe_one, submatrix_castSucc_one])
      map_mul' := fun y z => sigSL_ext (by
        change (p (y * z : G) : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc =
          (p y : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc *
            (p z : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc
        rw [h.map_mul _ y.2.1 _ z.2.1]
        exact leviBlock_mul z.2.2) }
  have hlevY : ∀ y : Y,
      ((levY y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (p y : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc := fun y => rfl
  have hR : (H.subgroupOf Y).map levY = ⊤ := by
    refine eq_top_of_conj_swap hAu hAAi (fun u hu => ?_) ?_ ?_
    · obtain ⟨s, hs, hsu⟩ := h.exists_mem_sZero (leviEmbed_mem_unitriangular hu)
      refine ⟨⟨s, hS₀Y hs⟩, mem_subgroupOf.2 (mem_sup_left hs), sigSL_ext ?_⟩
      rw [hlevY]
      change (p s : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = u
      rw [hsu, leviBlock_leviEmbed]
    · obtain ⟨x, hxF, hxb⟩ := hsw (swapMat01 F) (map_swapMat01 σ) det_swapMat01
      exact ⟨levY ⟨x, hF₀Y hxF⟩, ⟨⟨x, hF₀Y hxF⟩, mem_subgroupOf.2 (mem_sup_right hxF), rfl⟩,
        by rw [hlevY]; exact hxb⟩
    · obtain ⟨x, hxF, hxb⟩ := hsw (swapMat12 F) (map_swapMat12 σ) det_swapMat12
      exact ⟨levY ⟨x, hF₀Y hxF⟩, ⟨⟨x, hF₀Y hxF⟩, mem_subgroupOf.2 (mem_sup_right hxF), rfl⟩,
        by rw [hlevY]; exact hxb⟩
  have hYH : Y ≤ H := by
    intro y hy
    have h1 : levY ⟨y, hy⟩ ∈ (H.subgroupOf Y).map levY := by
      rw [hR]
      exact Subgroup.mem_top _
    obtain ⟨k, hkH, hk⟩ := h1
    have h2 : levY ((⟨y, hy⟩ : Y) * k⁻¹) = 1 := by
      rw [levY.map_mul, levY.map_inv, hk, mul_inv_cancel]
    have h3 : IsColRadical (p (((⟨y, hy⟩ * k⁻¹ : Y)) : G) : Matrix (Fin 4) (Fin 4) F) := by
      refine isColRadical_of_mem_leviQ (⟨y, hy⟩ * k⁻¹ : Y).2.2 ?_
      have h4 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) F =>
        (M : Matrix (Fin 3) (Fin 3) F)) h2
      simp only [hlevY, Matrix.SpecialLinearGroup.coe_one] at h4
      exact h4
    have h5 : (((⟨y, hy⟩ * k⁻¹ : Y)) : G) ∈ W₁ ⊔ W₂ :=
      (h.mem_sup_iff hF hW₂S₀ hS₀W₂ hW₂c hZ (⟨y, hy⟩ * k⁻¹ : Y).2.1).2 h3
    have h6 : (((⟨y, hy⟩ * k⁻¹ : Y)) : G) ∈ H := mem_sup_left ((sup_le hW₁S₀ hW₂S₀) h5)
    have h7 : ((k : Y) : G) ∈ H := mem_subgroupOf.1 hkH
    have h8 : y = (((⟨y, hy⟩ * k⁻¹ : Y)) : G) * ((k : Y) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h8]
    exact mul_mem h6 h7
  exact (h.perfectCore_le_leviPre hF hW₂S₀ hS₀W₂ hW₂c hZ).trans (hYH.trans hHW₂)

end Main

end CFSG.SeitzReduction.LinearPilot
