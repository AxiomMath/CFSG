module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Defs
import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

variable {K : Type} [Field K]

local notation "ι" => Fin 2 ⊕ Fin 2

local notation "J" => (fromBlocks 0 1 (-1) 0 : Matrix ι ι K)

local notation "M" => Matrix ι ι K

private def formL (u : ι → K) : (ι → K) →ₗ[K] K where
  toFun w := u ⬝ᵥ (J *ᵥ w)
  map_add' w w' := by simp [mulVec_add, dotProduct_add]
  map_smul' c w := by simp [mulVec_smul, dotProduct_smul]

private theorem formL_eq (v w : ι → K) :
    formL v w = v (.inl 0) * w (.inr 0) + v (.inl 1) * w (.inr 1) -
      v (.inr 0) * w (.inl 0) - v (.inr 1) * w (.inl 1) := by
  simp [formL, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks, one_apply]
  ring

private theorem formL_self (v : ι → K) : formL v v = 0 := by
  rw [formL_eq]; ring

private theorem formL_swap (v w : ι → K) : formL w v = -formL v w := by
  rw [formL_eq, formL_eq]; ring

private theorem formL_smul_left (c : K) (v w : ι → K) : formL (c • v) w = c * formL v w := by
  rw [formL_eq, formL_eq]; simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem formL_map {g : M} (hg : gᵀ * J * g = J) (v w : ι → K) :
    formL (g *ᵥ v) (g *ᵥ w) = formL v w := by
  change (g *ᵥ v) ⬝ᵥ (J *ᵥ (g *ᵥ w)) = v ⬝ᵥ (J *ᵥ w)
  conv_rhs => rw [← hg]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v gᵀ, Matrix.vecMul_transpose]

private theorem exists_formL_ne_zero {v : ι → K} (hv : v ≠ 0) : ∃ w, formL v w ≠ 0 := by
  by_contra h
  push Not at h
  refine hv (funext fun i => ?_)
  have h1 := h (Pi.single (.inr 0) 1)
  have h2 := h (Pi.single (.inr 1) 1)
  have h3 := h (Pi.single (.inl 0) 1)
  have h4 := h (Pi.single (.inl 1) 1)
  simp [formL_eq] at h1 h2 h3 h4
  rcases i with i | i <;> fin_cases i <;> simpa

section Weights

variable {E : Subgroup (GL ι K)} {v : ι → K} {χ : GL ι K → K}

private theorem weight_mul (hv : v ≠ 0) (hχ : ∀ g ∈ E, (g : M) *ᵥ v = χ g • v) {g h : GL ι K}
    (hg : g ∈ E) (hh : h ∈ E) : χ (g * h) = χ g * χ h := by
  have h1 := hχ _ (E.mul_mem hg hh)
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hχ h hh, Matrix.mulVec_smul, hχ g hg, smul_smul]
    at h1
  rw [mul_comm]
  exact smul_left_injective K hv h1.symm

private theorem weight_one (hv : v ≠ 0) (hχ : ∀ g ∈ E, (g : M) *ᵥ v = χ g • v) : χ 1 = 1 := by
  have h1 := hχ 1 E.one_mem
  rw [Units.val_one, Matrix.one_mulVec] at h1
  exact smul_left_injective K hv (by simpa using h1.symm)

private theorem weight_inv (hv : v ≠ 0) (hχ : ∀ g ∈ E, (g : M) *ᵥ v = χ g • v) {g : GL ι K}
    (hg : g ∈ E) : χ g⁻¹ = (χ g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← weight_mul hv hχ hg (E.inv_mem hg), mul_inv_cancel, weight_one hv hχ]

private theorem weight_pow_eq_one (hv : v ≠ 0) (hχ : ∀ g ∈ E, (g : M) *ᵥ v = χ g • v)
    {g : GL ι K} (hg : g ∈ E) {p : ℕ} (hgp : g ^ p = 1) : χ g ^ p = 1 := by
  have key : ∀ k : ℕ, ((g : M) ^ k) *ᵥ v = χ g ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hχ g hg, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have h1 := key p
  rw [← Units.val_pow_eq_pow_val, hgp, Units.val_one, Matrix.one_mulVec] at h1
  exact smul_left_injective K hv (by simpa using h1.symm)

private theorem formL_mulVec_of_weight (hsp : ∀ g ∈ E, (g : M)ᵀ * J * g = J)
    (hχ : ∀ g ∈ E, (g : M) *ᵥ v = χ g • v) {g : GL ι K} (hg : g ∈ E) (w : ι → K) :
    formL v ((g : M) *ᵥ w) = χ g⁻¹ * formL v w := by
  have hu : v = (g : M) *ᵥ (((g⁻¹ : GL ι K) : M) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  conv_lhs => rw [hu]
  rw [formL_map (hsp g hg), hχ _ (E.inv_mem hg), formL_smul_left]

end Weights

section Avg

variable {E : Subgroup (GL ι K)} [Fintype E]

private noncomputable def avg (E : Subgroup (GL ι K)) [Fintype E] (ψ : GL ι K → K)
    (w : ι → K) : ι → K :=
  ∑ g : E, ψ g • (((g : GL ι K) : M) *ᵥ w)

private theorem avg_mem {S : Submodule K (ι → K)} (hinv : ∀ g ∈ E, ∀ v ∈ S, (g : M) *ᵥ v ∈ S)
    (ψ : GL ι K → K) {w : ι → K} (hw : w ∈ S) : avg E ψ w ∈ S :=
  S.sum_mem fun g _ => S.smul_mem _ (hinv g g.2 w hw)

private theorem avg_weight {ψ : GL ι K → K} (hmul : ∀ g ∈ E, ∀ h ∈ E, ψ (g * h) = ψ g * ψ h)
    (hone : ψ 1 = 1) {h : GL ι K} (hh : h ∈ E) (w : ι → K) :
    (h : M) *ᵥ avg E ψ w = ψ h⁻¹ • avg E ψ w := by
  rw [avg, Matrix.mulVec_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : E)) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Units.val_mul, smul_smul]
  rw [hmul h hh g g.2, ← mul_assoc, ← hmul _ (E.inv_mem hh) h hh, inv_mul_cancel, hone, one_mul]

private theorem avg_pair (hsp : ∀ g ∈ E, (g : M)ᵀ * J * g = J) {v : ι → K} {χ : GL ι K → K}
    (hχ : ∀ g ∈ E, (g : M) *ᵥ v = χ g • v) (ψ : GL ι K → K) (w : ι → K) :
    formL v (avg E ψ w) = (∑ g : E, ψ g * χ (g : GL ι K)⁻¹) * formL v w := by
  rw [avg, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, formL_mulVec_of_weight hsp hχ g.2, smul_eq_mul, mul_assoc]

end Avg

section Eigen

variable [Fintype K]

private theorem prod_X_sub_C_eq :
    ∏ a : K, (Polynomial.X - Polynomial.C a) =
      (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq)
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
    rw [FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq K hq]; rfl)
  rw [FiniteField.roots_X_pow_card_sub_X] at h
  exact h

omit [Fintype K] in
private theorem exists_eigvec_aux {A : M} {S : Submodule K (ι → K)}
    (hS : ∀ v ∈ S, A *ᵥ v ∈ S) (s : Finset K) : ∀ v ∈ S, v ≠ 0 →
    Polynomial.aeval A (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) *ᵥ v = 0 →
    ∃ w ∈ S, w ≠ 0 ∧ ∃ c : K, A *ᵥ w = c • w := by
  classical
  induction s using Finset.induction_on with
  | empty => intro v _ hv h; simp at h; exact absurd h hv
  | insert a s ha ih =>
    intro v hvS hv h
    rw [Finset.prod_insert ha, mul_comm, map_mul, ← Matrix.mulVec_mulVec] at h
    have hu : Polynomial.aeval A (Polynomial.X - Polynomial.C a) *ᵥ v = A *ᵥ v - a • v := by
      simp [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    rw [hu] at h
    by_cases hu0 : A *ᵥ v - a • v = 0
    · exact ⟨v, hvS, hv, a, sub_eq_zero.1 hu0⟩
    · exact ih _ (S.sub_mem (hS v hvS) (S.smul_mem a hvS)) hu0 h

private theorem exists_eigvec {A : M} (hA : A ^ Fintype.card K = A) {S : Submodule K (ι → K)}
    (hS : ∀ v ∈ S, A *ᵥ v ∈ S) (hS0 : S ≠ ⊥) : ∃ w ∈ S, w ≠ 0 ∧ ∃ c : K, A *ᵥ w = c • w := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  refine exists_eigvec_aux hS Finset.univ v hv hv0 ?_
  rw [prod_X_sub_C_eq]
  simp [hA]

private theorem exists_joint_eigvec {E : Subgroup (GL ι K)}
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hq : ∀ g ∈ E, (g : M) ^ Fintype.card K = g) :
    ∀ (n : ℕ) (S : Submodule K (ι → K)), Module.finrank K S = n → S ≠ ⊥ →
      (∀ g ∈ E, ∀ v ∈ S, (g : M) *ᵥ v ∈ S) →
      ∃ v ∈ S, v ≠ 0 ∧ ∀ g ∈ E, ∃ c : K, (g : M) *ᵥ v = c • v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hS hinv
  by_cases hall : ∀ g ∈ E, ∀ v ∈ S, ∃ c : K, (g : M) *ᵥ v = c • v
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    exact ⟨v, hv, hv0, fun g hg => hall g hg v hv⟩
  push Not at hall
  obtain ⟨a, ha, w, hw, hwc⟩ := hall
  obtain ⟨u, hu, hu0, c, hc⟩ := exists_eigvec (hq a ha) (hinv a ha) hS
  set S' := S ⊓ LinearMap.ker (Matrix.mulVecLin ((a : M) - c • 1)) with hS'
  have hmem : ∀ v, v ∈ S' ↔ v ∈ S ∧ (a : M) *ᵥ v = c • v := by
    intro v
    simp [hS', sub_eq_zero]
  have hlt : S' < S :=
    lt_of_le_of_ne inf_le_left fun h => hwc c ((hmem w).1 (by rw [h]; exact hw)).2
  have hinv' : ∀ g ∈ E, ∀ v ∈ S', (g : M) *ᵥ v ∈ S' := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    refine ⟨hinv g hg v hv.1, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hcomm a ha g hg, Units.val_mul,
      ← Matrix.mulVec_mulVec, hv.2, Matrix.mulVec_smul]
  obtain ⟨v, hv, hv0, hvE⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) S' rfl
    (fun h => hu0 (by simpa [h] using (hmem u).2 ⟨hu, hc⟩)) hinv'
  exact ⟨v, ((hmem v).1 hv).1, hv0, hvE⟩

end Eigen

section Pairs

variable {E : Subgroup (GL ι K)}

private theorem exists_pair [Fintype K] [Finite E] (hsp : ∀ g ∈ E, (g : M)ᵀ * J * g = J)
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hq : ∀ g ∈ E, (g : M) ^ Fintype.card K = g)
    (hcard : (Nat.card E : K) ≠ 0) {S : Submodule K (ι → K)} (hS : S ≠ ⊥)
    (hinv : ∀ g ∈ E, ∀ v ∈ S, (g : M) *ᵥ v ∈ S)
    (hnd : ∀ e ∈ S, e ≠ 0 → ∃ w ∈ S, formL e w ≠ 0) :
    ∃ e ∈ S, ∃ f ∈ S, ∃ χ : GL ι K → K, (∀ g ∈ E, (g : M) *ᵥ e = χ g • e) ∧
      (∀ g ∈ E, (g : M) *ᵥ f = (χ g)⁻¹ • f) ∧ formL e f = 1 := by
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨e, he, he0, hχ⟩ := exists_joint_eigvec hcomm hq _ S rfl hS hinv
  choose! χ hχ using hχ
  obtain ⟨w, hw, hew⟩ := hnd e he he0
  have hpair : formL e (avg E χ w) = (Nat.card E : K) * formL e w := by
    rw [avg_pair hsp hχ, Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_ones,
      Nat.cast_sum, Nat.cast_one]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← weight_mul he0 hχ g.2 (E.inv_mem g.2), mul_inv_cancel, weight_one he0 hχ]
  have hf0 : formL e (avg E χ w) ≠ 0 := by rw [hpair]; exact mul_ne_zero hcard hew
  refine ⟨e, he, (formL e (avg E χ w))⁻¹ • avg E χ w, S.smul_mem _ (avg_mem hinv χ hw), χ, hχ,
    fun g hg => ?_, ?_⟩
  · rw [Matrix.mulVec_smul, avg_weight (fun g hg h hh => weight_mul he0 hχ hg hh)
      (weight_one he0 hχ) hg, weight_inv he0 hχ hg, smul_comm]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hf0]

private def perpPair (e₀ f₀ : ι → K) : Submodule K (ι → K) :=
  LinearMap.ker (formL e₀) ⊓ LinearMap.ker (formL f₀)

private theorem mem_perpPair {e₀ f₀ v : ι → K} :
    v ∈ perpPair e₀ f₀ ↔ formL e₀ v = 0 ∧ formL f₀ v = 0 := by
  simp [perpPair]

private theorem perpPair_ne_bot (e₀ f₀ : ι → K) : perpPair e₀ f₀ ≠ ⊥ := by
  have h : perpPair e₀ f₀ = LinearMap.ker ((formL e₀).prod (formL f₀)) := by
    rw [LinearMap.ker_prod]; rfl
  intro hb
  have h1 := LinearMap.finrank_range_add_finrank_ker ((formL e₀).prod (formL f₀))
  have h2 := Submodule.finrank_le (LinearMap.range ((formL e₀).prod (formL f₀)))
  rw [← h, hb, finrank_bot, Module.finrank_fintype_fun_eq_card] at h1
  simp [Module.finrank_prod] at h1 h2
  omega

private theorem perpPair_inv (hsp : ∀ g ∈ E, (g : M)ᵀ * J * g = J) {e₀ f₀ : ι → K}
    {χ₀ χ₀' : GL ι K → K} (h₀ : ∀ g ∈ E, (g : M) *ᵥ e₀ = χ₀ g • e₀)
    (h₀' : ∀ g ∈ E, (g : M) *ᵥ f₀ = χ₀' g • f₀) :
    ∀ g ∈ E, ∀ v ∈ perpPair e₀ f₀, (g : M) *ᵥ v ∈ perpPair e₀ f₀ := by
  intro g hg v hv
  rw [mem_perpPair] at hv ⊢
  rw [formL_mulVec_of_weight hsp h₀ hg, formL_mulVec_of_weight hsp h₀' hg, hv.1, hv.2]
  simp

private theorem perpPair_nondeg {e₀ f₀ : ι → K} (h₀ : formL e₀ f₀ = 1) :
    ∀ e ∈ perpPair e₀ f₀, e ≠ 0 → ∃ w ∈ perpPair e₀ f₀, formL e w ≠ 0 := by
  intro e he he0
  rw [mem_perpPair] at he
  obtain ⟨w, hw⟩ := exists_formL_ne_zero he0
  refine ⟨w - formL e₀ w • f₀ + formL f₀ w • e₀, ?_, ?_⟩
  · rw [mem_perpPair]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, formL_self, h₀, formL_swap e₀ f₀]
    constructor <;> ring
  · simp only [map_add, map_sub, map_smul, smul_eq_mul, formL_swap f₀ e, formL_swap e₀ e,
      he.1, he.2]
    simpa using hw

end Pairs

section Basis

private theorem exists_basis [Fintype K] {E : Subgroup (GL ι K)} [Finite E]
    (hsp : ∀ g ∈ E, (g : M)ᵀ * J * g = J)
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hq : ∀ g ∈ E, (g : M) ^ Fintype.card K = g)
    (hcard : (Nat.card E : K) ≠ 0) :
    ∃ e₀ f₀ e₁ f₁ : ι → K, ∃ χ₀ χ₁ : GL ι K → K,
      (∀ g ∈ E, (g : M) *ᵥ e₀ = χ₀ g • e₀) ∧ (∀ g ∈ E, (g : M) *ᵥ f₀ = (χ₀ g)⁻¹ • f₀) ∧
      (∀ g ∈ E, (g : M) *ᵥ e₁ = χ₁ g • e₁) ∧ (∀ g ∈ E, (g : M) *ᵥ f₁ = (χ₁ g)⁻¹ • f₁) ∧
      formL e₀ f₀ = 1 ∧ formL e₁ f₁ = 1 ∧ formL e₀ e₁ = 0 ∧ formL f₀ e₁ = 0 ∧
      formL e₀ f₁ = 0 ∧ formL f₀ f₁ = 0 := by
  obtain ⟨e₀, -, f₀, -, χ₀, h₀, h₀', h₀₀⟩ := exists_pair hsp hcomm hq hcard (S := ⊤) top_ne_bot
    (fun _ _ _ _ => Submodule.mem_top)
    (fun _ _ he => (exists_formL_ne_zero he).imp fun _ hw => ⟨Submodule.mem_top, hw⟩)
  obtain ⟨e₁, he₁, f₁, hf₁, χ₁, h₁, h₁', h₁₁⟩ := exists_pair hsp hcomm hq hcard
    (perpPair_ne_bot e₀ f₀) (perpPair_inv hsp h₀ h₀') (perpPair_nondeg h₀₀)
  rw [mem_perpPair] at he₁ hf₁
  exact ⟨e₀, f₀, e₁, f₁, χ₀, χ₁, h₀, h₀', h₁, h₁', h₀₀, h₁₁, he₁.1, he₁.2, hf₁.1, hf₁.2⟩

private theorem gram_of_pairs {e₀ f₀ e₁ f₁ : ι → K} (h₀ : formL e₀ f₀ = 1)
    (h₁ : formL e₁ f₁ = 1) (h₂ : formL e₀ e₁ = 0) (h₃ : formL f₀ e₁ = 0)
    (h₄ : formL e₀ f₁ = 0) (h₅ : formL f₀ f₁ = 0) (i j : ι) :
    formL (Sum.elim ![e₀, e₁] ![f₀, f₁] i) (Sum.elim ![e₀, e₁] ![f₀, f₁] j) = J i j := by
  have h₀' : formL f₀ e₀ = -1 := by rw [formL_swap, h₀]
  have h₁' : formL f₁ e₁ = -1 := by rw [formL_swap, h₁]
  have h₂' : formL e₁ e₀ = 0 := by rw [formL_swap, h₂, neg_zero]
  have h₃' : formL e₁ f₀ = 0 := by rw [formL_swap, h₃, neg_zero]
  have h₄' : formL f₁ e₀ = 0 := by rw [formL_swap, h₄, neg_zero]
  have h₅' : formL f₁ f₀ = 0 := by rw [formL_swap, h₅, neg_zero]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [formL_self, h₀, h₁, h₂, h₃, h₄, h₅, h₀', h₁', h₂', h₃', h₄', h₅', one_apply]

private theorem J_mul_J : J * J = -1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

private theorem exists_sp_conj (b : ι → ι → K) (hb : ∀ i j, formL (b i) (b j) = J i j) :
    ∃ Q ∈ CFSG.Open.StatedSp 2 K, ∀ (g : GL ι K) (d : ι → K),
      (∀ i, (g : M) *ᵥ b i = d i • b i) → ((MulAut.conj Q g : GL ι K) : M) = diagonal d := by
  set P : M := (of b)ᵀ with hPdef
  have hP : Pᵀ * J * P = J := by
    ext i j
    rw [mul_mul_apply, hPdef, transpose_transpose]
    exact hb i j
  have hLP : -(J * Pᵀ * J) * P = 1 := by
    rw [neg_mul, Matrix.mul_assoc J, Matrix.mul_assoc J, hP, J_mul_J, neg_neg]
  let U : GL ι K := ⟨P, -(J * Pᵀ * J), mul_eq_one_comm.1 hLP, hLP⟩
  refine ⟨U⁻¹, inv_mem (CFSG.Open.StatedAPI.mem_statedSp_iff.2 hP), fun g d hd => ?_⟩
  have hgP : (g : M) * P = P * diagonal d := by
    ext r c
    rw [mul_diagonal]
    have := congrFun (hd c) r
    simpa [hPdef, mul_apply, mulVec, dotProduct, mul_comm] using this
  rw [MulAut.conj_apply]
  change -(J * Pᵀ * J) * (g : M) * P = diagonal d
  rw [Matrix.mul_assoc, hgP, ← Matrix.mul_assoc, hLP, Matrix.one_mul]

private theorem exists_root_pair {p : ℕ} (hp : p.Prime) {E : Subgroup (GL ι K)}
    (hE : Nat.card E = p ^ 2) {χ₀ χ₁ : GL ι K → K}
    (hinj : ∀ g ∈ E, ∀ h ∈ E, χ₀ g = χ₀ h → χ₁ g = χ₁ h → g = h)
    (hpow : ∀ g ∈ E, χ₀ g ^ p = 1 ∧ χ₁ g ^ p = 1) :
    ∃ ζ : K, ζ ≠ 1 ∧ (∃ g ∈ E, χ₀ g = ζ ∧ χ₁ g = 1) ∧ ∃ g ∈ E, χ₀ g = 1 ∧ χ₁ g = ζ := by
  classical
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; exact pow_ne_zero 2 hp.ne_zero)
  have : Fintype E := Fintype.ofFinite E
  set R := Polynomial.nthRootsFinset p (1 : K) with hRdef
  have hR : R.card ≤ p := by
    rw [hRdef, Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  let φ : E → K × K := fun g => (χ₀ g, χ₁ g)
  have hφ : Function.Injective φ := fun g h hgh =>
    Subtype.ext (hinj g g.2 h h.2 (congrArg Prod.fst hgh) (congrArg Prod.snd hgh))
  have hsub : Finset.univ.image φ ⊆ R ×ˢ R := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    simp [φ, hRdef, Finset.mem_product, Polynomial.mem_nthRootsFinset hp.pos, hpow g g.2]
  have hcardI : (Finset.univ.image φ).card = p ^ 2 := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_univ, ← Nat.card_eq_fintype_card, hE]
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_product, hcardI, sq]; exact Nat.mul_le_mul hR hR)
  have hRp : p ≤ R.card := by
    by_contra h
    push Not at h
    have := Finset.card_le_card hsub
    rw [hcardI, Finset.card_product, sq] at this
    exact absurd this (not_le.2 (Nat.mul_lt_mul'' h h))
  obtain ⟨ζ, hζ, hζ1⟩ := Finset.exists_mem_ne (hp.one_lt.trans_le hRp) 1
  have h1 : (1 : K) ∈ R := Polynomial.one_mem_nthRootsFinset hp.pos
  have get : ∀ x ∈ R ×ˢ R, ∃ g ∈ E, χ₀ g = x.1 ∧ χ₁ g = x.2 := by
    intro x hx
    rw [← heq] at hx
    obtain ⟨g, -, hg⟩ := Finset.mem_image.1 hx
    exact ⟨g, g.2, by rw [← hg], by rw [← hg]⟩
  exact ⟨ζ, hζ1, get (ζ, 1) (Finset.mem_product.2 ⟨hζ, h1⟩),
    get (1, ζ) (Finset.mem_product.2 ⟨h1, hζ⟩)⟩

end Basis

private theorem pow_card_eq_self {q p : ℕ} (hq : 1 ≤ q) (hdvd : p ∣ q - 1) {g : GL ι K}
    (hg : g ^ p = 1) : (g : M) ^ q = g := by
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  obtain ⟨k, hk⟩ := hdvd
  calc g ^ q = g ^ (q - 1) * g := by rw [← pow_succ, Nat.sub_add_cancel hq]
    _ = g := by rw [hk, pow_mul, hg, one_pow, one_mul]

private theorem ne_zero_of_formL_eq_one {e f : ι → K} (h : formL e f = 1) : e ≠ 0 := by
  rintro rfl
  simp [formL_eq] at h

theorem exists_conj_spDiag {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (hpq : p ≠ q) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hE : IsElemSp p E)
    (hdvd : p ∣ q - 1) :
    ∃ P ∈ CFSG.Open.StatedSp 2 (ZMod q), ∃ ζ : ZMod q, ζ ≠ 1 ∧
      (∃ g ∈ E.map (MulAut.conj P).toMonoidHom, (g : Matrix _ _ (ZMod q)) = spDiagMatrix ζ 1) ∧
      ∃ g ∈ E.map (MulAut.conj P).toMonoidHom, (g : Matrix _ _ (ZMod q)) = spDiagMatrix 1 ζ := by
  have hqp : q.Prime := Fact.out
  have hsp : ∀ g ∈ E, (g : Matrix ι ι (ZMod q))ᵀ * fromBlocks 0 1 (-1) 0 *
      (g : Matrix ι ι (ZMod q)) = fromBlocks 0 1 (-1) 0 := fun g hg =>
    CFSG.Open.StatedAPI.mem_statedSp_iff.1 (hE.le_sp hg)
  have hq : ∀ g ∈ E, (g : Matrix ι ι (ZMod q)) ^ Fintype.card (ZMod q) = g := fun g hg => by
    rw [ZMod.card]; exact pow_card_eq_self hqp.one_lt.le hdvd (hE.pow_eq_one g hg)
  have : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hE.card_eq]; exact pow_ne_zero 2 hp.ne_zero)
  have hcard : (Nat.card E : ZMod q) ≠ 0 := by
    rw [hE.card_eq, Nat.cast_pow]
    refine pow_ne_zero 2 fun h => hpq ?_
    rw [ZMod.natCast_eq_zero_iff] at h
    exact ((Nat.prime_dvd_prime_iff_eq hqp hp).1 h).symm
  obtain ⟨e₀, f₀, e₁, f₁, χ₀, χ₁, h₀, h₀', h₁, h₁', g₀, g₁, g₂, g₃, g₄, g₅⟩ :=
    exists_basis hsp hE.comm hq hcard
  obtain ⟨Q, hQ, hconj⟩ := exists_sp_conj _ (gram_of_pairs g₀ g₁ g₂ g₃ g₄ g₅)
  have hd : ∀ g ∈ E, ((MulAut.conj Q g : GL ι (ZMod q)) : Matrix ι ι (ZMod q)) =
      spDiagMatrix (χ₀ g) (χ₁ g) := fun g hg => hconj g _ (by
    rintro (i | i) <;> fin_cases i
    exacts [h₀ g hg, h₁ g hg, h₀' g hg, h₁' g hg])
  have hinj : ∀ g ∈ E, ∀ h ∈ E, χ₀ g = χ₀ h → χ₁ g = χ₁ h → g = h := by
    intro g hg h hh h0 h1
    have := hd g hg
    rw [h0, h1, ← hd h hh] at this
    exact (MulAut.conj Q).injective (Units.ext this)
  obtain ⟨ζ, hζ, ⟨g, hg, hg0, hg1⟩, ⟨h, hh, hh0, hh1⟩⟩ := exists_root_pair hp hE.card_eq hinj
    fun g hg => ⟨weight_pow_eq_one (ne_zero_of_formL_eq_one g₀) h₀ hg (hE.pow_eq_one g hg),
      weight_pow_eq_one (ne_zero_of_formL_eq_one g₁) h₁ hg (hE.pow_eq_one g hg)⟩
  exact ⟨Q, hQ, ζ, hζ, ⟨_, ⟨g, hg, rfl⟩, by rw [← hg0, ← hg1]; exact hd g hg⟩,
    ⟨_, ⟨h, hh, rfl⟩, by rw [← hh0, ← hh1]; exact hd h hh⟩⟩


end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
