module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSL4Main
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSp4Main
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSL4

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.PSL
open scoped MatrixGroups

theorem exists_pairs_of_card_two {J : Finset (Fin 4)} (hJ : J.card = 2) :
    ∃ a b c d : Fin 4, a ∈ J ∧ b ∉ J ∧ c ∈ J ∧ d ∉ J ∧ a ≠ b ∧ c ≠ d ∧
      ∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔ x ∉ ({c, d} : Finset (Fin 4)) := by
  obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.1 hJ
  have hc : ({j₁, j₂} : Finset (Fin 4))ᶜ.card = 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hJ]
  obtain ⟨k₁, k₂, hk, hK⟩ := Finset.card_eq_two.1 hc
  have hk₁ : k₁ ∉ ({j₁, j₂} : Finset (Fin 4)) := by
    rw [← Finset.mem_compl, hK]
    simp
  have hk₂ : k₂ ∉ ({j₁, j₂} : Finset (Fin 4)) := by
    rw [← Finset.mem_compl, hK]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk₁ hk₂
  have hall : ∀ x : Fin 4, x = j₁ ∨ x = j₂ ∨ x = k₁ ∨ x = k₂ := by
    intro x
    by_cases hx : x ∈ ({j₁, j₂} : Finset (Fin 4))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      tauto
    · rw [← Finset.mem_compl, hK] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      tauto
  refine ⟨j₁, k₁, j₂, k₂, by simp, by simp [hk₁.1, hk₁.2], by simp, by simp [hk₂.1, hk₂.2],
    fun h => hk₁.1 h.symm, fun h => hk₂.2 h.symm, fun x => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl) (h | h)
    · exact hj h
    · exact hk₂.1 h.symm
    · exact hk₁.2 h
    · exact hk h
  · intro h
    push Not at h
    rcases hall x with h' | h' | h' | h'
    · exact Or.inl h'
    · exact absurd h' h.1
    · exact Or.inr h'
    · exact absurd h' h.2

variable {K : Type} [Field K] [Finite K]

theorem split_pair_hyps (hK : ringChar K ≠ 2)
    (hinj : Function.Injective (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)))
    {B : Subgroup (MulAut (projectiveSL 4 K))}
    (hB : (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ≤ B)
    {J : Finset (Fin 4)} {a b : Fin 4} (ha : a ∈ J) (hb : b ∉ J) :
    compInd K {a, b} * ((signGL K J : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (signGL K J : Matrix (Fin 4) (Fin 4) K) * compInd K {a, b} ∧
      ¬ PairBlockScalar a b ((signGL K J : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ∧
      ∀ y ∈ oddCoreIn B (conjAut 4 K (signGL K J)), ∃ D : GL (Fin 4) K, y = conjAut 4 K D ∧
        compInd K {a, b} * (D : Matrix (Fin 4) (Fin 4) K) = D * compInd K {a, b} ∧
        (PairBlockScalar a b (D : Matrix (Fin 4) (Fin 4) K) → conjAut 4 K D = 1) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · rw [coe_signGL, compInd, signMat, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  · rintro ⟨h, -, -⟩
    rw [coe_signGL, signMat, diagonal_apply_eq, diagonal_apply_eq] at h
    simp only [ha, hb, ↓reduceIte] at h
    exact h2 (by linear_combination -h)
  · obtain ⟨α, β, rfl⟩ := split_oddCoreIn hK (by omega) hinj hB ha hb hy
    refine ⟨_, rfl, ?_, fun hs => ?_⟩
    · rw [coe_blockScalarGL, compInd, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    · obtain ⟨h, -, -⟩ := hs
      rw [coe_blockScalarGL, diagonal_apply_eq, diagonal_apply_eq] at h
      simp only [ha, hb, ↓reduceIte] at h
      have hαβ : α = β := Units.ext h
      subst hαβ
      have : blockScalarGL J α α = GeneralLinearGroup.scalar (Fin 4) α := by
        apply Units.ext
        rw [coe_blockScalarGL, GeneralLinearGroup.coe_scalar, scalar_apply]
        congr 1
        funext i
        split_ifs <;> rfl
      rw [this, conjAut_scalar]

theorem quad_pair_hyps {l : K} (hl : ¬ IsSquare l)
    (hinj : Function.Injective (MulAut.conj : projectiveSL (2 * 2) K →*
      MulAut (projectiveSL (2 * 2) K)))
    {B : Subgroup (MulAut (projectiveSL (2 * 2) K))}
    (hB : (MulAut.conj : projectiveSL (2 * 2) K →* MulAut (projectiveSL (2 * 2) K)).range ≤ B)
    (k : Fin 2) :
    compInd K {finProdFinEquiv (k, (0 : Fin 2)), finProdFinEquiv (k, (1 : Fin 2))} *
        ((quadGL l 2 hl : GL (Fin (2 * 2)) K) : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) =
        ((quadGL l 2 hl : GL (Fin (2 * 2)) K) : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) *
          compInd K {finProdFinEquiv (k, (0 : Fin 2)), finProdFinEquiv (k, (1 : Fin 2))} ∧
      ¬ PairBlockScalar (finProdFinEquiv (k, (0 : Fin 2))) (finProdFinEquiv (k, (1 : Fin 2)))
        ((quadGL l 2 hl : GL (Fin (2 * 2)) K) : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) ∧
      ∀ y ∈ oddCoreIn B (conjAut (2 * 2) K (quadGL l 2 hl)), ∃ D : GL (Fin (2 * 2)) K,
        y = conjAut (2 * 2) K D ∧
        compInd K {finProdFinEquiv (k, (0 : Fin 2)), finProdFinEquiv (k, (1 : Fin 2))} *
          (D : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) =
          D * compInd K {finProdFinEquiv (k, (0 : Fin 2)), finProdFinEquiv (k, (1 : Fin 2))} ∧
        (PairBlockScalar (finProdFinEquiv (k, (0 : Fin 2))) (finProdFinEquiv (k, (1 : Fin 2)))
          (D : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) → conjAut (2 * 2) K D = 1) := by
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · rw [coe_quadGL]
    exact compInd_commute_blockRep_scalar' k _
  · rintro ⟨-, -, h⟩
    rw [coe_quadGL, quadMat_apply] at h
    simp [compMat] at h
  · obtain ⟨D, x, rfl, hD⟩ := nonsplit_oddCoreIn hl le_rfl hinj hB hy
    refine ⟨D, rfl, by rw [hD]; exact compInd_commute_blockRep_scalar' k x, fun hs => ?_⟩
    obtain ⟨h1, -, h3⟩ := hs
    rw [hD] at h1 h3
    obtain ⟨α, hα⟩ := blockRep_scalar_eq_smul_of_block k h1 h3
    have hα0 : α ≠ 0 := by
      intro h0
      have hdet := D.isUnit.map Matrix.detMonoidHom
      rw [Matrix.coe_detMonoidHom, hD, hα, h0, zero_smul] at hdet
      have : Nonempty (Fin (2 * 2)) := ⟨⟨0, by omega⟩⟩
      rw [det_zero] at hdet
      exact not_isUnit_zero hdet
    have : D = GeneralLinearGroup.scalar (Fin (2 * 2)) (Units.mk0 α hα0) := by
      apply Units.ext
      rw [hD, hα]
      ext i j
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    rw [this, conjAut_scalar]

theorem sl4_twin_X {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f)
    (hinj : Function.Injective (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (projectiveSL 4 K)}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {Y : Subgroup X} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCentralizerCore t) :
    (∃ A : GL (Fin 4) K, ψ t = conjAut 4 K A ∧ ∃ (H : GL (Fin 4) K) (J₀ : Finset (Fin 4))
      (μ : Kˣ), Odd J₀.card ∧ H * A * H⁻¹ = GeneralLinearGroup.scalar (Fin 4) μ * signGL K J₀) ∨
    (5 ≤ Nat.card K ∧ ∃ ψ' : X →* MulAut (projectiveSL 4 K), Function.Injective ψ' ∧
      (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ≤ ψ'.range ∧
      (∀ x, ψ' x ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ↔
        ψ x ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range) ∧
      ∃ (a b c d : Fin 4) (_ : a ≠ b) (_ : c ≠ d),
        (∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔ x ∉ ({c, d} : Finset (Fin 4))) ∧
        ActsProperly (ψ' t) (Y.map ψ') (pairSlice K a b) ⊥ ∧
        ActsProperly (ψ' t) (Y.map ψ') (pairSlice K c d) ⊥) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hn : 3 ≤ 4 := by norm_num
  have hqodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hq3 : 3 ≤ ℓ ^ f := by
    have := hℓ.two_le
    have : 3 ≤ ℓ := by omega
    exact this.trans (Nat.le_self_pow (by omega) ℓ)
  have hq5 : Nat.card K ≠ 3 → 5 ≤ Nat.card K := fun h => by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hYne : ∀ {ψ' : X →* MulAut (projectiveSL 4 K)}, Function.Injective ψ' → Y.map ψ' ≠ ⊥ :=
    fun h hmap => hY ((map_eq_bot_iff_of_injective _ h).1 hmap)
  have hYO' : ∀ {ψ' : X →* MulAut (projectiveSL 4 K)}, Function.Injective ψ' →
      Y.map ψ' ≤ oddCoreIn ψ'.range (ψ' t) := fun h => by
    rw [← map_oddCentralizerCore_of_injective h]
    exact map_mono hYO
  have hbot : ∀ {ψ' : X →* MulAut (projectiveSL 4 K)}, Function.Injective ψ' →
      oddCoreIn ψ'.range (ψ' t) = ⊥ → False := fun hinj' h =>
    hY (eq_bot_of_oddCoreIn hinj' h hYO)
  have hInnN : (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range.Normal :=
    conj_range_normal
  have hconj : ∀ H : GL (Fin 4) K,
      Function.Injective ((MulAut.conj (conjAut 4 K H)).toMonoidHom.comp ψ) ∧
      (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ≤
        ((MulAut.conj (conjAut 4 K H)).toMonoidHom.comp ψ).range ∧
      ∀ x, ((MulAut.conj (conjAut 4 K H)).toMonoidHom.comp ψ) x ∈
          (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ↔
        ψ x ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
    intro H
    obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut 4 K H)
    refine ⟨hinj', hInn', fun x => ?_⟩
    change conjAut 4 K H * ψ x * (conjAut 4 K H)⁻¹ ∈ _ ↔ _
    constructor
    · intro h
      have := hInnN.conj_mem _ h (conjAut 4 K H)⁻¹
      rwa [inv_inv, show (conjAut 4 K H)⁻¹ * (conjAut 4 K H * ψ x * (conjAut 4 K H)⁻¹) *
        conjAut 4 K H = ψ x by group] at this
    · intro h
      exact hInnN.conj_mem _ h _
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 (ψ t)
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    by_cases hσ : σ = 1
    swap
    · exact absurd (field_eq_bot hℓ hℓ2 hf hKc hn hinj hψ hInn ht hσ hα hYO) hY
    subst hσ
    rw [map_one, mul_one] at hα
    have htt : t * t = 1 := by
      rw [← pow_two]
      have h := pow_orderOf_eq_one t
      rwa [ht] at h
    have hA2 : conjAut 4 K (A * A) * fieldAut 4 K 1 = 1 := by
      rw [map_one, mul_one, map_mul, ← hα, ← map_mul, htt, map_one]
    obtain ⟨-, l, hl⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 hA2
    have hns : ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin 4) c := by
      intro c hc
      have : ψ t = 1 := by rw [hα, hc, conjAut_scalar]
      have ht1 : t = 1 := hψ (by rw [this, map_one])
      rw [ht1, orderOf_one] at ht
      exact absurd ht (by norm_num)
    by_cases hsq : IsSquare (l : K)
    ·
      obtain ⟨r, hr⟩ := hsq
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact l.ne_zero (by rw [hr, mul_zero])
      set μ := Units.mk0 r hr0
      have hAμ : A * A = GeneralLinearGroup.scalar (Fin 4) (μ * μ) := by
        rw [← hl]
        congr 1
        exact Units.ext hr
      obtain ⟨H, J, a, b, ha, hb, hH⟩ := exists_split_normal_form hK hAμ hns
      obtain ⟨hinj', hInn', hpre⟩ := hconj H
      set ψ' := (MulAut.conj (conjAut 4 K H)).toMonoidHom.comp ψ with hψ'def
      have hψ't : ψ' t = conjAut 4 K (signGL K J) := by
        change conjAut 4 K H * ψ t * (conjAut 4 K H)⁻¹ = _
        rw [hα, ← map_inv, ← map_mul, ← map_mul, hH, map_mul, conjAut_scalar, one_mul]
      by_cases h3 : Nat.card K = 3
      · exfalso
        refine hbot hinj' ?_
        rw [hψ't]
        exact split_oddCoreIn_eq_bot_three hK hn h3 hinj hInn' ha hb
      by_cases hJodd : Odd J.card
      · exact Or.inl ⟨A, hα, H, J, μ, hJodd, hH⟩
      have hJ2 : J.card = 2 := by
        have h1 : 1 ≤ J.card := Finset.card_pos.2 ⟨a, ha⟩
        have h3' : J.card ≤ 3 := by
          have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
            ⟨Finset.subset_univ J, fun h => hb (h ▸ Finset.mem_univ b)⟩)
          rw [Finset.card_univ, Fintype.card_fin] at this
          omega
        rw [Nat.not_odd_iff_even] at hJodd
        obtain ⟨k, hk⟩ := hJodd
        omega
      obtain ⟨a', b', c', d', ha', hb', hc', hd', hab, hcd, hpair⟩ := exists_pairs_of_card_two hJ2
      have hAt : orderOf (conjAut 4 K (signGL K J)) = 2 := by
        rw [← hψ't, orderOf_injective _ hinj']
        exact ht
      obtain ⟨h1b, h1n, h1c⟩ := split_pair_hyps hK hinj hInn' ha' hb'
      obtain ⟨h2b, h2n, h2c⟩ := split_pair_hyps hK hinj hInn' hc' hd'
      refine Or.inr ⟨hq5 h3, ψ', hinj', hInn', hpre, a', b', c', d', hab, hcd, hpair, ?_, ?_⟩
      · rw [hψ't]
        exact pair_actsProperly hinj hAt hab h1b h1n h1c (hYne hinj') (hψ't ▸ hYO' hinj')
      · rw [hψ't]
        exact pair_actsProperly hinj hAt hcd h2b h2n h2c (hYne hinj') (hψ't ▸ hYO' hinj')
    ·
      have hAm : (A : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K) * A = (l : K) • 1 := by
        have := congrArg Units.val hl
        rw [Units.val_mul] at this
        rw [← this]
        ext i j
        simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
      obtain ⟨H, hH⟩ := exists_quad_normal_form (m := 2) hsq (A := A) hAm
      have hHGL : H * A * H⁻¹ = quadGL (l : K) 2 hsq := Units.ext hH
      obtain ⟨hinj', hInn', hpre⟩ := hconj H
      set ψ' := (MulAut.conj (conjAut 4 K H)).toMonoidHom.comp ψ with hψ'def
      have hψ't : ψ' t = conjAut 4 K (quadGL (l : K) 2 hsq) := by
        change conjAut 4 K H * ψ t * (conjAut 4 K H)⁻¹ = _
        rw [hα, ← map_inv, ← map_mul, ← map_mul, hHGL]
      by_cases h3 : Nat.card K = 3
      · exfalso
        refine hbot hinj' ?_
        rw [hψ't]
        exact nonsplit_oddCoreIn_eq_bot_three hsq le_rfl h3 hinj hInn'
      have hAt : orderOf (conjAut 4 K (quadGL (l : K) 2 hsq)) = 2 := by
        rw [← hψ't, orderOf_injective _ hinj']
        exact ht
      obtain ⟨h1b, h1n, h1c⟩ := quad_pair_hyps hsq hinj hInn' (0 : Fin 2)
      obtain ⟨h2b, h2n, h2c⟩ := quad_pair_hyps hsq hinj hInn' (1 : Fin 2)
      have hab : (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) : Fin 4) ≠
          finProdFinEquiv ((0 : Fin 2), (1 : Fin 2)) := by decide
      have hcd : (finProdFinEquiv ((1 : Fin 2), (0 : Fin 2)) : Fin 4) ≠
          finProdFinEquiv ((1 : Fin 2), (1 : Fin 2)) := by decide
      refine Or.inr ⟨hq5 h3, ψ', hinj', hInn', hpre, _, _, _, _, hab, hcd, by decide, ?_, ?_⟩
      · rw [hψ't]
        exact pair_actsProperly hinj hAt hab h1b h1n h1c (hYne hinj') (hψ't ▸ hYO' hinj')
      · rw [hψ't]
        exact pair_actsProperly hinj hAt hcd h2b h2n h2c (hYne hinj') (hψ't ▸ hYO' hinj')
  · rw [pow_one] at hα
    exfalso
    by_cases hσ : σ = 1
    · subst hσ
      have hα' : ψ t = conjAut 4 K A * dualAut 4 K := by rw [hα, map_one, mul_one]
      have hsq : ψ t ^ 2 = 1 := by
        rw [← map_pow]
        have h := pow_orderOf_eq_one t
        rw [ht] at h
        rw [h, map_one]
      have hsq' : (conjAut 4 K A * fieldAut 4 K 1 * dualAut 4 K) ^ 2 = 1 := by
        rw [← hα]
        exact hsq
      rcases LocalAnalysis.ComponentInitial.OddHigherLinear.transpose_eq_or_eq_neg_of_sq hn A
          hsq' with hA | hA
      · exact hY (orthogonal_eq_bot hK hn hinj hψ hInn hA hα' hYO)
      · refine hY (eq_bot_of_oddCoreIn hψ ?_ hYO)
        rw [hα']
        exact symplectic_oddCoreIn_eq_bot hK hn hinj hInn hA
    · exact hY (graphField_eq_bot hℓ hℓ2 hf hKc hn hinj hψ hInn ht hσ hα hYO)

end CFSG.ComponentClassification.Burgoyne.B
