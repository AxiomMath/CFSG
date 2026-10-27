module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSU4
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSL4Twin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSU

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (compInd signMat compInd_commute_diagonal
  conj_embedding conj_range_normal eq_bot_of_oddCoreIn)
open scoped MatrixGroups

variable {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K) {n : ℕ}

theorem exists_uconj_transfer' (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))} (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ.range)
    {t : X} {A A' : uU h n} (htA : ψ t = uConjAut h (by omega) A) (H : uU h n) {c : K}
    (hc : c ≠ 0)
    (hH : ((((H : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((H : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        c • ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ ψ' : X →* MulAut (StatedProj (StatedSU n (p ^ f) K)), Function.Injective ψ' ∧
      (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
        MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ'.range ∧
      ψ' t = uConjAut h (by omega) A' ∧
      ∀ x, ψ' x ∈ (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
          MulAut (StatedProj (StatedSU n (p ^ f) K))).range ↔
        ψ x ∈ (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
          MulAut (StatedProj (StatedSU n (p ^ f) K))).range := by
  obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (uConjAut h (by omega) H⁻¹)
  have hN : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range.Normal := conj_range_normal
  refine ⟨_, hinj', hInn', ?_, fun x => ?_⟩
  · change uConjAut h (by omega) H⁻¹ * ψ t * (uConjAut h (by omega) H⁻¹)⁻¹ = _
    rw [htA, ← map_inv, inv_inv, ← map_mul, ← map_mul]
    refine uConjAut_eq_of_eq_smul h hn hc ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
    exact hH
  · change uConjAut h (by omega) H⁻¹ * ψ x * (uConjAut h (by omega) H⁻¹)⁻¹ ∈ _ ↔ _
    constructor
    · intro h'
      have := hN.conj_mem _ h' (uConjAut h (by omega) H⁻¹)⁻¹
      rwa [inv_inv, show (uConjAut h (by omega) H⁻¹)⁻¹ * (uConjAut h (by omega) H⁻¹ * ψ x *
        (uConjAut h (by omega) H⁻¹)⁻¹) * uConjAut h (by omega) H⁻¹ = ψ x by group] at this
    · intro h'
      exact hN.conj_mem _ h' _

theorem usplit_oddCoreIn_eq_bot_three (hp2 : p ≠ 2) (hn : 3 ≤ n) (h3 : p ^ f = 3)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J) :
    oddCoreIn B (uConjAut h (by omega) (uSign h J)) = ⊥ := by
  have := h.finite
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨α, β, hα, hβ, rfl⟩ := split_oddCoreIn h hp2 hn hinj hB ha hb hy
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have h4 : ∀ γ : Kˣ, h.norm (γ : K) = 1 → (γ : K) ^ 4 = 1 := by
    intro γ hγ
    rw [UnitaryFieldData.norm, h.bar_apply, h3] at hγ
    linear_combination hγ
  have hD4 : uDiagJ h J α β hα hβ ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_uDiagJ, diagonal_pow,
      OneMemClass.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    ext i
    simp only [Pi.pow_apply]
    split_ifs
    · exact h4 α hα
    · exact h4 β hβ
  have hy4 : (uConjAut h (by omega) (uDiagJ h J α β hα hβ)) ^ 4 = 1 := by
    rw [← map_pow, hD4, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hy4
  have h1 : orderOf (uConjAut h (by omega) (uDiagJ h J α β hα hβ)) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have h3' : orderOf (uConjAut h (by omega) (uDiagJ h J α β hα hβ)) ≠ 3 := fun e3 => by
      rw [e3] at hdvd
      norm_num at hdvd
    obtain ⟨k, hk⟩ := hodd
    omega
  exact mem_bot.2 (orderOf_eq_one_iff.1 h1)

theorem usplit_pair_hyps (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J) :
    compInd K {a, b} * (((uSign h J : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (((uSign h J : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K {a, b} ∧
      ¬ PairBlockScalar a b (((uSign h J : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      ∀ y ∈ oddCoreIn B (uConjAut h (by omega) (uSign h J)), ∃ D : uU h n,
        y = uConjAut h (by omega) D ∧
        compInd K {a, b} * ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K {a, b} ∧
        (PairBlockScalar a b ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
          uConjAut h (by omega) D = 1) := by
  have h2 := utwo_ne_zero h hp2
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · rw [coe_uSign, signMat]
    exact compInd_commute_diagonal _ _
  · rintro ⟨h', -, -⟩
    rw [coe_uSign, signMat, diagonal_apply_eq, diagonal_apply_eq] at h'
    simp only [ha, hb, ↓reduceIte] at h'
    exact h2 (by linear_combination -h')
  · obtain ⟨α, β, hα, hβ, rfl⟩ := split_oddCoreIn h hp2 hn hinj hB ha hb hy
    refine ⟨_, rfl, ?_, fun hs => ?_⟩
    · rw [coe_uDiagJ]
      exact compInd_commute_diagonal _ _
    · obtain ⟨e1, -, -⟩ := hs
      rw [coe_uDiagJ, diagonal_apply_eq, diagonal_apply_eq] at e1
      simp only [ha, hb, ↓reduceIte] at e1
      refine (uConjAut_eq_one_iff h hn _).2 ⟨α, ?_⟩
      apply Units.ext
      rw [coe_uDiagJ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      congr 1
      ext i
      split_ifs
      · rfl
      · exact e1.symm

theorem upaired_oddCoreIn_eq_bot_three (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (h3 : p ^ f = 3)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))).range ≤ B)
    {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    oddCoreIn B (uConjAut h (by omega) (uPairA h h2 hl hN)) = ⊥ := by
  have := h.finite
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨a, b, D, hab, hD, rfl⟩ := paired_oddCoreIn h hp2 h2 hm hinj hB hl hN hy
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hK9 : Nat.card K = 9 := by rw [h.card_eq_sq, h3]; norm_num
  have : Fintype K := Fintype.ofFinite K
  have h8 : ∀ c : K, c ≠ 0 → c ^ 8 = 1 := fun c hc => by
    have := FiniteField.pow_card_sub_one_eq_one c hc
    rwa [← Nat.card_eq_fintype_card, hK9] at this
  have ha : a ≠ 0 := fun e => by rw [e, map_zero, zero_mul] at hab; exact zero_ne_one hab
  have hb : b ≠ 0 := fun e => by rw [e, mul_zero] at hab; exact zero_ne_one hab
  have hD8 : D ^ 8 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD, prPhi_pow h2 hl, smul_pow, smul_pow,
      h8 a ha, h8 b hb, one_pow, one_smul, prPhi_one h2 hl, OneMemClass.coe_one, Units.val_one]
  have hy8 : (uConjAut h (by omega) D) ^ 8 = 1 := by rw [← map_pow, hD8, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hy8
  have h1 : orderOf (uConjAut h (by omega) D) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hodd
    have h3' : orderOf (uConjAut h (by omega) D) ≠ 3 := fun e3 => by
      rw [e3] at hdvd
      norm_num at hdvd
    have h5' : orderOf (uConjAut h (by omega) D) ≠ 5 := fun e5 => by
      rw [e5] at hdvd
      norm_num at hdvd
    have h7' : orderOf (uConjAut h (by omega) D) ≠ 7 := fun e7 => by
      rw [e7] at hdvd
      norm_num at hdvd
    omega
  exact mem_bot.2 (orderOf_eq_one_iff.1 h1)

theorem upaired_pair_hyps (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))).range ≤ B)
    {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) (i : Fin m) :
    compInd K {finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inr i)} *
        (((uPairA h h2 hl hN : uU h (m + m)) : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) =
        (((uPairA h h2 hl hN : uU h (m + m)) : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) *
          compInd K {finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inr i)} ∧
      ¬ PairBlockScalar (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr i))
        (((uPairA h h2 hl hN : uU h (m + m)) : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) ∧
      ∀ y ∈ oddCoreIn B (uConjAut h (by omega) (uPairA h h2 hl hN)), ∃ D : uU h (m + m),
        y = uConjAut h (by omega) D ∧
        compInd K {finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inr i)} *
          ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
          ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *
            compInd K {finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inr i)} ∧
        (PairBlockScalar (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr i))
          ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) →
          uConjAut h (by omega) D = 1) := by
  have hn : 3 ≤ m + m := by omega
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · rw [coe_uPairA, prA_eq_prPhi h2 hl, show -(l • (1 : Matrix (Fin m) (Fin m) K)) = (-l) • 1 by
      rw [neg_smul]]
    exact prPhi_commute_compInd h2 hl _ _ _
  · rintro ⟨-, h', -⟩
    rw [coe_uPairA, prA, prFin_apply, fromBlocks_apply₁₂, one_apply_eq] at h'
    exact one_ne_zero h'
  · obtain ⟨a, b, D, hab, hD, rfl⟩ := paired_oddCoreIn h hp2 h2 hm hinj hB hl hN hy
    refine ⟨D, rfl, by rw [hD]; exact prPhi_commute_compInd h2 hl _ _ _, fun hs => ?_⟩
    obtain ⟨-, e1, -⟩ := hs
    rw [hD, prPhi_eq h2 hl, prFin_apply, fromBlocks_apply₁₂] at e1
    simp only [Matrix.smul_apply, Matrix.sub_apply, one_apply_eq, smul_eq_mul, mul_one] at e1
    have hab' : a = b := by
      rcases mul_eq_zero.1 e1 with e2 | e2
      · exact absurd e2 (inv_ne_zero (mul_ne_zero h2 hl))
      · exact sub_eq_zero.1 e2
    subst hab'
    have ha : a ≠ 0 := fun e => by rw [e, map_zero, zero_mul] at hab; exact zero_ne_one hab
    refine (uConjAut_eq_one_iff h hn D).2 ⟨Units.mk0 a ha, Units.ext ?_⟩
    rw [hD, prPhi_smul, prPhi_one h2 hl, GeneralLinearGroup.coe_scalar,
      Matrix.smul_one_eq_diagonal]
    rfl

theorem su4_twin_X (hp2 : p ≠ 2) (hn4 : n = 4)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {Y : Subgroup X} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCentralizerCore t) :
    (∃ A : uU h n, ψ t = uConjAut h (by omega) A ∧ ∃ (H : uU h n) (J₀ : Finset (Fin n)) (l : K),
      l ≠ 0 ∧ Odd J₀.card ∧
      (((H : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((H : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J₀) ∨
    (5 ≤ p ^ f ∧ ∃ ψ' : X →* MulAut (StatedProj (StatedSU n (p ^ f) K)),
      Function.Injective ψ' ∧
      (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
        MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ'.range ∧
      (∀ x, ψ' x ∈ (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
          MulAut (StatedProj (StatedSU n (p ^ f) K))).range ↔
        ψ x ∈ (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
          MulAut (StatedProj (StatedSU n (p ^ f) K))).range) ∧
      ∃ (a b c d : Fin n) (_ : a ≠ b) (_ : c ≠ d),
        (∀ x : Fin n, x ∈ ({a, b} : Finset (Fin n)) ↔ x ∉ ({c, d} : Finset (Fin n))) ∧
        ActsProperly (ψ' t) (Y.map ψ') (slice (uBlock p f K {a, b})) ⊥ ∧
        ActsProperly (ψ' t) (Y.map ψ') (slice (uBlock p f K {c, d})) ⊥) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 := utwo_ne_zero h hp2
  have hn : 3 ≤ n := by omega
  have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨e, _⟩ => by omega
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hcard : p ^ f = 3 ∨ 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      obtain ⟨k, hk⟩ := hpodd
      omega
    have : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    obtain ⟨k, hk⟩ : Odd (p ^ f) := hpodd.pow
    omega
  have hYne : ∀ {ψ' : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))},
      Function.Injective ψ' → Y.map ψ' ≠ ⊥ :=
    fun h' hmap => hY ((map_eq_bot_iff_of_injective _ h').1 hmap)
  have hYO' : ∀ {ψ' : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))},
      Function.Injective ψ' → Y.map ψ' ≤ oddCoreIn ψ'.range (ψ' t) := fun h' => by
    rw [← map_oddCentralizerCore_of_injective h']
    exact map_mono hYO
  have hbot : ∀ {ψ' : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))},
      Function.Injective ψ' → oddCoreIn ψ'.range (ψ' t) = ⊥ → False :=
    fun h' e => hY (eq_bot_of_oddCoreIn h' e hYO)
  obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut h hn hq' (ψ t)
  have hsq : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ 2 = 1 := by
    rw [← hα, ← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  rcases uFieldAut_eq_or_of_sq h hn hq' hsq with rfl | hφ
  swap
  ·
    exfalso
    have hφe : φ = barEq h := RingEquiv.ext hφ
    subst hφe
    rw [graph_sq] at hsq
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
    have hAc : M * M.map h.bar = (c : K) • 1 := by
      have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uGlAut]
        at e
      change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (barEq h) = _
      rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    refine hbot hψ ?_
    rw [hα]
    exact graph_oddCoreIn_eq_bot h hp2 hn hinj hInn hAc
  rw [map_one, mul_one] at hα hsq
  rw [← map_pow] at hsq
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
  have hAA : M * M = (c : K) • 1 := by
    have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] at e
    rw [← pow_two, e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hN : h.norm (c : K) = 1 := by
    have e : ((M * M).map h.bar)ᵀ * (M * M) = 1 := by
      rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ M M, hU,
        Matrix.one_mul, hU]
    rw [hAA] at e
    have e1 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
    simp [Matrix.mul_apply, Matrix.one_apply] at e1
    rw [UnitaryFieldData.norm, mul_comm]
    simpa [Matrix.smul_apply, Matrix.one_apply] using e1
  obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one h hp2 hN
  have hAA' : M * M = (l ^ 2) • 1 := by rw [hAA, hlc]
  have hNl : h.norm l * h.norm l = 1 := by
    rw [← hN, ← hlc, UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow]
    ring
  have htt : ∀ c' : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c' := by
    intro c' e
    have h1 : uConjAut h (by omega) A = 1 := (uConjAut_eq_one_iff h hn A).2 ⟨c', e⟩
    rw [h1, ← map_one ψ] at hα
    have := hψ hα
    rw [this, orderOf_one] at ht
    exact absurd ht (by decide)
  rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
  ·
    have hNi : h.bar l⁻¹ * l⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_one]
    have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = 1 := by
      rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
        ext i j; simp [map_mul]]
      rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
    have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul]
      rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
    obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form h h2 hU' hA'2
    set HG := uGL h Hm hHU with hHG
    have hHi : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (Hm.map h.bar)ᵀ := rfl
    have hconj : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M *
        ((HG : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J := by
      rw [hHi, coe_uGL]
      have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
        Matrix.one_mul]
    have hHH : Hm * (Hm.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
    have hJ : ∃ a ∈ J, ∃ b, b ∉ J := by
      by_contra hcon
      push Not at hcon
      obtain ⟨s, hs, hsJ⟩ : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
        by_cases hne : J.Nonempty
        · obtain ⟨a, ha⟩ := hne
          refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
          ext i j
          simp [signMat, diagonal_apply, one_apply, hcon a ha i]
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          refine ⟨1, one_ne_zero, ?_⟩
          ext i j
          simp [signMat, diagonal_apply, one_apply, hne]
      have e : l⁻¹ • M = s • 1 := by
        calc l⁻¹ • M = (l⁻¹ • M) * (Hm * (Hm.map h.bar)ᵀ) := by rw [hHH, Matrix.mul_one]
          _ = (Hm * signMat K J) * (Hm.map h.bar)ᵀ := by rw [← Matrix.mul_assoc, hHA]
          _ = s • 1 := by
              rw [hsJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
      apply htt (Units.mk0 (l * s) (mul_ne_zero hl0 hs))
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      change M = _
      have e2 : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      rw [e2, e, smul_smul, Matrix.smul_one_eq_diagonal]
      rfl
    obtain ⟨a, ha, b, hb⟩ := hJ
    obtain ⟨ψ', hinj', hInn', hψ't, hpre⟩ := exists_uconj_transfer' h hn hψ hInn hα
      ⟨HG, uGL_mem h _ _⟩ hl0 (A' := uSign h J) (by rw [coe_uSign]; exact hconj)
    rcases hcard with h3 | h5
    · exact (hbot hinj' (by
        rw [hψ't]
        exact usplit_oddCoreIn_eq_bot_three h hp2 hn h3 hinj hInn' ha hb)).elim
    by_cases hJodd : Odd J.card
    · exact Or.inl ⟨A, hα, ⟨HG, uGL_mem h _ _⟩, J, l, hl0, hJodd, hconj⟩
    subst hn4
    have hJ2 : J.card = 2 := by
      have h1 : 1 ≤ J.card := Finset.card_pos.2 ⟨a, ha⟩
      have h3' : J.card ≤ 3 := by
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
          ⟨Finset.subset_univ J, fun h' => hb (h' ▸ Finset.mem_univ b)⟩)
        rw [Finset.card_univ, Fintype.card_fin] at this
        omega
      rw [Nat.not_odd_iff_even] at hJodd
      obtain ⟨k, hk⟩ := hJodd
      omega
    obtain ⟨a', b', c', d', ha', hb', hc', hd', hab, hcd, hpair⟩ := exists_pairs_of_card_two hJ2
    have hAt : orderOf (uConjAut h (by omega) (uSign h J)) = 2 := by
      rw [← hψ't, orderOf_injective _ hinj']
      exact ht
    obtain ⟨h1b, h1n, h1c⟩ := usplit_pair_hyps h hp2 hn hinj hInn' ha' hb'
    obtain ⟨h2b, h2n, h2c⟩ := usplit_pair_hyps h hp2 hn hinj hInn' hc' hd'
    refine Or.inr ⟨h5, ψ', hinj', hInn', hpre, a', b', c', d', hab, hcd, hpair, ?_, ?_⟩
    · rw [hψ't]
      exact uPair_actsProperly h hp2 h5 _ hinj hAt hab h1b h1n h1c (hYne hinj')
        (hψ't ▸ hYO' hinj')
    · rw [hψ't]
      exact uPair_actsProperly h hp2 h5 _ hinj hAt hcd h2b h2n h2c (hYne hinj')
        (hψ't ▸ hYO' hinj')
  ·
    have hNi : h.bar l⁻¹ * l⁻¹ = -1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_neg, inv_one]
    have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = -1 := by
      rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
        ext i j; simp [map_mul]]
      rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, neg_one_smul]
    have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul]
      rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
    obtain ⟨m, rfl⟩ := exists_half_of_antiunitary h h2 hU' hA'2
    have hm : 2 ≤ m := by omega
    obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form h h2 hU' hA'2 hl0 hN1
    set HG := uGL h Hm hHU with hHG
    have hHi : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
        Matrix (Fin (m + m)) (Fin (m + m)) K) = (Hm.map h.bar)ᵀ := rfl
    have hconj : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
        Matrix (Fin (m + m)) (Fin (m + m)) K) * M *
        ((HG : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
          (1 : K) • ((uPairA (m := m) h h2 hl0 hN1 : GL (Fin (m + m)) K) :
            Matrix (Fin (m + m)) (Fin (m + m)) K) := by
      rw [hHi, coe_uGL, coe_uPairA, one_smul]
      have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
        Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
      congr 2
      · rw [smul_zero]
      · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      · rw [smul_smul, ← sq]
      · rw [smul_zero]
    obtain ⟨ψ', hinj', hInn', hψ't, hpre⟩ := exists_uconj_transfer' h hn hψ hInn hα
      ⟨HG, uGL_mem h _ _⟩ one_ne_zero hconj
    rcases hcard with h3 | h5
    · exact (hbot hinj' (by
        rw [hψ't]
        exact upaired_oddCoreIn_eq_bot_three h hp2 h2 hm h3 hinj hInn' hl0 hN1)).elim
    obtain rfl : m = 2 := by omega
    have hAt : orderOf (uConjAut h (by omega) (uPairA (m := 2) h h2 hl0 hN1)) = 2 := by
      rw [← hψ't, orderOf_injective _ hinj']
      exact ht
    obtain ⟨h1b, h1n, h1c⟩ := upaired_pair_hyps h hp2 h2 hm hinj hInn' hl0 hN1 0
    obtain ⟨h2b, h2n, h2c⟩ := upaired_pair_hyps h hp2 h2 hm hinj hInn' hl0 hN1 1
    have hab : finSumFinEquiv (Sum.inl (0 : Fin 2)) ≠
        (finSumFinEquiv (Sum.inr (0 : Fin 2)) : Fin (2 + 2)) := by decide
    have hcd : finSumFinEquiv (Sum.inl (1 : Fin 2)) ≠
        (finSumFinEquiv (Sum.inr (1 : Fin 2)) : Fin (2 + 2)) := by decide
    refine Or.inr ⟨h5, ψ', hinj', hInn', hpre, _, _, _, _, hab, hcd, by decide, ?_, ?_⟩
    · rw [hψ't]
      exact uPair_actsProperly h hp2 h5 _ hinj hAt hab h1b h1n h1c (hYne hinj')
        (hψ't ▸ hYO' hinj')
    · rw [hψ't]
      exact uPair_actsProperly h hp2 h5 _ hinj hAt hcd h2b h2n h2c (hYne hinj')
        (hψ't ▸ hYO' hinj')

end CFSG.ComponentClassification.Burgoyne.B
