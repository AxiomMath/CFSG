module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd commute_compInd_iff signMat
  commute_signMat_iff exists_not_mem_pair)
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

abbrev prBase (x : Fin m ⊕ Fin m) : Fin m := x.elim id id

theorem prPhi_smul_one_apply (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (a b : K)
    {x y : Fin m ⊕ Fin m} (hxy : prBase x ≠ prBase y) :
    prPhi m l (a • 1) (b • 1) (finSumFinEquiv x) (finSumFinEquiv y) = 0 := by
  rw [prPhi_eq h2 hl, prFin_apply]
  rcases x with i | i <;> rcases y with j | j <;>
    simp only [prBase, Sum.elim_inl, Sum.elim_inr, id] at hxy <;>
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, one_apply, hxy]

theorem mem_prPair {x : Fin m ⊕ Fin m} (i : Fin m) :
    finSumFinEquiv x ∈ ({finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inr i)} :
      Finset (Fin (m + m))) ↔ prBase x = i := by
  rw [Finset.mem_insert, Finset.mem_singleton, finSumFinEquiv.injective.eq_iff,
    finSumFinEquiv.injective.eq_iff]
  rcases x with j | j <;> simp

theorem prPhi_commute_compInd (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (a b : K) (i : Fin m) :
    compInd K {finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inr i)} *
        prPhi m l (a • 1) (b • 1) =
      prPhi m l (a • 1) (b • 1) *
        compInd K {finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inr i)} := by
  rw [commute_compInd_iff]
  intro x y hxy
  obtain ⟨x', rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨y', rfl⟩ := finSumFinEquiv.surjective y
  rw [mem_prPair, mem_prPair] at hxy
  refine prPhi_smul_one_apply h2 hl a b fun e => ?_
  rw [e] at hxy
  tauto

theorem prPhi_pow (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (G G' : Matrix (Fin m) (Fin m) K)
    (k : ℕ) : prPhi m l G G' ^ k = prPhi m l (G ^ k) (G' ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, prPhi_one h2 hl]
  | succ k ih => rw [pow_succ, ih, prPhi_mul h2 hl, ← pow_succ, ← pow_succ]

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem paired_propAConclusionIn (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))).range ≤ B)
    {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {Y : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (uConjAut h (by omega) (uPairA h h2 hl hN))) :
    PropAConclusionIn B (uConjAut h (by omega) (uPairA h h2 hl hN)) Y := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hn : 3 ≤ m + m := by omega
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hcard : p ^ f = 3 ∨ 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      obtain ⟨k, hk⟩ := hpodd
      omega
    have : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hcore := fun {y} (hy : y ∈ oddCoreIn B (uConjAut h (by omega) (uPairA h h2 hl hN))) =>
    paired_oddCoreIn h hp2 h2 hm hinj hB hl hN hy
  set i₀ : Fin (m + m) := finSumFinEquiv (Sum.inl ⟨0, by omega⟩) with hi₀
  set j₀ : Fin (m + m) := finSumFinEquiv (Sum.inr ⟨0, by omega⟩) with hj₀
  have hij : i₀ ≠ j₀ := finSumFinEquiv.injective.ne Sum.inl_ne_inr
  rcases hcard with h3 | h5
  ·
    exfalso
    apply hY
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨a, b, D, hab, hD, rfl⟩ := hcore (hYO hy)
    have hodd := odd_orderOf_of_mem_oddCoreIn (hYO hy)
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
        h8 a ha, h8 b hb, one_pow, one_smul, prPhi_one h2 hl, OneMemClass.coe_one,
        Units.val_one]
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
  ·
    set F := CFSG.LieType.Steinberg.fixedSubfield K p f with hF
    have hFc : Nat.card F = p ^ f := CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq
    have h2F : (2 : F) ≠ 0 := fun e => h2 (by
      have h1 : ((1 + 1 : F) : K) = 1 + 1 := by rw [Subfield.coe_add, Subfield.coe_one]
      rw [← one_add_one_eq_two] at e ⊢
      rw [← h1, e, Subfield.coe_zero])
    have hF2 : ringChar F ≠ 2 := fun e => h2F (by
      have := ringChar.spec F 2
      exact_mod_cast (this.2 (by rw [e])))
    obtain ⟨e⟩ := nonempty_uBlock_pair_equiv h hij
    obtain ⟨k, hk⟩ := exists_not_mem_pair hn i₀ j₀
    have hLZ : ∀ g ∈ uBlock p f K {i₀, j₀},
        g ∈ (StatedScalars (Fin (m + m)) K).subgroupOf (StatedSU (m + m) (p ^ f) K) → g = 1 :=
      fun g hg hz => eq_one_of_mem_uBlock_scalars hk hg hz
    obtain ⟨ζ, hζ0, hζ, hζ2⟩ := exists_norm_one_sq_ne_one h
    have hoffR : ∀ {D : uU h (m + m)}, (∀ x ∈ slice (uBlock p f K {i₀, j₀}),
        uConjAut h (by omega) D * x = x * uConjAut h (by omega) D) →
        ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) i₀ j₀ = 0 := by
      intro D hcen
      have e1 := commute_of_centralize h hp2 h5 (by omega) hinj hij hcen
        (uDiag2_mem_uBlock h hij (by simp) (by simp) hζ0 hζ)
      rw [coe_uDiag2] at e1
      exact (entries_of_commute_diag hζ0 hζ2 e1 j₀ (Ne.symm hij)).1
    have hA₀ij : prA m l i₀ j₀ = 1 := by
      rw [prA, hi₀, hj₀, prFin_apply, fromBlocks_apply₁₂, one_apply_eq]
    have hA₀c : compInd K {i₀, j₀} * prA m l = prA m l * compInd K {i₀, j₀} := by
      rw [prA_eq_prPhi h2 hl, show -(l • (1 : Matrix (Fin m) (Fin m) K)) = (-l) • 1 by
        rw [neg_smul]]
      exact prPhi_commute_compInd h2 hl _ _ _
    have hA₀2 : uConjAut h (by omega)
        (uPairA (m := m) h h2 hl hN * uPairA (m := m) h h2 hl hN) = 1 := by
      refine (uConjAut_eq_one_iff h hn _).2 ⟨Units.mk0 (l ^ 2) (pow_ne_zero 2 hl),
        Units.ext ?_⟩
      rw [Subgroup.coe_mul, Units.val_mul, coe_uPairA, prA_mul_self h2 hl,
        GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
      rfl
    refine slice_propAConclusionIn hinj hB hLZ hF2 (by rw [hFc]; omega) (uPairSign_mem h hij) e
      (uPairSign_eq_neg_one h h2 hij e) (fun g hg => commute_uPairSign h h2 hij hg) ?_ ?_ hY hYO
      ?_ ?_ ?_ ?_
    ·
      intro g' hg' g hg
      have e1 := congrArg (fun x : StatedSU (m + m) (p ^ f) K =>
        ((x : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K)) hg'
      simp only [Subgroup.coe_mul, Units.val_mul, coe_uPairSign] at e1
      have hc := (commute_signMat_iff h2 {i₀, j₀} _).1 e1.symm
      refine conj_mem_uBlock (D := ((g' : GL (Fin (m + m)) K) :
        Matrix (Fin (m + m)) (Fin (m + m)) K))
        (Di := (((g'⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K)) ?_ ?_ hc hg ?_
      · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one]
      · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one]
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    ·
      apply orderOf_eq_prime
      · rw [← map_pow, pow_two, hA₀2]
      · intro h1
        obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn (uPairA h h2 hl hN)).1 h1
        have e1 := congrArg (fun M : GL (Fin (m + m)) K =>
          (M : Matrix (Fin (m + m)) (Fin (m + m)) K) i₀ j₀) hc
        simp only [coe_uPairA, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          diagonal_apply_ne _ hij, hA₀ij] at e1
        exact one_ne_zero e1
    ·
      exact uConjAut_mem_normalizer_slice h (by omega) (by rw [coe_uPairA]; exact hA₀c)
    ·
      by_contra hall
      push Not at hall
      have e1 := hoffR (D := uPairA h h2 hl hN) hall
      rw [coe_uPairA, hA₀ij] at e1
      exact one_ne_zero e1
    ·
      intro y hy
      obtain ⟨a, b, D, -, hD, rfl⟩ := hcore hy
      exact uConjAut_mem_normalizer_slice h (by omega) (by
        rw [hD]
        exact prPhi_commute_compInd h2 hl _ _ _)
    ·
      intro y hy hcen
      obtain ⟨a, b, D, -, hD, rfl⟩ := hcore hy
      have e1 := hoffR hcen
      rw [hD, hi₀, hj₀, prPhi_eq h2 hl, prFin_apply, fromBlocks_apply₁₂] at e1
      simp only [Matrix.smul_apply, Matrix.sub_apply, one_apply_eq, smul_eq_mul, mul_one] at e1
      have hab : a = b := by
        rcases mul_eq_zero.1 e1 with e2 | e2
        · exact absurd e2 (inv_ne_zero (mul_ne_zero h2 hl))
        · exact sub_eq_zero.1 e2
      subst hab
      have ha : a ≠ 0 := by
        intro e0
        have := (mem_uU h).1 D.2
        rw [hD, e0, zero_smul, show prPhi m l 0 0 = 0 by
          rw [show (0 : Matrix (Fin m) (Fin m) K) = (0 : K) • 1 by rw [zero_smul],
            prPhi_smul, zero_smul], Matrix.mul_zero] at this
        exact zero_ne_one (congrFun (congrFun this i₀) i₀)
      refine (uConjAut_eq_one_iff h hn D).2 ⟨Units.mk0 a ha, Units.ext ?_⟩
      rw [hD, prPhi_smul, prPhi_one h2 hl, GeneralLinearGroup.coe_scalar,
        Matrix.smul_one_eq_diagonal]
      rfl

end CFSG.ComponentClassification.Burgoyne.U
