module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsLift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLinear
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.Quasithin (perfectCore derivedSeriesOf)
open scoped commutatorElement

section Root

variable {K : Type} [Field K] {n : ℕ}

@[expose] def trSL (i j : Fin n) (hij : i ≠ j) (c : K) : SpecialLinearGroup (Fin n) K :=
  ⟨transvection i j c, det_transvection_of_ne i j hij c⟩

theorem coe_trSL (i j : Fin n) (hij : i ≠ j) (c : K) :
    ((trSL i j hij c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + single i j c :=
  rfl

theorem trSL_mul (i j : Fin n) (hij : i ≠ j) (a b : K) :
    trSL i j hij a * trSL i j hij b = trSL i j hij (a + b) :=
  Subtype.ext (transvection_mul_transvection_same i j hij a b)

theorem trSL_inv (i j : Fin n) (hij : i ≠ j) (a : K) :
    (trSL i j hij a)⁻¹ = trSL i j hij (-a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [trSL_mul, add_neg_cancel]
  exact Subtype.ext (transvection_zero i j)

theorem single_neg' (i j : Fin n) (c : K) :
    (single i j (-c) : Matrix (Fin n) (Fin n) K) = -single i j c := by
  rw [eq_neg_iff_add_eq_zero, ← single_add, neg_add_cancel, single_zero]

theorem trSL_commute {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') (hji : j ≠ i')
    (hj'i : j' ≠ i) (a b : K) :
    trSL i j hij a * trSL i' j' hij' b = trSL i' j' hij' b * trSL i j hij a := by
  apply Subtype.ext
  change transvection i j a * transvection i' j' b = transvection i' j' b * transvection i j a
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_of_ne _ _ _ _ hji, single_mul_single_of_ne _ _ _ _ hj'i, add_zero]
  abel

theorem trSL_comm {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a b : K) :
    ⁅trSL i j hij a, trSL j l hjl b⁆ = trSL i l hil (a * b) := by
  rw [commutatorElement_def, trSL_inv, trSL_inv]
  apply Subtype.ext
  change transvection i j a * transvection j l b * transvection i j (-a) *
    transvection j l (-b) = transvection i l (a * b)
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ hij.symm,
    single_mul_single_of_ne _ _ _ _ hil.symm, single_mul_single_of_ne _ _ _ _ hjl.symm, add_zero,
    mul_neg, neg_mul, single_neg']
  abel

end Root

section Standard

variable {K : Type} [Field K] {k : ℕ}

@[expose] def idxU (hk : 2 ≤ k) : Fin (2 + k) := finSumFinEquiv (Sum.inr ⟨0, by omega⟩)

@[expose] def idxV (hk : 2 ≤ k) : Fin (2 + k) := finSumFinEquiv (Sum.inr ⟨1, by omega⟩)

@[expose] def idxW (k : ℕ) : Fin (2 + k) := finSumFinEquiv (Sum.inl 0)

@[expose] def idxW' (k : ℕ) : Fin (2 + k) := finSumFinEquiv (Sum.inl 1)

theorem idxU_ne_idxV (hk : 2 ≤ k) : idxU hk ≠ idxV hk :=
  finSumFinEquiv.injective.ne (by simp [Fin.ext_iff])

theorem idxW_ne_idxU (hk : 2 ≤ k) : idxW k ≠ idxU hk := finSumFinEquiv.injective.ne (by simp)

theorem idxW'_ne_idxU (hk : 2 ≤ k) : idxW' k ≠ idxU hk := finSumFinEquiv.injective.ne (by simp)

theorem idxW_ne_idxV (hk : 2 ≤ k) : idxW k ≠ idxV hk := finSumFinEquiv.injective.ne (by simp)

theorem idxW'_ne_idxV (hk : 2 ≤ k) : idxW' k ≠ idxV hk := finSumFinEquiv.injective.ne (by simp)

theorem idxW_ne_idxW' (k : ℕ) : idxW k ≠ idxW' k :=
  finSumFinEquiv.injective.ne (by simp)

theorem blk_single_zero (i j : Fin 2) (c : K) :
    blk (single i j c) (0 : Matrix (Fin k) (Fin k) K) =
      single (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) c := by
  ext x y
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
  rw [blk, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, single_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rcases x with x | x <;> rcases y with y | y
  · rw [fromBlocks_apply₁₁, single_apply]
    simp
  · simp
  · simp
  · simp

theorem stdT_mem_perfectCore (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) :
    trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K) ∈ perfectCore (centralizer
      ({trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K)} :
        Set (SpecialLinearGroup (Fin (2 + k)) K))) := by
  set t₀ := trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K) with ht₀
  have hmat : (t₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk 1 (1 + single ⟨0, by omega⟩ ⟨1, by omega⟩ 1) := by
    rw [← one_add_smul_stdE hk, one_smul, stdE_eq_single]
    rfl
  have hL : (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range ≤
      centralizer ({t₀} : Set (SpecialLinearGroup (Fin (2 + k)) K)) := by
    rintro _ ⟨X, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    change blk (X : Matrix (Fin 2) (Fin 2) K) 1 * (t₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (t₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * blk (X : Matrix (Fin 2) (Fin 2) K) 1
    rw [hmat, blk_mul, blk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]
  have hperf : ⁅(blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range,
      (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range⁆ =
      (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range := by
    have hP := (CFSG.RankThree.PartOne.KCOrthogonal.sl2_isPerfect h4).commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hP]
  have hLP := CFSG.Quasithin.le_perfectCore_of_perfect hL hperf
  have hl₁ : trSL (idxW k) (idxW' k) (idxW_ne_idxW' k) (1 : K) ∈
      perfectCore (centralizer ({t₀} : Set (SpecialLinearGroup (Fin (2 + k)) K))) := by
    refine hLP ⟨tr₂ 0 1 (by decide), Subtype.ext ?_⟩
    rw [coe_blkSL₁_tr₂, blk_single_zero]
    rfl
  have hl₂ : trSL (idxW' k) (idxW k) (idxW_ne_idxW' k).symm (1 : K) ∈
      perfectCore (centralizer ({t₀} : Set (SpecialLinearGroup (Fin (2 + k)) K))) := by
    refine hLP ⟨tr₂ 1 0 (by decide), Subtype.ext ?_⟩
    rw [coe_blkSL₁_tr₂, blk_single_zero]
    rfl
  have hc₁ : trSL (idxU hk) (idxW k) (idxW_ne_idxU hk).symm (1 : K) ∈
      centralizer ({t₀} : Set (SpecialLinearGroup (Fin (2 + k)) K)) := by
    rw [mem_centralizer_singleton_iff]
    exact trSL_commute (idxW_ne_idxU hk).symm (idxU_ne_idxV hk) (idxW_ne_idxU hk)
      (idxU_ne_idxV hk).symm 1 1
  have hc₂ : trSL (idxW k) (idxV hk) (idxW_ne_idxV hk) (1 : K) ∈
      centralizer ({t₀} : Set (SpecialLinearGroup (Fin (2 + k)) K)) := by
    rw [mem_centralizer_singleton_iff]
    exact trSL_commute (idxW_ne_idxV hk) (idxU_ne_idxV hk) (idxU_ne_idxV hk).symm
      (idxW_ne_idxV hk).symm 1 1
  have hs₁ := commutatorElement_mem_perfectCore hc₁ hl₁
  have hs₂ := commutatorElement_mem_perfectCore' hc₂ hl₂
  rw [trSL_comm _ _ (idxW'_ne_idxU hk).symm, mul_one] at hs₁
  rw [trSL_comm _ _ (idxW'_ne_idxV hk), mul_one] at hs₂
  have h := trSL_comm (idxW'_ne_idxU hk).symm (idxW'_ne_idxV hk) (idxU_ne_idxV hk) (1 : K) 1
  rw [mul_one] at h
  have hmem : ⁅trSL (idxU hk) (idxW' k) (idxW'_ne_idxU hk).symm (1 : K),
      trSL (idxW' k) (idxV hk) (idxW'_ne_idxV hk) (1 : K)⁆ ∈
      perfectCore (centralizer ({t₀} : Set (SpecialLinearGroup (Fin (2 + k)) K))) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hs₁ hs₂) (inv_mem hs₁)) (inv_mem hs₂)
  rw [h] at hmem
  exact hmem

theorem mem_statedSL_iff' {n : ℕ} {g : GL (Fin n) K} :
    g ∈ StatedSL n K ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem mem_perfectCore_of_transvection [CharP K 2] (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K)
    {M : GL (Fin (2 + k)) K} (hM2 : orderOf M = 2) (hr : commRank M = 1) :
    M ∈ perfectCore (StatedSL (2 + k) K ⊓ centralizer ({M} : Set (GL (Fin (2 + k)) K))) := by
  obtain ⟨P, hP⟩ := exists_conj_of_sq_eq_zero (sub_one_mul_self_eq_zero hM2) (stdE_mul_self hk)
    (by rw [rank_stdE]; exact hr)
  set t₀ := trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K) with ht₀
  have hPM : P * M * P⁻¹ = SpecialLinearGroup.toGL t₀ := by
    apply Units.ext
    have hPP : (P : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
        ((P⁻¹ : GL (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hM1 : (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 + ((M : Matrix _ _ K) - 1) := by
      rw [add_sub_cancel]
    rw [Units.val_mul, Units.val_mul, hM1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP, hP,
      stdE_eq_single]
    rfl
  have h₀ := map_mem_perfectCore_of_le (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin (2 + k)) K →* GL (Fin (2 + k)) K)
    (K := StatedSL (2 + k) K ⊓ centralizer ({SpecialLinearGroup.toGL t₀} : Set _))
    (by
      rintro _ ⟨c, hc, rfl⟩
      refine mem_inf.2 ⟨by rw [statedSL_eq_range_toGL]; exact ⟨c, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        mem_centralizer_singleton_iff.1 hc])
    (stdT_mem_perfectCore hk h4)
  have h₁ := map_mem_perfectCore_of_le (MulAut.conj P⁻¹).toMonoidHom
    (K := StatedSL (2 + k) K ⊓ centralizer ({M} : Set (GL (Fin (2 + k)) K))) (by
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨hgS, hgc⟩ := mem_inf.1 hg
      refine mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_statedSL_iff'] at hgS ⊢
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul,
          det_mul, hgS, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
      · rw [mem_centralizer_singleton_iff] at hgc ⊢
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hM' : M = P⁻¹ * SpecialLinearGroup.toGL t₀ * P := by rw [← hPM]; group
        rw [hM', inv_inv]
        calc P⁻¹ * g * P * (P⁻¹ * SpecialLinearGroup.toGL t₀ * P) =
            P⁻¹ * (g * SpecialLinearGroup.toGL t₀) * P := by group
          _ = P⁻¹ * (SpecialLinearGroup.toGL t₀ * g) * P := by rw [hgc]
          _ = P⁻¹ * SpecialLinearGroup.toGL t₀ * P * (P⁻¹ * g * P) := by group) h₀
  have hM' : (MulAut.conj P⁻¹).toMonoidHom (SpecialLinearGroup.toGL t₀) = M := by
    change P⁻¹ * SpecialLinearGroup.toGL t₀ * P⁻¹⁻¹ = M
    rw [← hPM, inv_inv]
    group
  rwa [hM'] at h₁

end Standard

section Families

variable {G : Type} [Group G] {A : Subgroup G}

theorem mem_perfectCore_of_linear {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) (e : rankTwoQuot A ≃* StatedProj (StatedSL n K))
    (hodd : Odd (Nat.card (center ↥A))) {x : G} (hx : IsInvolutionOfRank e x 1) :
    x ∈ perfectCore (A ⊓ centralizer ({x} : Set G)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  obtain ⟨hxo, M, hM, hM2, hr⟩ := hx
  have hx2 : x ^ 2 = 1 := by
    rw [← hxo]
    exact pow_orderOf_eq_one x
  exact mem_perfectCore_of_represents e hodd hx2 hM
    (mem_perfectCore_of_transvection (by omega) h4 hM2 hr)

@[expose] def SymplecticTransvectionPerfect : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 2 ≤ n → 4 ≤ Nat.card K →
    ∀ M : GL (Fin n ⊕ Fin n) K, M ∈ StatedSp n K → orderOf M = 2 → commRank M = 1 →
      M ∈ perfectCore (StatedSp n K ⊓ centralizer ({M} : Set (GL (Fin n ⊕ Fin n) K)))

@[expose] def UnitaryTransvectionPerfect : Prop :=
  ∀ (n m : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ n → 4 ≤ 2 ^ m → Nat.card K = (2 ^ m) ^ 2 →
    ∀ M : GL (Fin n) K, M ∈ StatedSU n (2 ^ m) K → orderOf M = 2 → commRank M = 1 →
      M ∈ perfectCore (StatedSU n (2 ^ m) K ⊓ centralizer ({M} : Set (GL (Fin n) K)))

@[expose] def OrthogonalSingularPerfect : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → 4 ≤ Nat.card K →
    (∀ M : GL (Fin n ⊕ Fin n) K, M ∈ StatedOmega (StatedQuadPlus n K) → orderOf M = 2 →
      commRank M = 2 →
      (∀ v, StatedQuadPlus n K (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) = 0) →
      M ∈ perfectCore (StatedOmega (StatedQuadPlus n K) ⊓
        centralizer ({M} : Set (GL (Fin n ⊕ Fin n) K)))) ∧
    ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ M : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K,
        M ∈ StatedOmega (StatedQuadMinus n K b c) → orderOf M = 2 → commRank M = 2 →
        (∀ v, StatedQuadMinus n K b c (((M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) - 1) *ᵥ v) = 0) →
        M ∈ perfectCore (StatedOmega (StatedQuadMinus n K b c) ⊓
          centralizer ({M} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)))

theorem classicalPrimaryPerfect_of (hS : SymplecticTransvectionPerfect)
    (hU : UnitaryTransvectionPerfect) (hO : OrthogonalSingularPerfect) :
    ClassicalPrimaryPerfect := by
  intro G _ _ A D _ hodd hq x hx
  have hsq : orderOf x = 2 → x ^ 2 = 1 := fun h => by rw [← h]; exact pow_orderOf_eq_one x
  cases D with
  | linear n m hn hm hnm K hK e =>
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hm hK
    exact mem_perfectCore_of_linear hn (by rw [hK]; exact hq) e hodd hx
  | unitary n m hn hm K hK e =>
    obtain ⟨hxo, M, hM, hM2, hr⟩ := hx
    exact mem_perfectCore_of_represents e hodd (hsq hxo) hM (hU n m K hn hq hK M hM.2.1 hM2 hr)
  | symplectic n m hn hm hnm K hK e =>
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hm hK
    obtain ⟨hxo, M, hM, hM2, hr⟩ := hx
    exact mem_perfectCore_of_represents e hodd (hsq hxo) hM
      (hS n K hn (by rw [hK]; exact hq) M hM.2.1 hM2 hr)
  | orthPlus n m hn hm K hK e =>
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hm hK
    obtain ⟨hxo, M, hM, hM2, hr, hQ⟩ := hx
    exact mem_perfectCore_of_represents e hodd (hsq hxo) hM
      ((hO n K hn (by rw [hK]; exact hq)).1 M hM.2.1 hM2 hr hQ)
  | orthMinus n m hn hm K hK b c hbc e =>
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hm hK
    obtain ⟨hxo, M, hM, hM2, hr, hQ⟩ := hx
    exact mem_perfectCore_of_represents e hodd (hsq hxo) hM
      ((hO n K hn (by rw [hK]; exact hq)).2 b c hbc M hM.2.1 hM2 hr hQ)

end Families

end CFSG.ComponentClassification.RankTwoClassical
