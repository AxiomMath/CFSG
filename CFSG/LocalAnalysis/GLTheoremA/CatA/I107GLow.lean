module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107G

open CFSG.Open CFSG.Assembly

section Unipotent

variable {K : Type} [Field K] {d : ℕ}

@[expose] def blockEmbed (k : ℕ) (A : Matrix (Fin k) (Fin (d - k)) K) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i j => if h : i.val < k ∧ k ≤ j.val then
    A ⟨i.val, h.1⟩ ⟨j.val - k, by have := j.isLt; omega⟩ else 0

theorem blockEmbed_of_not {k : ℕ} {A : Matrix (Fin k) (Fin (d - k)) K} {i j : Fin d}
    (h : ¬ (i.val < k ∧ k ≤ j.val)) : blockEmbed k A i j = 0 := by
  simp [blockEmbed, h]

theorem blockEmbed_zero (k : ℕ) : blockEmbed (d := d) k (0 : Matrix (Fin k) (Fin (d - k)) K) = 0 := by
  ext i j
  simp only [blockEmbed, Matrix.of_apply, Matrix.zero_apply]
  split_ifs <;> simp

theorem blockEmbed_add (k : ℕ) (A B : Matrix (Fin k) (Fin (d - k)) K) :
    blockEmbed k (A + B) = blockEmbed k A + blockEmbed k B := by
  ext i j
  simp only [blockEmbed, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem blockEmbed_mul (k : ℕ) (A B : Matrix (Fin k) (Fin (d - k)) K) :
    blockEmbed k A * blockEmbed k B = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases h1 : i.val < k ∧ k ≤ m.val
  · by_cases h2 : m.val < k ∧ k ≤ j.val
    · exact absurd h2.1 (not_lt.2 h1.2)
    · rw [blockEmbed_of_not h2, mul_zero]
  · rw [blockEmbed_of_not h1, zero_mul]

theorem blockEmbed_injective {k : ℕ} (hk : k ≤ d) :
    Function.Injective (fun A : Matrix (Fin k) (Fin (d - k)) K => blockEmbed k A) := by
  intro A B h
  ext a b
  have := congrFun (congrFun h ⟨a.val, by omega⟩) ⟨b.val + k, by omega⟩
  simpa [blockEmbed] using this

theorem det_one_add_blockEmbed {k : ℕ} (A : Matrix (Fin k) (Fin (d - k)) K) :
    (1 + blockEmbed k A).det = 1 := by
  have hT : (1 + blockEmbed k A).BlockTriangular id := by
    intro i j hji
    have hji' : j.val < i.val := hji
    have hne : i ≠ j := fun h => by subst h; omega
    rw [Matrix.add_apply, Matrix.one_apply_ne hne,
      blockEmbed_of_not (by intro h; have := h.1; have := h.2; omega), zero_add]
  rw [Matrix.det_of_isUpperTriangular hT]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Matrix.add_apply, Matrix.one_apply_eq, blockEmbed_of_not (by intro h; have := h.1; have := h.2; omega),
    add_zero]

theorem one_add_blockEmbed_mul_one_sub {k : ℕ} (A : Matrix (Fin k) (Fin (d - k)) K) :
    (1 + blockEmbed k A) * (1 - blockEmbed k A) = 1 ∧ (1 - blockEmbed k A) * (1 + blockEmbed k A) = 1 := by
  have hE := blockEmbed_mul k A A
  constructor <;> simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hE] <;> abel

@[expose] def unipUnit {k : ℕ} (A : Matrix (Fin k) (Fin (d - k)) K) : Matrix.GeneralLinearGroup (Fin d) K :=
  Units.mk (1 + blockEmbed k A) (1 - blockEmbed k A) (one_add_blockEmbed_mul_one_sub A).1
    (one_add_blockEmbed_mul_one_sub A).2

theorem unipUnit_val {k : ℕ} (A : Matrix (Fin k) (Fin (d - k)) K) :
    ((unipUnit A : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + blockEmbed k A :=
  rfl

@[expose] def unipHom (k : ℕ) : Multiplicative (Matrix (Fin k) (Fin (d - k)) K) →* Matrix.GeneralLinearGroup (Fin d) K where
  toFun x := unipUnit (Multiplicative.toAdd x)
  map_one' := by
    apply Units.ext
    simp only [unipUnit_val, toAdd_one, blockEmbed_zero, add_zero, Units.val_one]
  map_mul' x y := by
    apply Units.ext
    simp only [unipUnit_val, toAdd_mul, blockEmbed_add, Units.val_mul]
    have hxy := blockEmbed_mul k (Multiplicative.toAdd x) (Multiplicative.toAdd y)
    have hyx := blockEmbed_mul k (Multiplicative.toAdd y) (Multiplicative.toAdd x)
    simp only [add_mul, mul_add, one_mul, mul_one, hxy, hyx, add_zero, zero_add]
    abel

end Unipotent

section Quotient

variable {K : Type} [Field K]

theorem mem_LargeEvenSLGroup_iff {d : ℕ} (g : Matrix.GeneralLinearGroup (Fin d) K) :
    g ∈ LargeEvenSLGroup (Fin d) K ↔ (g : Matrix (Fin d) (Fin d) K).det = 1 := by
  unfold LargeEvenSLGroup
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg (fun u : Kˣ => (u : K)) h
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  · intro h
    ext
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h

theorem unipUnit_det {d k : ℕ} (A : Matrix (Fin k) (Fin (d - k)) K) :
    ((unipUnit A : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
  rw [unipUnit_val, det_one_add_blockEmbed]

@[expose] def unipSL {d k : ℕ} :
    Multiplicative (Matrix (Fin k) (Fin (d - k)) K) →* LargeEvenSLGroup (Fin d) K where
  toFun x := ⟨unipHom (K := K) (d := d) k x, (mem_LargeEvenSLGroup_iff _).2 (unipUnit_det _)⟩
  map_one' := Subtype.ext (unipHom (K := K) (d := d) k).map_one
  map_mul' x y := Subtype.ext ((unipHom (K := K) (d := d) k).map_mul x y)

@[expose] def unipProj {d k : ℕ} :
    Multiplicative (Matrix (Fin k) (Fin (d - k)) K) →* LargeEvenProj (LargeEvenSLGroup (Fin d) K) :=
  (QuotientGroup.mk' ((LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K))).comp unipSL

theorem card_matrix_block (k d : ℕ) :
    Nat.card (Matrix (Fin k) (Fin (d - k)) K) = Nat.card K ^ (k * (d - k)) := by
  show Nat.card (Fin k → Fin (d - k) → K) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]

theorem unipProj_injective {d k : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ d) :
    Function.Injective (unipProj (K := K) (d := d) (k := k)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  unfold unipProj at hx
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 hx
  have hk0 : (0 : ℕ) < d := by omega
  have h00 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin d) K =>
    (g : Matrix (Fin d) (Fin d) K) ⟨0, hk0⟩ ⟨0, hk0⟩) hc
  have hE : blockEmbed k (Multiplicative.toAdd x) ⟨0, hk0⟩ ⟨0, hk0⟩ = 0 :=
    blockEmbed_of_not (by intro h; have := h.2; omega)
  simp only [unipSL, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk, unipHom, unipUnit_val,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.add_apply,
    Matrix.one_apply_eq, hE, add_zero] at h00
  have hc1 : c = 1 := Units.ext h00
  subst hc1
  have hM := congrArg (fun g : Matrix.GeneralLinearGroup (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hc
  simp only [unipSL, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk, unipHom, unipUnit_val,
    Units.val_one, map_one, Matrix.GeneralLinearGroup.coe_one] at hM
  have hB : blockEmbed k (Multiplicative.toAdd x) = blockEmbed k 0 := by
    rw [blockEmbed_zero]
    simpa using hM.symm
  have hx0 := blockEmbed_injective hkd hB
  simpa using hx0

end Quotient

theorem two_eq_zero_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : (2 : K) = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hc, m, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have hdvd : p ∣ 2 ^ n := by
    rw [hcard]
    exact dvd_pow_self p m.ne_zero
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  simpa using CharP.cast_eq_zero K 2

theorem sq_div_four_eq (d : ℕ) : d ^ 2 / 4 = d / 2 * (d - d / 2) := by
  rcases Nat.even_or_odd' d with ⟨m, rfl | rfl⟩
  · have h1 : (2 * m) ^ 2 = 4 * (m * m) := by ring
    have h2 : (2 * m) / 2 = m := by omega
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)]
    congr 1
    omega
  · have h1 : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1, h2, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt (by norm_num)]
    have h3 : 2 * m + 1 - m = m + 1 := by omega
    rw [h3]
    ring

section Pieces

variable {K : Type} [Field K] [Finite K]

@[expose] def unipE {d k : ℕ} : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
  (unipProj (K := K) (d := d) (k := k)).range

theorem unipE_card {d k : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ d) :
    Nat.card (unipE (K := K) (d := d) (k := k)) = Nat.card K ^ (k * (d - k)) := by
  rw [← card_matrix_block k d]
  have e1 : Nat.card (unipE (K := K) (d := d) (k := k)) =
      Nat.card (Multiplicative (Matrix (Fin k) (Fin (d - k)) K)) :=
    Nat.card_congr (MonoidHom.ofInjective (f := unipProj (K := K) (d := d) (k := k))
      (unipProj_injective hk1 hkd)).toEquiv.symm
  rw [e1]
  exact Nat.card_congr Multiplicative.toAdd

theorem unipE_isElemAbelian {d k : ℕ} (h2 : (2 : K) = 0) :
    IsElemAbelian 2 (unipE (K := K) (d := d) (k := k)) := by
  have hA : ∀ A : Matrix (Fin k) (Fin (d - k)) K, A + A = 0 := fun A => by
    ext i j
    simp [← two_mul, h2]
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
    have hsq : a ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul, hA]
    rw [← ha, ← map_pow, hsq, map_one]

theorem pRank_unipProj_ge {d k n : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ d) (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    n * (k * (d - k)) ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hn hK
  have hcard : Nat.card (unipE (K := K) (d := d) (k := k)) = 2 ^ (n * (k * (d - k))) := by
    rw [unipE_card hk1 hkd, hK, ← pow_mul]
  apply le_csSup
  · refine ⟨Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin d) K)), ?_⟩
    rintro m ⟨E, -, -, hE⟩
    have h1 : Nat.card E ≤ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      Subgroup.card_le_card_group E
    rw [hE] at h1
    have h3 : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  · exact ⟨unipE, le_top, unipE_isElemAbelian (d := d) (k := k) h2, hcard⟩

end Pieces

section Marking

theorem twoRankLow_tagA_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hA : lab.tag = .A)
    (hS : IsSimpleGroup S) (hrk : Rk2IsLabel S lab) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  obtain ⟨tag, rank, n⟩ := lab
  subst hA
  have hraw := rk2IsLabel_rawDatum hrk
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  haveI := hS
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_quotient_nonab θ hna
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  let e : S ≃* LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ
  have hp := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e
  rw [hp]
  have hform : twoRankLow107 ⟨.A, rank, n⟩ = n * ((rank + 1) / 2 * (rank + 1 - (rank + 1) / 2)) := by
    simp only [twoRankLow107]
    rw [sq_div_four_eq]
  rw [hform]
  rcases Nat.eq_zero_or_pos ((rank + 1) / 2) with h0 | h0
  · rw [h0]
    simp
  · exact pRank_unipProj_ge h0 (by omega) hn hK

end Marking

end CFSG.LocalAnalysis.GLTheoremA.I107G

end
