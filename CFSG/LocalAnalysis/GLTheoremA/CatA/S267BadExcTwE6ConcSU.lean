module

public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear CFSG.LieType.Universal.Unitary

section Blocks

variable {K : Type} [Field K] {n : ℕ}

theorem compIndicator_eq_reindex (J : Finset (Fin n)) :
    compIndicator K J =
      reindexAlgEquiv K K (Equiv.sumCompl (· ∈ J)) (fromBlocks 0 0 0 1) := by
  ext i j
  rw [compIndicator_apply, coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · rw [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_pos hj,
      fromBlocks_apply₁₁]
    simp [hi]
  · rw [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₁₂]
    simp [hi]
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_pos hj,
      fromBlocks_apply₂₁]
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [hij]
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₂₂, one_apply]
    by_cases hij : i = j
    · subst hij
      simp [hi]
    · have hne : (⟨i, hi⟩ : {x // x ∉ J}) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
      simp [hij, hne]

theorem compIndicator_compl (J : Finset (Fin n)) :
    compIndicator K Jᶜ = 1 - compIndicator K J := by
  ext i j
  rw [Matrix.sub_apply, compIndicator_apply, compIndicator_apply, one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ J <;> simp [hi]
  · simp [hij]

theorem fromBlocks_sub_fromBlocks {l m o r : Type*} (A A' : Matrix l m K) (B B' : Matrix l o K)
    (C C' : Matrix r m K) (D D' : Matrix r o K) :
    fromBlocks A B C D - fromBlocks A' B' C' D' = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext (i | i) (j | j) <;> simp

theorem blockOn_sub_one_mul_sub (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) K)
    {t : K} (hX : X * X - t • X + 1 = 0) :
    (blockOn K J X - 1) * (blockOn K J X - (t - 1) • 1) = (t - 2) • (1 - compIndicator K J) := by
  set R := reindexAlgEquiv K K (Equiv.sumCompl (· ∈ J)) with hR
  set X' := reindexAlgEquiv K K J.equivFin.symm X with hX'def
  have hX' : X' * X' - t • X' + 1 = 0 := by
    have h := congrArg (reindexAlgEquiv K K J.equivFin.symm) hX
    rwa [map_add, map_sub, map_mul, map_smul, map_one, map_zero] at h
  have hH : blockOn K J X = R (fromBlocks X' 0 0 1) := rfl
  have h1 : (1 : Matrix (Fin n) (Fin n) K) = R (fromBlocks 1 0 0 1) := by
    rw [fromBlocks_one, map_one]
  have hblk : (X' - 1) * (X' - (t - 1) • 1) = (t - 2) • (1 : Matrix _ _ K) := by
    have e : (X' - 1) * (X' - (t - 1) • 1) = (X' * X' - t • X' + 1) + (t - 2) • 1 := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, mul_smul_comm]
      module
    rw [e, hX', zero_add]
  have hL : (blockOn K J X - 1) * (blockOn K J X - (t - 1) • 1) =
      R ((fromBlocks X' 0 0 1 - fromBlocks 1 0 0 1) *
        (fromBlocks X' 0 0 1 - (t - 1) • fromBlocks 1 0 0 1)) := by
    rw [map_mul, map_sub, map_sub, map_smul, ← hH, ← h1]
  have hRt : (t - 2) • (1 - compIndicator K J) =
      R ((t - 2) • (fromBlocks 1 0 0 1 - fromBlocks 0 0 0 1)) := by
    rw [map_smul, map_sub, ← h1, ← compIndicator_eq_reindex]
  rw [hL, hRt]
  congr 1
  rw [fromBlocks_smul (t - 1), fromBlocks_sub_fromBlocks, fromBlocks_sub_fromBlocks,
    fromBlocks_multiply, fromBlocks_sub_fromBlocks, fromBlocks_smul]
  simp only [smul_zero, sub_self, sub_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  rw [hblk]

theorem commute_compIndicator_of_commute {J : Finset (Fin n)}
    {X : Matrix (Fin J.card) (Fin J.card) K} {t : K} (hX : X * X - t • X + 1 = 0) (ht : t ≠ 2)
    {Y : Matrix (Fin n) (Fin n) K} (hY : Commute Y (blockOn K J X)) :
    Commute Y (compIndicator K J) := by
  have h1 : Commute Y ((blockOn K J X - 1) * (blockOn K J X - (t - 1) • 1)) :=
    (hY.sub_right (Commute.one_right Y)).mul_right
      (hY.sub_right ((Commute.one_right Y).smul_right (t - 1)))
  rw [blockOn_sub_one_mul_sub J X hX] at h1
  have ht2 : t - 2 ≠ 0 := sub_ne_zero.2 ht
  have h2 : Commute Y (1 - compIndicator K J) := by
    have h3 := h1.smul_right (t - 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ ht2, one_smul] at h3
  have h4 := (Commute.one_right Y).sub_right h2
  rwa [sub_sub_cancel] at h4

end Blocks

section TwoByTwo

variable {K : Type} [Field K]

theorem sq_sub_trace_smul_add_one {X : Matrix (Fin 2) (Fin 2) K} (hX : X.det = 1) :
    X * X - X.trace • X + 1 = 0 := by
  rw [det_fin_two] at hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, one_apply] <;>
    first | linear_combination hX | linear_combination (-1 : K) * hX | linear_combination (0 : K) * hX

theorem one_add_pow_of_sq_eq_zero {m : ℕ} {N : Matrix (Fin m) (Fin m) K} (hN : N * N = 0)
    (k : ℕ) : (1 + N) ^ k = 1 + (k : K) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hN, smul_zero,
      add_zero, Nat.cast_succ, add_smul, one_smul]
    abel

theorem eq_one_of_trace_eq_two {X : Matrix (Fin 2) (Fin 2) K} (hX : X.det = 1) {p : ℕ}
    (hp : (p : K) ≠ 0) (hXp : X ^ p = 1) (ht : X.trace = 2) : X = 1 := by
  have hCH := sq_sub_trace_smul_add_one hX
  rw [ht] at hCH
  set N := X - 1 with hNdef
  have hN : N * N = 0 := by
    have e : N * N = X * X - (2 : K) • X + 1 := by
      rw [hNdef, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul]
      module
    rw [e, hCH]
  have hXN : X = 1 + N := by rw [hNdef]; abel
  rw [hXN, one_add_pow_of_sq_eq_zero hN, add_eq_left] at hXp
  have hN0 : N = 0 := by
    have h := congrArg (fun Y => (p : K)⁻¹ • Y) hXp
    simpa [smul_smul, inv_mul_cancel₀ hp] using h
  rw [hXN, hN0, add_zero]

end TwoByTwo

section Scalars

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {n : ℕ}

theorem eq_one_of_pow_eq_one_of_coprime {p : ℕ} (hpn : Nat.Coprime p n) {l : K}
    (hlp : l ^ p = 1) (hln : l ^ n = 1) : l = 1 := by
  have h : l ^ Nat.gcd p n = 1 := pow_gcd_eq_one.mpr ⟨hlp, hln⟩
  rwa [hpn.gcd_eq_one, pow_one] at h

theorem pow_eq_one_of_coe_eq_smul {g : Su K ℓ f n} {l : K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • (1 : Matrix (Fin n) (Fin n) K)) :
    l ^ n = 1 := by
  have h := g.2.1
  rwa [hg, det_smul, det_one, mul_one, Fintype.card_fin] at h

theorem pow_card_add_one_eq_one {g h : Su K ℓ f n} (hn0 : n ≠ 0) {l : K}
    (hl : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      l • ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    l ^ (ℓ ^ f + 1) = 1 := by
  have hg := g.2.2
  have hh := h.2.2
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K ℓ f
  set H : Matrix (Fin n) (Fin n) K := ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have e : conjTr σ (l • H) * (l • H) = (σ l * l) • (conjTr σ H * H) := by
    rw [conjTr, Matrix.map_smul' _ _ _ (map_mul σ), transpose_smul, smul_mul_smul_comm]
    rfl
  rw [hl, e, hh] at hg
  have h00 := congrFun (congrFun hg ⟨0, Nat.pos_of_ne_zero hn0⟩) ⟨0, Nat.pos_of_ne_zero hn0⟩
  simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h00
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ] at h00
  exact h00

theorem eq_one_of_smul_one {p : ℕ} (hpn : Nat.Coprime p (Nat.gcd n (ℓ ^ f + 1)))
    {g : Su K ℓ f n} (hgp : g ^ p = 1) {l : K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • (1 : Matrix (Fin n) (Fin n) K)) :
    g = 1 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    apply Subtype.ext
    apply Units.ext
    exact Subsingleton.elim _ _
  have hn : l ^ n = 1 := pow_eq_one_of_coe_eq_smul hg
  have hQ : l ^ (ℓ ^ f + 1) = 1 :=
    pow_card_add_one_eq_one (h := 1) hn0.ne' (by rw [hg]; rfl)
  have hp : l ^ p = 1 := by
    have h := congrArg (fun x : Su K ℓ f n => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hgp
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hg, smul_pow, one_pow,
      OneMemClass.coe_one, Units.val_one] at h
    have hi := congrFun (congrFun h ⟨0, hn0⟩) ⟨0, hn0⟩
    simpa using hi
  have hl : l = 1 := eq_one_of_pow_eq_one_of_coprime hpn hp
    ((pow_gcd_eq_one).mpr ⟨hn, hQ⟩)
  apply Subtype.ext
  apply Units.ext
  rw [hg, hl, one_smul]
  rfl

theorem eq_one_of_conj_eq_smul {p : ℕ} (hn0 : n ≠ 0)
    (hpn : Nat.Coprime p (Nat.gcd n (ℓ ^ f + 1))) {g h : Su K ℓ f n}
    (hhp : h ^ p = 1) {l : K}
    (hl : (((g * h * g⁻¹ : Su K ℓ f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      l • (((h : Su K ℓ f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    l = 1 := by
  have hn : l ^ n = 1 := by
    have h1 := (g * h * g⁻¹).2.1
    have h2 := h.2.1
    rw [hl, det_smul, Fintype.card_fin, h2, mul_one] at h1
    exact h1
  have hQ : l ^ (ℓ ^ f + 1) = 1 := pow_card_add_one_eq_one hn0 hl
  have hp : l ^ p = 1 := by
    have h1 : (g * h * g⁻¹) ^ p = 1 := by rw [conj_pow, hhp, mul_one, mul_inv_cancel]
    have h2 := congrArg (fun x : Su K ℓ f n => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h1
    have h3 := congrArg (fun x : Su K ℓ f n => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hhp
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at h2 h3
    rw [hl, smul_pow, h3] at h2
    have hi := congrFun (congrFun h2 ⟨0, Nat.pos_of_ne_zero hn0⟩) ⟨0, Nat.pos_of_ne_zero hn0⟩
    simpa using hi
  exact eq_one_of_pow_eq_one_of_coprime hpn hp ((pow_gcd_eq_one).mpr ⟨hn, hQ⟩)

end Scalars

section CoordBlocks

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {n : ℕ}

theorem compIndicator_mul_self (J : Finset (Fin n)) :
    compIndicator K J * compIndicator K J = compIndicator K J := by
  ext i j
  rw [compIndicator_mul_apply]
  by_cases hi : i ∈ J
  · rw [if_pos hi, compIndicator_apply]
    simp [hi]
  · rw [if_neg hi]

theorem commute_of_idempotent {R : Type*} [Ring R] {c g h : R} (hc : c * c = c)
    (hcg : c * g = c) (hgc : g * c = c) (heh : (1 - c) * h = 1 - c) (hhe : h * (1 - c) = 1 - c) :
    g * h = h * g := by
  have hce : c * (1 - c) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
  have hec : (1 - c) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
  have hee : (1 - c) * (1 - c) = 1 - c := by rw [sub_mul, one_mul, hce, sub_zero]
  set g₀ := g - c with hg₀
  set h₀ := h - (1 - c) with hh₀
  have hcg₀ : c * g₀ = 0 := by rw [hg₀, mul_sub, hcg, hc, sub_self]
  have hg₀c : g₀ * c = 0 := by rw [hg₀, sub_mul, hgc, hc, sub_self]
  have heh₀ : (1 - c) * h₀ = 0 := by rw [hh₀, mul_sub, heh, hee, sub_self]
  have hh₀e : h₀ * (1 - c) = 0 := by rw [hh₀, sub_mul, hhe, hee, sub_self]
  have hch₀ : c * h₀ = h₀ := by
    have h1 : (1 - c) * h₀ = h₀ - c * h₀ := by rw [sub_mul, one_mul]
    rw [heh₀] at h1
    exact (sub_eq_zero.1 h1.symm).symm
  have hh₀c : h₀ * c = h₀ := by
    have h1 : h₀ * (1 - c) = h₀ - h₀ * c := by rw [mul_sub, mul_one]
    rw [hh₀e] at h1
    exact (sub_eq_zero.1 h1.symm).symm
  have heg₀ : (1 - c) * g₀ = g₀ := by rw [sub_mul, one_mul, hcg₀, sub_zero]
  have hg₀e : g₀ * (1 - c) = g₀ := by rw [mul_sub, mul_one, hg₀c, sub_zero]
  have hgh₀ : g₀ * h₀ = 0 := by rw [← hch₀, ← mul_assoc, hg₀c, zero_mul]
  have hhg₀ : h₀ * g₀ = 0 := by rw [← heg₀, ← mul_assoc, hh₀e, zero_mul]
  have hg : g = c + g₀ := by rw [hg₀, add_sub_cancel]
  have hh : h = (1 - c) + h₀ := by rw [hh₀, add_sub_cancel]
  rw [hg, hh, add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, hce, hch₀, hg₀e, hgh₀, hec,
    heg₀, hh₀c, hhg₀]
  abel

theorem commute_of_mem_coordBlockSU {J : Finset (Fin n)} {g h : Su K ℓ f n}
    (hg : g ∈ coordBlockSU K ℓ f J) (hh : h ∈ coordBlockSU K ℓ f Jᶜ) : g * h = h * g := by
  rw [mem_coordBlockSU_iff_indicator] at hg hh
  rw [compIndicator_compl] at hh
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  apply Subtype.ext
  apply Units.ext
  exact commute_of_idempotent (compIndicator_mul_self J) hg1 hg2 hh1 hh2

theorem coordBlockSU_mono {J J' : Finset (Fin n)} (hJ : J ⊆ J') :
    coordBlockSU K ℓ f J ≤ coordBlockSU K ℓ f J' := by
  intro g hg
  rw [mem_coordBlockSU_iff] at hg ⊢
  intro i j hij
  exact hg i j (hij.imp (fun h hi => h (hJ hi)) (fun h hj => h (hJ hj)))

theorem coordBlockSU_inf_compl (J : Finset (Fin n)) :
    coordBlockSU K ℓ f J ⊓ coordBlockSU K ℓ f Jᶜ = ⊥ := by
  rw [eq_bot_iff]
  intro g hgJ
  obtain ⟨hg, hg'⟩ := Subgroup.mem_inf.1 hgJ
  rw [mem_coordBlockSU_iff] at hg hg'
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [OneMemClass.coe_one, Units.val_one, one_apply]
  by_cases hi : i ∈ J
  · exact hg' i j (Or.inl (by simpa using hi))
  · exact hg i j (Or.inl hi)

end CoordBlocks

section Layer

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

abbrev blk01 : Finset (Fin 6) := {0, 1}

theorem coordBlockSU_compl_le_centralizer {h : Su K ℓ f 6} (hh : h ∈ coordBlockSU K ℓ f blk01) :
    coordBlockSU K ℓ f blk01ᶜ ≤ Subgroup.centralizer {h} := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_coordBlockSU hh hx).symm

theorem conj_mem_coordBlockSU_of_commute {p : ℕ} (hp : (p : K) ≠ 0) {h : Su K ℓ f 6}
    (hh : h ∈ coordBlockSU K ℓ f blk01) (hhp : h ^ p = 1) (hh1 : h ≠ 1) {y : Su K ℓ f 6}
    (hy : y * h = h * y) {g : Su K ℓ f 6} (hg : g ∈ coordBlockSU K ℓ f blk01ᶜ) :
    y * g * y⁻¹ ∈ coordBlockSU K ℓ f blk01ᶜ := by
  obtain ⟨M, rfl⟩ := hh
  have hMp : M ^ p = 1 := blockSUOn_injective (K := K) (p := ℓ) (f := f) blk01
    (by rw [map_pow, hhp, map_one])
  have hM1 : M ≠ 1 := fun h1 => hh1 (by rw [h1, map_one])
  set X : Matrix (Fin blk01.card) (Fin blk01.card) K :=
    ((M : GL (Fin blk01.card) K) : Matrix (Fin blk01.card) (Fin blk01.card) K) with hXdef
  have hXp0 : X ^ p = 1 := by
    have h1 := congrArg (fun z : Su K ℓ f blk01.card =>
      ((z : GL (Fin blk01.card) K) : Matrix (Fin blk01.card) (Fin blk01.card) K)) hMp
    simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] using h1
  have hX10 : X ≠ 1 := fun h1 => hM1 (Subtype.ext (Units.ext h1))
  set e := reindexAlgEquiv K K (finCongr (show blk01.card = 2 from rfl)) with he
  set X₂ : Matrix (Fin 2) (Fin 2) K := e X with hX₂
  have hdet : X₂.det = 1 := by
    rw [hX₂, he, coe_reindexAlgEquiv, det_reindex_self]
    exact M.2.1
  have hXp : X₂ ^ p = 1 := by rw [hX₂, ← map_pow, hXp0, map_one]
  have hX1 : X₂ ≠ 1 := fun h1 => hX10 (e.injective (h1.trans (map_one e).symm))
  have ht : X₂.trace ≠ 2 := fun ht => hX1 (eq_one_of_trace_eq_two hdet hp hXp ht)
  have hCH : X * X - X₂.trace • X + 1 = 0 := by
    apply e.injective
    rw [map_add, map_sub, map_mul, map_smul, map_one, map_zero]
    exact sq_sub_trace_smul_add_one hdet
  have hcomm : Commute ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) (blockOn K blk01 X) := by
    have h1 := congrArg (fun z : Su K ℓ f 6 => ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hy
    simp only [Subgroup.coe_mul, Units.val_mul, coe_coe_blockSUOn] at h1
    exact h1
  have hC := commute_compIndicator_of_commute hCH ht hcomm
  refine conj_mem_coordBlockSU ?_ hg
  rw [compIndicator_compl]
  exact ((Commute.one_right _).sub_right hC).eq.symm

theorem card_coordBlockSU (J : Finset (Fin 6)) :
    Nat.card (coordBlockSU K ℓ f J) = Nat.card (Su K ℓ f J.card) :=
  Nat.card_congr (MonoidHom.ofInjective (blockSUOn_injective (K := K) (p := ℓ) (f := f) J)).toEquiv.symm

theorem dvd_card_coordBlockSU_compl {p : ℕ} (hp2 : p ∣ Nat.card (Su K ℓ f 2)) :
    p ∣ Nat.card (coordBlockSU K ℓ f blk01ᶜ) := by
  have h1 : Nat.card (coordBlockSU K ℓ f ({2, 3} : Finset (Fin 6))) = Nat.card (Su K ℓ f 2) := by
    rw [card_coordBlockSU]
    rfl
  exact (h1 ▸ hp2).trans (Subgroup.card_dvd_of_le (coordBlockSU_mono (by decide)))

end Layer

section ElemAbelian

variable {p : ℕ} [Fact p.Prime]

@[expose] def powHom {G : Type*} [Group G] (M : G) (hM : orderOf M = p) :
    Multiplicative (ZMod p) →* G where
  toFun x := M ^ (Multiplicative.toAdd x).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    have key : ∀ n : ℕ, M ^ (n % p) = M ^ n := fun n => by rw [← hM]; exact pow_mod_orderOf M n
    change M ^ (Multiplicative.toAdd x + Multiplicative.toAdd y).val =
      M ^ (Multiplicative.toAdd x).val * M ^ (Multiplicative.toAdd y).val
    rw [ZMod.val_add, key, pow_add]

theorem powHom_apply {G : Type*} [Group G] (M : G) (hM : orderOf M = p) (x : Multiplicative (ZMod p)) :
    powHom M hM x = M ^ (Multiplicative.toAdd x).val := rfl

theorem powHom_injective {G : Type*} [Group G] {M : G} (hM : orderOf M = p) :
    Function.Injective (powHom M hM) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [powHom_apply] at hx
  have h := orderOf_dvd_of_pow_eq_one hx
  rw [hM] at h
  have hlt := ZMod.val_lt (Multiplicative.toAdd x)
  have h0 : (Multiplicative.toAdd x).val = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
  rw [ZMod.val_eq_zero] at h0
  exact h0

theorem isElemAbelian_range_of_injective {G : Type*} [Group G] {m : ℕ}
    {φ : (Fin m → Multiplicative (ZMod p)) →* G} (hφ : Function.Injective φ) :
    CFSG.Open.IsElemAbelian p φ.range ∧ Nat.card φ.range = p ^ m := by
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    change (x : G) * y = y * x
    rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := by
      funext i
      rw [Pi.pow_apply, Pi.one_apply]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, Nat.card_fun,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin m),
      Fintype.card_fin]

end ElemAbelian

section SUTwo

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem dvd_card_su_two (hK : Nat.card K = (ℓ ^ f) ^ 2) {p : ℕ} (hp : p ∣ (ℓ ^ f) ^ 2 - 1) :
    p ∣ Nat.card (Su K ℓ f 2) := by
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  have e := (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans (conjEquiv P hP)
  rw [← Nat.card_congr e.toEquiv, CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two,
    CFSG.LieType.Steinberg.card_fixedSubfield hK]
  exact Dvd.dvd.mul_left hp _

end SUTwo

section DGroups

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {p : ℕ}
  [Fact p.Prime]

@[expose] noncomputable def suCongr {a b : ℕ} (h : a = b) : Su K ℓ f a ≃* Su K ℓ f b := by
  subst h
  exact MulEquiv.refl _

@[expose] noncomputable def pairBlock (J : Finset (Fin 6)) (hJ : J.card = 2) :
    Su K ℓ f 2 →* Su K ℓ f 6 :=
  (blockSUOn K ℓ f J).comp (suCongr hJ.symm).toMonoidHom

theorem pairBlock_injective (J : Finset (Fin 6)) (hJ : J.card = 2) :
    Function.Injective (pairBlock (K := K) (ℓ := ℓ) (f := f) J hJ) :=
  (blockSUOn_injective J).comp (suCongr hJ.symm).injective

theorem pairBlock_mem (J : Finset (Fin 6)) (hJ : J.card = 2) (X : Su K ℓ f 2) :
    pairBlock J hJ X ∈ coordBlockSU K ℓ f J :=
  ⟨_, rfl⟩

abbrev blk23 : Finset (Fin 6) := {2, 3}

abbrev blk45 : Finset (Fin 6) := {4, 5}

theorem card_blk01 : blk01.card = 2 := rfl

theorem card_blk23 : blk23.card = 2 := rfl

theorem card_blk45 : blk45.card = 2 := rfl

theorem mul_three_eq {G : Type*} [Group G] {a₀ a₁ a₂ b₀ b₁ b₂ : G} (h01 : b₀ * a₁ = a₁ * b₀)
    (h02 : b₀ * a₂ = a₂ * b₀) (h12 : b₁ * a₂ = a₂ * b₁) :
    a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) = a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) := by
  calc a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) = a₀ * (b₀ * a₁) * (b₁ * a₂) * b₂ := by group
    _ = a₀ * (a₁ * b₀) * (a₂ * b₁) * b₂ := by rw [h01, h12]
    _ = a₀ * a₁ * (b₀ * a₂) * b₁ * b₂ := by group
    _ = a₀ * a₁ * (a₂ * b₀) * b₁ * b₂ := by rw [h02]
    _ = a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) := by group

@[expose] noncomputable def blockTripleHom (M : Su K ℓ f 2) (hM : orderOf M = p) :
    (Fin 3 → Multiplicative (ZMod p)) →* Su K ℓ f 6 where
  toFun x := pairBlock blk01 card_blk01 (powHom M hM (x 0)) * pairBlock blk23 card_blk23 (powHom M hM (x 1)) *
    pairBlock blk45 card_blk45 (powHom M hM (x 2))
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, map_mul]
    refine mul_three_eq ?_ ?_ ?_
    · exact commute_of_mem_coordBlockSU (pairBlock_mem _ _ _)
        (coordBlockSU_mono (J := blk23) (by decide) (pairBlock_mem _ _ _))
    · exact commute_of_mem_coordBlockSU (pairBlock_mem _ _ _)
        (coordBlockSU_mono (J := blk45) (by decide) (pairBlock_mem _ _ _))
    · exact commute_of_mem_coordBlockSU (pairBlock_mem _ _ _)
        (coordBlockSU_mono (J := blk45) (by decide) (pairBlock_mem _ _ _))

theorem blockTripleHom_apply (M : Su K ℓ f 2) (hM : orderOf M = p)
    (x : Fin 3 → Multiplicative (ZMod p)) :
    blockTripleHom M hM x = pairBlock blk01 card_blk01 (powHom M hM (x 0)) *
      pairBlock blk23 card_blk23 (powHom M hM (x 1)) * pairBlock blk45 card_blk45 (powHom M hM (x 2)) :=
  rfl

theorem eq_one_of_mem_coordBlockSU {J J' : Finset (Fin 6)} (hJ' : J' ⊆ Jᶜ) {g : Su K ℓ f 6}
    (hg : g ∈ coordBlockSU K ℓ f J) (hg' : g ∈ coordBlockSU K ℓ f J') : g = 1 := by
  have h := coordBlockSU_inf_compl (K := K) (ℓ := ℓ) (f := f) J
  have hmem : g ∈ coordBlockSU K ℓ f J ⊓ coordBlockSU K ℓ f Jᶜ :=
    Subgroup.mem_inf.2 ⟨hg, coordBlockSU_mono hJ' hg'⟩
  rw [h] at hmem
  exact (Subgroup.mem_bot.1 hmem)

theorem blockTripleHom_injective (M : Su K ℓ f 2) (hM : orderOf M = p) :
    Function.Injective (blockTripleHom M hM) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [blockTripleHom_apply] at hx
  set u₀ := pairBlock (K := K) (ℓ := ℓ) (f := f) blk01 card_blk01 (powHom M hM (x 0))
  set u₁ := pairBlock (K := K) (ℓ := ℓ) (f := f) blk23 card_blk23 (powHom M hM (x 1))
  set u₂ := pairBlock (K := K) (ℓ := ℓ) (f := f) blk45 card_blk45 (powHom M hM (x 2))
  have hu₁₂ : u₁ * u₂ ∈ coordBlockSU K ℓ f blk01ᶜ :=
    mul_mem (coordBlockSU_mono (J := blk23) (by decide) (pairBlock_mem _ _ _))
      (coordBlockSU_mono (J := blk45) (by decide) (pairBlock_mem _ _ _))
  have h0 : u₀ = 1 := by
    have e : u₀ = (u₁ * u₂)⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← mul_assoc]; exact hx
    exact eq_one_of_mem_coordBlockSU (J' := blk01ᶜ) (subset_of_eq rfl) (pairBlock_mem _ _ _)
      (e ▸ inv_mem hu₁₂)
  rw [h0, one_mul] at hx
  have h1 : u₁ = 1 := by
    have e : u₁ = u₂⁻¹ := eq_inv_of_mul_eq_one_left hx
    exact eq_one_of_mem_coordBlockSU (J' := blk45) (by decide) (pairBlock_mem _ _ _)
      (e ▸ inv_mem (pairBlock_mem _ _ _))
  rw [h1, one_mul] at hx
  have hx0 : x 0 = 1 := by
    apply powHom_injective hM
    apply pairBlock_injective (K := K) (ℓ := ℓ) (f := f) blk01 card_blk01
    rw [map_one, map_one]
    exact h0
  have hx1 : x 1 = 1 := by
    apply powHom_injective hM
    apply pairBlock_injective (K := K) (ℓ := ℓ) (f := f) blk23 card_blk23
    rw [map_one, map_one]
    exact h1
  have hx2 : x 2 = 1 := by
    apply powHom_injective hM
    apply pairBlock_injective (K := K) (ℓ := ℓ) (f := f) blk45 card_blk45
    rw [map_one, map_one]
    exact hx
  funext i
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hx2

theorem blockTripleHom_single_mem (M : Su K ℓ f 2) (hM : orderOf M = p) :
    blockTripleHom M hM (Pi.mulSingle 0 (Multiplicative.ofAdd 1)) ∈ coordBlockSU K ℓ f blk01 := by
  rw [blockTripleHom_apply]
  have h1 : (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p)) : Fin 3 → _) 1 = 1 := rfl
  have h2 : (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p)) : Fin 3 → _) 2 = 1 := rfl
  rw [h1, h2, map_one (powHom M hM), map_one (pairBlock blk23 card_blk23),
    map_one (pairBlock blk45 card_blk45), mul_one, mul_one]
  exact pairBlock_mem _ _ _

variable (K) in
@[expose] noncomputable def diagGL (n : ℕ) : (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

theorem coe_diagGL {n : ℕ} (a : Fin n → Kˣ) :
    ((diagGL K n a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => (a i : K) :=
  rfl

theorem diagGL_mem_SUid {n : ℕ} {a : Fin n → Kˣ}
    (hσ : ∀ i, CFSG.LieType.BorelTits.unitaryInvolution K ℓ f (a i) * a i = 1)
    (hdet : ∏ i, a i = 1) :
    diagGL K n a ∈ SUid (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f) n := by
  refine ⟨?_, ?_⟩
  · rw [coe_diagGL, det_diagonal]
    have := congrArg (fun u : Kˣ => (u : K)) hdet
    simpa [Units.coe_prod] using this
  · rw [coe_diagGL, conjTr, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal]
    ext i j
    rw [diagonal_apply, one_apply]
    split_ifs with h
    · exact hσ i
    · rfl

variable (c : Kˣ) (hc : orderOf c = p)

@[expose] noncomputable def diagTuple (x : Fin 5 → Multiplicative (ZMod p)) : Fin 6 → Kˣ :=
  fun i => if h : (i : ℕ) < 5 then powHom c hc (x ⟨i, h⟩) else (∏ j, powHom c hc (x j))⁻¹

theorem diagTuple_castSucc (x : Fin 5 → Multiplicative (ZMod p)) (j : Fin 5) :
    diagTuple c hc x j.castSucc = powHom c hc (x j) := by
  simp [diagTuple, j.is_lt]

theorem diagTuple_last (x : Fin 5 → Multiplicative (ZMod p)) :
    diagTuple c hc x (Fin.last 5) = (∏ j, powHom c hc (x j))⁻¹ := by
  simp [diagTuple]

theorem prod_diagTuple (x : Fin 5 → Multiplicative (ZMod p)) : ∏ i, diagTuple c hc x i = 1 := by
  rw [Fin.prod_univ_castSucc, diagTuple_last]
  simp only [diagTuple_castSucc]
  exact mul_inv_cancel _

@[expose] noncomputable def diagTupleHom : (Fin 5 → Multiplicative (ZMod p)) →* (Fin 6 → Kˣ) where
  toFun := diagTuple c hc
  map_one' := by
    funext i
    simp only [diagTuple, Pi.one_apply, map_one, Finset.prod_const_one, inv_one, dite_eq_ite,
      ite_self]
  map_mul' x y := by
    funext i
    simp only [diagTuple, Pi.mul_apply, map_mul]
    split_ifs
    · rfl
    · rw [Finset.prod_mul_distrib, mul_inv]

theorem diagTuple_pow_eq_one (x : Fin 5 → Multiplicative (ZMod p)) (i : Fin 6) :
    diagTuple c hc x i ^ p = 1 := by
  have hx : x ^ p = 1 := by
    funext j
    rw [Pi.pow_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have h := congrFun (congrArg (diagTupleHom c hc) hx) i
  rwa [map_pow, map_one, Pi.pow_apply, Pi.one_apply] at h

@[expose] noncomputable def diagSUHom (hpQ : p ∣ ℓ ^ f + 1) :
    (Fin 5 → Multiplicative (ZMod p)) →* Su K ℓ f 6 :=
  ((diagGL K 6).comp (diagTupleHom c hc)).codRestrict _ fun x => by
    refine diagGL_mem_SUid (fun i => ?_) (prod_diagTuple c hc x)
    obtain ⟨k, hk⟩ := hpQ
    have h1 : (diagTuple c hc x i : K) ^ (ℓ ^ f + 1) = 1 := by
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, diagTuple_pow_eq_one, Units.val_one, one_pow]
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
    exact h1

theorem coe_diagSUHom (hpQ : p ∣ ℓ ^ f + 1) (x : Fin 5 → Multiplicative (ZMod p)) :
    (((diagSUHom c hc hpQ x : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal fun i => (diagTuple c hc x i : K) :=
  rfl

theorem diagSUHom_injective (hpQ : p ∣ ℓ ^ f + 1) : Function.Injective (diagSUHom c hc hpQ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  funext j
  have h := congrArg (fun g : Su K ℓ f 6 => ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) j.castSucc
    j.castSucc) hx
  simp only [coe_diagSUHom, diagonal_apply_eq, OneMemClass.coe_one, Units.val_one, one_apply_eq,
    diagTuple_castSucc] at h
  exact powHom_injective hc (Units.ext (h.trans (by rw [Pi.one_apply, map_one, Units.val_one])))

@[expose] def diagGen : Fin 5 → Multiplicative (ZMod p) :=
  (Pi.mulSingle (0 : Fin 5) (Multiplicative.ofAdd (1 : ZMod p)) : Fin 5 → Multiplicative (ZMod p)) *
    Pi.mulSingle (1 : Fin 5) (Multiplicative.ofAdd (-1 : ZMod p))

theorem diagGen_ne_one : (diagGen : Fin 5 → Multiplicative (ZMod p)) ≠ 1 := by
  intro h
  have h0 := congrFun h 0
  simp only [diagGen, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.one_apply] at h0
  rw [Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 5) ≠ 1), mul_one] at h0
  exact one_ne_zero (Multiplicative.ofAdd.injective h0)

theorem diagSUHom_diagGen_mem (hpQ : p ∣ ℓ ^ f + 1) :
    diagSUHom c hc hpQ diagGen ∈ coordBlockSU K ℓ f blk01 := by
  have hprod : ∏ j, (diagGen : Fin 5 → Multiplicative (ZMod p)) j = 1 := by
    simp only [diagGen, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle',
      if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ofAdd_neg]
    exact mul_inv_cancel _
  have hlast : diagTuple c hc diagGen (Fin.last 5) = 1 := by
    rw [diagTuple_last, ← map_prod, hprod, map_one, inv_one]
  have hmid : ∀ j : Fin 5, j ≠ 0 → j ≠ 1 → diagTuple c hc diagGen j.castSucc = 1 := by
    intro j hj0 hj1
    rw [diagTuple_castSucc, diagGen, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj0,
      Pi.mulSingle_eq_of_ne hj1, mul_one, map_one]
  rw [mem_coordBlockSU_iff]
  intro i j hij
  rw [coe_diagSUHom, diagonal_apply]
  split_ifs with h
  · subst h
    have hi : i ∉ blk01 := hij.elim id id
    have hval : diagTuple c hc diagGen i = 1 := by
      fin_cases i
      · exact absurd (by decide) hi
      · exact absurd (by decide) hi
      · exact hmid 2 (by decide) (by decide)
      · exact hmid 3 (by decide) (by decide)
      · exact hmid 4 (by decide) (by decide)
      · exact hlast
    rw [hval, Units.val_one]
  · rfl

end DGroups

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc

end
