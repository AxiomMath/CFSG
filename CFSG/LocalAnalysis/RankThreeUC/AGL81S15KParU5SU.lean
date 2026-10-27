module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KParU5Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSU

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.KParU5Proof

open Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.LieType.CurtisTits

section Center

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem exists_scalar_eq_mat_of_mem_center_f (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    ∃ u : F, mat (unitaryInvolution F 2 f) n z = Matrix.scalar (Fin n) u := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  set ψ : SU (unitaryInvolution F 2 f) n ≃* StatedSU n (2 ^ f) F :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hF n)) with hψ
  have h1 : ψ z ∈ Subgroup.center ↥(StatedSU n (2 ^ f) F) := by
    rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv ψ]
    exact ⟨z, hz, rfl⟩
  rw [(isQuasisimple_statedSU_of_card hF hn hnq).2, Subgroup.mem_subgroupOf] at h1
  obtain ⟨u, hu⟩ := h1
  have hcoe : ((ψ z : StatedSU n (2 ^ f) F) : GL (Fin n) F) = P * (z : GL (Fin n) F) * P⁻¹ := rfl
  have hz' : (z : GL (Fin n) F) = P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) u * P := by
    rw [hu, hcoe]
    group
  refine ⟨(u : F), ?_⟩
  rw [mat_apply, hz', Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    ← (Matrix.scalar_commute (u : F) (fun r => mul_comm _ r) _).eq, Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

include hF in
theorem center_inf_rankOne_last_eq_bot_f (hn5 : 5 ≤ n) (hn : ¬Even n) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    (hzL : z ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n)
      k) :
    z = 1 := by
  obtain ⟨u, hu⟩ :=
    exists_scalar_eq_mat_of_mem_center_f hF (by omega) (fun h => by simp at h; omega) hz
  have hblk := isBlkOn_lastIdxOdd hn hk hzL
  set s₀ : Fin n := ⟨0, by omega⟩
  have hk1 : 1 ≤ k.val := by
    have := k.isLt
    obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hn
    omega
  have hs₀ : s₀ ∉ Set.range (lastIdxOdd k hn) := by
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    fin_cases i <;> simp [lastIdxOdd, s₀, val_lowIdx, midIdx, Fin.val_rev] at this <;> omega
  have h1 := hblk s₀ s₀ (Or.inl hs₀)
  rw [hu, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
  apply Subtype.ext
  apply Units.ext
  change mat (unitaryInvolution F 2 f) n z = mat (unitaryInvolution F 2 f) n 1
  rw [hu, map_one, h1, map_one]

end Center

section Diag

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] noncomputable def diagSU {n : ℕ} (d : Fin n → F) (hd0 : ∀ i, d i ≠ 0)
    (hdet : ∏ i, d i = 1) (hnorm : ∀ i, σ (d i) * d (Fin.rev i) = 1) : SU σ n :=
  ⟨⟨diagonal d, diagonal fun i => (d i)⁻¹,
    by
      rw [diagonal_mul_diagonal]
      have : (fun i => d i * (d i)⁻¹) = fun _ => (1 : F) := funext fun i => mul_inv_cancel₀ (hd0 i)
      rw [this, diagonal_one],
    by
      rw [diagonal_mul_diagonal]
      have : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : F) := funext fun i => inv_mul_cancel₀ (hd0 i)
      rw [this, diagonal_one]⟩,
    by
      change (diagonal d).det = 1
      rw [det_diagonal, hdet],
    by
      change conjTr σ (diagonal d) * antidiag n * diagonal d = antidiag n
      have hc : conjTr σ (diagonal d) = diagonal fun i => σ (d i) := by
        unfold conjTr
        rw [diagonal_map (map_zero σ), diagonal_transpose]
      rw [hc]
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [antidiag, Matrix.of_apply]
      split_ifs with h
      · subst h
        rw [mul_one]
        exact hnorm i
      · simp⟩

theorem exists_diag3 {t : F} (ht : t ≠ 0) (hσt : σ t = t⁻¹) :
    ∃ b : SU σ 3, mat σ 3 b = diagonal ![t, (t ^ 2)⁻¹, t] := by
  have hσt2 : σ ((t ^ 2)⁻¹) = t ^ 2 := by
    rw [map_inv₀, map_pow, hσt, inv_pow, inv_inv]
  refine ⟨diagSU ![t, (t ^ 2)⁻¹, t] (fun i => by fin_cases i <;> simp [ht])
    (by rw [Fin.prod_univ_three]; simp; field_simp) (fun i => ?_), rfl⟩
  fin_cases i
  · simp [hσt, ht]
  · simp [hσt2, ht]
  · simp [hσt, ht]

end Diag

section Pair

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

theorem mat_blk3Hom (k : Subfield F) {σ : F ≃+* F} (hk : ∀ c ∈ k, σ c = c)
    (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    mat σ 3 (blk3Hom k hk A) = blk3 k (A : Matrix (Fin 2) (Fin 2) k) := rfl

include hF in
theorem exists_pair_su3 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqd : q ∣ 2 ^ f + 1) :
    ∃ a b : SU (unitaryInvolution F 2 f) 3, a ^ q = 1 ∧ b ^ q = 1 ∧ a * b = b * a ∧
      ∀ s u : ℕ, a ^ s * b ^ u = 1 → q ∣ s ∧ q ∣ u := by
  haveI : Fact q.Prime := ⟨hq⟩
  set σ := unitaryInvolution F 2 f with hσdef
  have hqd0 := hqd
  obtain ⟨l, hl1, hlo⟩ := exists_norm_one_orderOf_eq hF
  obtain ⟨m, hm⟩ := hqd
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hlm : m ∣ orderOf l := ⟨q, by rw [hlo, hm, mul_comm]⟩
  set t' : Fˣ := l ^ m with ht'
  have hto : orderOf t' = q := by
    rw [ht', orderOf_pow_of_dvd hm0 hlm, hlo, hm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  set t : F := (t' : F) with htdef
  have ht0 : t ≠ 0 := t'.ne_zero
  have htq : t ^ q = 1 := by
    have := pow_orderOf_eq_one t'
    rw [hto] at this
    simpa [htdef] using congrArg (fun u : Fˣ => (u : F)) this
  have hσt1 : σ t * t = 1 := by
    rw [htdef, ht', Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hl1, one_pow]
  have hσt : σ t = t⁻¹ := eq_inv_of_mul_eq_one_left hσt1
  have htorder : ∀ j : ℕ, t ^ j = 1 → q ∣ j := fun j hj => by
    rw [← hto]
    exact orderOf_dvd_of_pow_eq_one (by
      apply Units.ext
      simpa [htdef] using hj)
  obtain ⟨b, hb⟩ := exists_diag3 (σ := σ) ht0 hσt
  have hf1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hcard : Nat.card (fixedSubfield F 2 f) = 2 ^ f := card_fixedSubfield hF
  obtain ⟨w, -, hw, hw1, -⟩ := exists_order_inverted_sl2 (F := fixedSubfield F 2 f) hq hq2 (by
    rw [hcard]
    exact hqd0.trans (CFSG.AGLEmbedding.ParabPrime.sub_one_dvd_and_add_one_dvd _ hf1).2)
  have hk' : ∀ c ∈ fixedSubfield F 2 f, σ c = c := fun c hc => mem_fixedSubfield.1 hc
  have hwo : orderOf w = q := orderOf_eq_prime hw hw1
  have hdq : (![t, (t ^ 2)⁻¹, t] : Fin 3 → F) ^ q = 1 := by
    funext i
    fin_cases i
    · simpa using htq
    · simp [inv_pow]
      rw [← pow_mul, mul_comm, pow_mul, htq, one_pow]
    · simpa using htq
  have hbq : b ^ q = 1 := by
    apply mat_injective
    rw [map_pow, hb, diagonal_pow, hdq, map_one]
    exact diagonal_one
  refine ⟨blk3Hom (fixedSubfield F 2 f) hk' w, b, ?_, hbq, ?_, ?_⟩
  · rw [← map_pow, hw, map_one]
  · apply mat_injective
    rw [map_mul, map_mul, hb, mat_blk3Hom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk3, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  · intro s u hsu
    have hmat := congrArg (mat σ 3) hsu
    rw [← map_pow (blk3Hom (fixedSubfield F 2 f) hk') w s, map_mul, map_pow (mat σ 3) b u, hb,
      mat_blk3Hom, diagonal_pow, map_one] at hmat
    have h11 := congrFun (congrFun hmat 1) 1
    simp [blk3, Matrix.mul_diagonal] at h11
    have h2u : q ∣ 2 * u := htorder _ (by rw [pow_mul]; exact h11)
    have hqu : q ∣ u := by
      rcases (Nat.Prime.dvd_mul hq).1 h2u with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h) hq2
      · exact h
    obtain ⟨c, rfl⟩ := hqu
    have hbu : b ^ (q * c) = 1 := by rw [pow_mul, hbq, one_pow]
    rw [hbu, mul_one] at hsu
    have hws : w ^ s = 1 := by
      apply blk3Hom_injective (fixedSubfield F 2 f) hk'
      rw [map_pow, hsu, map_one]
    have hsq : orderOf w ∣ s := orderOf_dvd_iff_pow_eq_one.2 hws
    rw [hwo] at hsq
    exact ⟨hsq, dvd_mul_right q c⟩

end Pair

@[expose] def lastNodeOdd (n : ℕ) (hn5 : 5 ≤ n) : Fin (n / 2) :=
  ⟨n / 2 - 1, Nat.sub_lt (Nat.div_pos (by omega) (by norm_num)) (by norm_num)⟩

theorem lastNodeOdd_last (n : ℕ) (hn5 : 5 ≤ n) :
    ¬ ((lastNodeOdd n hn5).val + 1 < n / 2) := by
  have h1 : 1 ≤ n / 2 := by
    have := Nat.div_pos (show 2 ≤ n by omega) (by norm_num : 0 < 2)
    omega
  change ¬ (n / 2 - 1 + 1 < n / 2)
  rw [Nat.sub_add_cancel h1]
  exact lt_irrefl _

section Transfer

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.QuasithinUnique

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem exists_pair_rankOne_odd {n : ℕ} (hn5 : 5 ≤ n) (hn : ¬ Even n) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqd : q ∣ 2 ^ f + 1) :
    ∃ a ∈ rankOne (rootDatum hF n).rootGroup (lastNodeOdd n hn5),
      ∃ b ∈ rankOne (rootDatum hF n).rootGroup (lastNodeOdd n hn5),
        a ^ q = 1 ∧ b ^ q = 1 ∧ a * b = b * a ∧
          ∀ s t : ℕ, a ^ s * b ^ t = 1 → q ∣ s ∧ q ∣ t := by
  obtain ⟨a₃, b₃, ha, hb, hab, hind⟩ := exists_pair_su3 hF hq hq2 hqd
  set e := rankOneLastOddEquiv hF hn (lastNodeOdd_last n hn5) with he
  refine ⟨(e.symm a₃ : SU (unitaryInvolution F 2 f) n), (e.symm a₃).2,
    (e.symm b₃ : SU (unitaryInvolution F 2 f) n), (e.symm b₃).2, ?_, ?_, ?_, ?_⟩
  · rw [← SubgroupClass.coe_pow, ← map_pow, ha, map_one]
    rfl
  · rw [← SubgroupClass.coe_pow, ← map_pow, hb, map_one]
    rfl
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
  · intro s t h
    have h1 : (e.symm a₃) ^ s * (e.symm b₃) ^ t = 1 := Subtype.ext (by simpa using h)
    have h2 := congrArg e h1
    rw [map_mul, map_pow, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      map_one] at h2
    exact hind s t h2

include hF in
theorem exists_minOver_su_odd {n : ℕ} (hn5 : 5 ≤ n) (hn : ¬ Even n) {W : Type} [Group W]
    [Finite W] {L S₀ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* StatedProj (StatedSU n (2 ^ f) F)) :
    ∃ P : Subgroup W, IsMinOverBorel L S₀ P ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ f + 1 →
        2 ≤ CFSG.Open.pRank q (pElementSubgroup 2 P) := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hB := borelQuotient_su hF (by omega) ζ hζ e
  exact exists_minOver_two_le_pRank hS hB (lastNodeOdd n hn5)
    (fun π' hπ' z hz h1 => center_inf_rankOne_last_eq_bot_f hF hn5 hn
      (lastNodeOdd_last n hn5) (hπ'.ker_central z (MonoidHom.mem_ker.2 h1)) hz)
    (fun q hq hq2 hqN => exists_pair_rankOne_odd (n := n) hF hn5 hn hq hq2 hqN)

end Transfer

end CFSG.LocalAnalysis.RankThreeUC.S15.KParU5Proof
