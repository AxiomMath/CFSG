module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSUFour
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open Matrix CFSG.Open CFSG.HardMathSupport.Timmesfeld.FieldBonus
  CFSG.LocalAnalysis.ComponentInitial

theorem two_le_pRank_statedSU_of_su2_block {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    {q : ℕ} (hq : q ≠ 0) {r : ℕ} [Fact r.Prime] {g : GL (Fin 2) K}
    (hgS : IsSU2 q (g : Matrix (Fin 2) (Fin 2) K)) (hgr : g ^ r = 1)
    (hns : ∀ c : Kˣ, (g : Matrix (Fin 2) (Fin 2) K) ≠ Matrix.scalar (Fin 2) (c : K)) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSU n q K))) := by
  have hS : ∀ j k : Fin 2, IsSU2 q
      (((Pi.mulSingle j g : Fin 2 → GL (Fin 2) K) k : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
    intro j k
    rw [pi_mulSingle_apply_su2]
    split_ifs
    · exact hgS
    · rw [Units.val_one]; exact isSU2_one _ hq
  set A := blkHom n hn (Pi.mulSingle 0 g) with hA
  set B := blkHom n hn (Pi.mulSingle 1 g) with hB
  have hAS : A ∈ StatedSU n q K := blkHom_mem_statedSU n hn hq _ (hS 0)
  have hBS : B ∈ StatedSU n q K := blkHom_mem_statedSU n hn hq _ (hS 1)
  have hpow : ∀ j : Fin 2, (Pi.mulSingle j g : Fin 2 → GL (Fin 2) K) ^ r = 1 := by
    intro j
    rw [← Pi.mulSingle_pow, hgr, Pi.mulSingle_one]
  have hAr : A ^ r = 1 := by
    rw [hA, ← map_pow, hpow, map_one]
  have hBr : B ^ r = 1 := by
    rw [hB, ← map_pow, hpow, map_one]
  have hcP : (Pi.mulSingle (0 : Fin 2) g : Fin 2 → GL (Fin 2) K) *
      (Pi.mulSingle (1 : Fin 2) g : Fin 2 → GL (Fin 2) K) =
      (Pi.mulSingle (1 : Fin 2) g : Fin 2 → GL (Fin 2) K) *
      (Pi.mulSingle (0 : Fin 2) g : Fin 2 → GL (Fin 2) K) := by
    funext k
    fin_cases k <;> simp [Pi.mul_apply]
  have hcomm : A * B = B * A := by
    rw [hA, hB, ← map_mul, ← map_mul, hcP]
  have hxA : A ∉ StatedScalars (Fin n) K := by
    rintro ⟨c, hc⟩
    have h1 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
    simp only [GeneralLinearGroup.coe_scalar, hA, coe_blkHom] at h1
    have h2 := blkMat_eq_scalar n hn _ (c : K) h1.symm 0
    exact hns c (by simpa [pi_mulSingle_apply_su2] using h2)
  have hyB : ∀ (m : ℕ), ∀ c ∈ StatedScalars (Fin n) K, A ^ m * c ≠ B := by
    rintro m _ ⟨c, rfl⟩ hmc
    have hAm : A ^ m = blkHom n hn (Pi.mulSingle 0 (g ^ m)) := by
      rw [hA, ← map_pow, ← Pi.mulSingle_pow]
    have h1 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hmc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hAm, hB, coe_blkHom] at h1
    apply hns c
    ext a' b'
    have h2 := congrFun (congrFun h1 (idx n hn a' 1)) (idx n hn b' 1)
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, blkMat_idx, blkMat_idx] at h2
    simp only [pi_mulSingle_apply_su2] at h2
    simp at h2
    rw [← h2]
    by_cases hab' : a' = b'
    · subst hab'; simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, Matrix.one_apply, hab']
  exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_statedProj
    (H := StatedSU n q K) (p := r) hAS hBS hAr hBr ⟨1, one_mem _, by
      rw [one_mul]; exact hcomm⟩ hxA hyB

theorem exists_su2_prime_order_char_two {K : Type} [Field K] {f : ℕ}
    (h : UnitaryFieldData 2 f K) {r : ℕ} (hr : r.Prime) (hrq : r ∣ (2 ^ f) ^ 2 - 1) :
    ∃ g : GL (Fin 2) K, IsSU2 (2 ^ f) (g : Matrix (Fin 2) (Fin 2) K) ∧ g ^ r = 1 ∧
      ∀ c : Kˣ, (g : Matrix (Fin 2) (Fin 2) K) ≠ Matrix.scalar (Fin 2) (c : K) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Finite K := h.finite
  have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 2) (by norm_num)
  rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.prod_Icc_two_two,
    show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at hint
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_two_pow)
  have hcard : Nat.card (StatedSU 2 (2 ^ f) K) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    apply Nat.cast_injective (R := ℤ)
    rw [hint]
    push_cast [Nat.cast_sub h1]
    ring
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := StatedSU 2 (2 ^ f) K) r
    (by rw [hcard]; exact Dvd.dvd.mul_left hrq _)
  have hgr : g ^ r = 1 := hg ▸ pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    exact hr.one_lt.ne hg
  obtain ⟨hdet, hu⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 g.2
  have hgS : IsSU2 (2 ^ f) ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    refine ⟨?_, hdet⟩
    have e : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f) =
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar := by
      ext i j
      simp [h.bar_apply]
    rw [e]
    exact hu
  have hns : ∀ c : Kˣ, ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠
      Matrix.scalar (Fin 2) (c : K) := by
    intro c hc
    have hc2 : (c : K) ^ 2 = 1 := by
      have := congrArg Matrix.det hc
      rw [hdet] at this
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using this.symm
    have h20 : (2 : K) = 0 := by
      haveI := h.charP
      exact CharTwo.two_eq_zero
    have hc1 : (c : K) = 1 := by
      have h3 : ((c : K) - 1) ^ 2 = 0 := by linear_combination hc2 + (1 - (c : K)) * h20
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)
    apply hg1
    apply Subtype.ext
    apply Units.ext
    rw [hc, hc1, map_one]
    rfl
  exact ⟨(g : GL (Fin 2) K), hgS, by rw [← Subgroup.coe_pow, hgr]; rfl, hns⟩

theorem two_le_pRank_psu_of_dvd {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 4 ≤ n)
    (hC : StatedClassicalModel X .PSU n 2 f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ (2 ^ f) ^ 2 - 1) : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  have h : UnitaryFieldData 2 f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hgS, hgr, hns⟩ := exists_su2_prime_order_char_two h hr hrq
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact two_le_pRank_statedSU_of_su2_block hn (pow_ne_zero f two_ne_zero) hgS hgr hns

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
