module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDLevi
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamLinear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Matrix

section Valuation

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValNat_prod_finset {s : Finset ℕ} {f : ℕ → ℕ} (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem padicValNat_card_GL_eq_sum {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hpK : ¬ p ∣ Nat.card K) :
    padicValNat p (Nat.card (GL (Fin n) K)) =
      ∑ j ∈ Finset.Ioc 0 n, padicValNat p (Nat.card K ^ j - 1) := by
  haveI := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hcard : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  set q := Nat.card K with hq
  rw [Matrix.card_GL_field, hcard, Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n]
  have hne0 : ∀ i ∈ Finset.range n, q ^ n - q ^ i ≠ 0 := fun i hi =>
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hq1 (Finset.mem_range.1 hi))
  have hterm : ∀ i ∈ Finset.range n,
      padicValNat p (q ^ n - q ^ i) = padicValNat p (q ^ (n - i) - 1) := by
    intro i hi
    have hin : i ≤ n := (Finset.mem_range.1 hi).le
    have hlt : 0 < q ^ (n - i) - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow
      (by have := Finset.mem_range.1 hi; omega) hq1)
    have hsplit : q ^ n - q ^ i = q ^ i * (q ^ (n - i) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hin]
    have h0 : padicValNat p (q ^ i) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h => hpK (hp.out.dvd_of_dvd_pow h))
    rw [hsplit, padicValNat.mul (pow_ne_zero _ (by omega)) hlt.ne', h0, zero_add]
  rw [padicValNat_prod_finset hne0, Finset.sum_congr rfl hterm]
  exact sum_range_sub_eq_sum_Ioc (fun j => padicValNat p (q ^ j - 1)) n

theorem not_dvd_pow_add_one_of_odd {q e : ℕ} (hp5 : 5 ≤ p) (heo : Odd e)
    (hpe : ∀ j : ℕ, p ∣ q ^ j - 1 ↔ e ∣ j) (j : ℕ) (hq : 1 ≤ q) : ¬ p ∣ q ^ j + 1 := by
  intro h
  have hqj : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq
  have h1 : p ∣ q ^ (2 * j) - 1 := by
    have : q ^ (2 * j) - 1 = (q ^ j + 1) * (q ^ j - 1) := by
      rw [mul_comm, pow_mul]
      have := Nat.sq_sub_sq (q ^ j) 1
      simpa using this
    rw [this]
    exact Dvd.dvd.mul_right h _
  have h2 : e ∣ 2 * j := (hpe _).1 h1
  have hcop : Nat.Coprime e 2 := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_)
    intro h2dvd
    exact (Nat.not_even_iff_odd.2 heo) (even_iff_two_dvd.2 h2dvd)
  have h3 : e ∣ j := hcop.dvd_of_dvd_mul_left h2
  have h4 : p ∣ q ^ j - 1 := (hpe j).2 h3
  have h5 : p ∣ 2 := by
    have : (q ^ j + 1) - (q ^ j - 1) = 2 := by omega
    rw [← this]
    exact Nat.dvd_sub h h4
  have := Nat.le_of_dvd two_pos h5
  omega

end Valuation

section Levi

variable (r : ℕ) (K : Type) [Field K]

@[expose] noncomputable def leviUnit (g : GL (Fin r) K) : GL (Fin r ⊕ Fin r) K where
  val := fromBlocks (g : Matrix (Fin r) (Fin r) K) 0 0
    (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ)
  inv := fromBlocks ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0 0
    ((g : Matrix (Fin r) (Fin r) K)ᵀ)
  val_inv := by
    simp only [fromBlocks_multiply, ← transpose_mul, Units.inv_mul, Units.mul_inv, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, transpose_one, fromBlocks_one]
  inv_val := by
    simp only [fromBlocks_multiply, ← transpose_mul, Units.inv_mul, Units.mul_inv, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, transpose_one, fromBlocks_one]

@[expose] noncomputable def leviGL : GL (Fin r) K →* GL (Fin r ⊕ Fin r) K :=
  MonoidHom.mk' (leviUnit r K) fun g h => Units.ext (by
    simp only [leviUnit, Units.val_mul, fromBlocks_multiply, _root_.mul_inv_rev, transpose_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add])

theorem leviGL_mem_statedSp (g : GL (Fin r) K) : leviGL r K g ∈ StatedSp r K := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  have h1 : ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      (g : Matrix (Fin r) (Fin r) K) = 1 := Units.inv_mul g
  have h2 : (g : Matrix (Fin r) (Fin r) K) *
      ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = 1 := Units.mul_inv g
  have h3 : ((g : Matrix (Fin r) (Fin r) K))ᵀ *
      (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))ᵀ = 1 := by
    rw [← transpose_mul, h1, transpose_one]
  simp only [leviGL, MonoidHom.mk'_apply, leviUnit, fromBlocks_transpose, transpose_zero,
    transpose_transpose, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add, neg_mul, mul_neg, h1, h3, Matrix.mul_neg, Matrix.neg_mul]
  simp

@[expose] noncomputable def leviSp : GL (Fin r) K →* StatedSp r K :=
  (leviGL r K).codRestrict (StatedSp r K) (leviGL_mem_statedSp r K)

theorem leviSp_injective : Function.Injective (leviSp r K) := by
  intro a b h
  have h1 : leviGL r K a = leviGL r K b := congrArg Subtype.val h
  have h2 := congrArg
    (fun u : GL (Fin r ⊕ Fin r) K => (u : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h1
  simp only [leviGL, MonoidHom.mk'_apply, leviUnit] at h2
  exact Units.ext (fromBlocks_inj.1 h2).1

end Levi

section Order

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem padicValNat_card_statedSp_eq (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (heo : Odd e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (r : ℕ) :
    padicValNat p (Nat.card (StatedSp r K)) = padicValNat p (Nat.card (GL (Fin r) K)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp r,
    padicValNat_card_GL_eq_sum hpK]
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have h0 : padicValNat p (Nat.card K ^ (r ^ 2)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hpK (hp.out.dvd_of_dvd_pow h))
  have hne : ∀ j ∈ Finset.Icc 1 r, Nat.card K ^ (2 * j) - 1 ≠ 0 := fun j hj =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by have := (Finset.mem_Icc.1 hj).1; omega) hq1)
  rw [padicValNat.mul (pow_ne_zero _ (by omega)) (Finset.prod_ne_zero_iff.2 hne), h0, zero_add,
    padicValNat_prod_finset hne]
  have hIcc : Finset.Icc 1 r = Finset.Ioc 0 r := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Ioc.1 hj).1
  have hqj : 1 ≤ Nat.card K ^ j := Nat.one_le_pow _ _ (by omega)
  have hfac : Nat.card K ^ (2 * j) - 1 = (Nat.card K ^ j + 1) * (Nat.card K ^ j - 1) := by
    rw [mul_comm, pow_mul]
    have := Nat.sq_sub_sq (Nat.card K ^ j) 1
    simpa using this
  have hlt : 0 < Nat.card K ^ j - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hq1)
  rw [hfac, padicValNat.mul (by omega) hlt.ne',
    padicValNat.eq_zero_of_not_dvd (not_dvd_pow_add_one_of_odd hp5 heo hpe j (by omega)),
    zero_add]

theorem not_dvd_card_scalars_sp (hp3 : 3 ≤ p) {r : ℕ} (hr : 1 ≤ r) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) := by
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨c, hc⟩ : ((z : StatedSp r K) : GL (Fin r ⊕ Fin r) K) ∈ StatedScalars (Fin r ⊕ Fin r) K :=
    z.2
  have hmem : ((z : StatedSp r K) : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := (z : StatedSp r K).2
  rw [← hc, CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hr] at hmem
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((z : StatedSp r K) : GL (Fin r ⊕ Fin r) K) ^ 2 = 1
    rw [← hc, ← map_pow, hmem, map_one]
  have := Nat.le_of_dvd two_pos (hz ▸ orderOf_dvd_of_pow_eq_one hz2)
  omega

theorem le_pRank_GL_matrix {n e r' : ℕ} (hpK : ¬ p ∣ Nat.card K) (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (hr : r' * e ≤ n) :
    r' ≤ CFSG.Open.pRank p (⊤ : Subgroup (GL (Fin n) K)) := by
  let ψ : GL (Fin n) K ≃* (Module.End K (Fin n → K))ˣ := Matrix.GeneralLinearGroup.toLin
  have hfr : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have h1 := le_pRank_GL (V := Fin n → K) hpK he hpe (r := r') (by rw [hfr]; exact hr)
  exact h1.trans (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt ψ).symm.le

end Order

section Sp

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem crossAt_statedProj_sp_odd (hp5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) (hpK : ¬ p ∣ Nat.card K)
    {e : ℕ} (he : 0 < e) (heo : Odd e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) :
    (CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp r K))) = 2 →
      ∀ R : Sylow p (StatedProj (StatedSp r K)),
        IsMulCommutative (R : Subgroup (StatedProj (StatedSp r K)))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp r K))) →
      ∀ y : StatedProj (StatedSp r K), y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (StatedProj (StatedSp r K))))) := by
  have hp2 : Odd p := hp.out.odd_of_ne_two (by omega)
  have hidx : ¬ p ∣ (leviSp r K).range.index := by
    have hmul := Subgroup.card_mul_index (leviSp r K).range
    have hcardR : Nat.card (leviSp r K).range = Nat.card (GL (Fin r) K) :=
      (Nat.card_congr (MonoidHom.ofInjective (leviSp_injective r K)).toEquiv).symm
    have hv := padicValNat_card_statedSp_eq hp5 hpK heo hpe r
    have hI0 : (leviSp r K).range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 := congrArg (padicValNat p) hmul
    rw [padicValNat.mul Nat.card_pos.ne' hI0, hcardR] at h1
    intro hd
    have := (dvd_iff_padicValNat_ne_zero hI0).1 hd
    change padicValNat p (Nat.card (GL (Fin r) K)) +
      padicValNat p (leviSp r K).range.index = padicValNat p (Nat.card (StatedSp r K)) at h1
    omega
  refine crossAt_of_levi (d := r / e) hp5
    ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K))
    (not_dvd_card_scalars_sp (by omega) hr) (leviSp r K) (leviSp_injective r K) hidx
    (fun hne P hP => isMulCommutative_of_isPGroup_GL_matrix hp2 hpK he hpe hne hP) ?_ ?_
  · exact le_pRank_GL_matrix hpK he hpe (Nat.div_mul_le_self r e)
  · intro hpd y₀ hy₀
    have h3e : 3 * e ≤ r := by
      have := (Nat.le_div_iff_mul_le he).1 hpd
      nlinarith
    exact le_pRank_centralizer_GL_matrix hp5 hpK he hpe (by omega) h3e hy₀

end Sp

end CFSG.LocalAnalysis.RankFourTheoremC
