module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZLin3Aut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZLinData
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Trans
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinOuter
import CFSG.LieType.SeitzGeneration.OuterLinearDescent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin3

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3
open CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin (coe_diag3_pow glaPPrimeCore_le_center
  commute_of_mem_glaPPrimeCoreOf incl0 incl0_injective incl0_mem_coordBlockSL B0_le x12 x21
  x12_mem_coordBlockSL x21_mem_coordBlockSL prod_du prod_dr)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL coe_diagGL coe_diagGL_inv slConjugation_diagGL_apply
  slConjugation_diagGL_congr)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem blockDiag_of_mul_eq_smul {B : Matrix (Fin 3) (Fin 3) K} (hB : B.det ≠ 0) {d d' : Fin 3 → K}
    (hd : ∏ i, d i = 1) (hd' : ∏ i, d' i = 1) (h12 : d 1 = d 2) (h12' : d' 1 = d' 2)
    (h01 : d 0 ≠ d 1) {c : K} (hc : c ^ 3 = 1)
    (h : B * diagonal d' = c • (diagonal d * B)) :
    (∀ i, d' i = c * d i) ∧ B 0 1 = 0 ∧ B 0 2 = 0 ∧ B 1 0 = 0 ∧ B 2 0 = 0 := by
  have hent : ∀ k l, B k l * d' l = c * (d k * B k l) := by
    intro k l
    have := congrFun (congrFun h k) l
    simpa [mul_diagonal, diagonal_mul, Matrix.smul_apply] using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  have hd0 := ne_zero_of_prod_eq_one hd
  have h1 : d' 1 = c * d 1 := by
    by_contra hne
    have hz : ∀ k l, k ≠ 0 → l ≠ 0 → B k l = 0 := by
      intro k l hk hl
      have hdk : d k = d 1 := by fin_cases k <;> simp_all
      have hdl : d' l = d' 1 := by fin_cases l <;> simp_all
      have := hent k l
      rw [hdk, hdl] at this
      have h2 : B k l * (d' 1 - c * d 1) = 0 := by linear_combination this
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.1 h3) hne
    apply hB
    rw [Matrix.det_fin_three, hz 1 1 (by decide) (by decide), hz 1 2 (by decide) (by decide),
      hz 2 1 (by decide) (by decide), hz 2 2 (by decide) (by decide)]
    ring
  have h0 : d' 0 = c * d 0 := by
    have hp : d 0 * d 1 * d 2 = 1 := by simpa [Fin.prod_univ_three] using hd
    have hp' : d' 0 * d' 1 * d' 2 = 1 := by simpa [Fin.prod_univ_three] using hd'
    rw [← h12', h1] at hp'
    rw [← h12] at hp
    have hd1 := hd0 1
    have key : (d' 0 - c * d 0) * (c ^ 2 * (d 1 * d 1)) = 0 := by
      linear_combination hp' - c ^ 3 * hp - hc
    have hcd : c ^ 2 * (d 1 * d 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc0) (mul_ne_zero hd1 hd1)
    rcases mul_eq_zero.1 key with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hcd
  have hall : ∀ i, d' i = c * d i := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · show d' 2 = c * d 2
      rw [← h12', h1, h12]
  refine ⟨hall, ?_⟩
  have hcomm : ∀ k l, d k ≠ d l → B k l = 0 := by
    intro k l hkl
    have := hent k l
    rw [hall l] at this
    have h2 : c * (B k l * (d l - d k)) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hc0
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h4
      · exact absurd (sub_eq_zero.1 h4).symm hkl
  exact ⟨hcomm 0 1 h01, hcomm 0 2 (h12 ▸ h01), hcomm 1 0 (Ne.symm h01),
    hcomm 2 0 (h12 ▸ Ne.symm h01)⟩

theorem diag_of_blockDiag {B : Matrix (Fin 3) (Fin 3) K} (hB : B.det ≠ 0) (h01 : B 0 1 = 0)
    (h02 : B 0 2 = 0) (h10 : B 1 0 = 0) (h20 : B 2 0 = 0) {y : Fin 3 → K} (hy0 : y 0 ≠ 0)
    (hy12 : y 1 ≠ y 2) {c : K} (h : B * diagonal y = c • (diagonal y * B)) :
    c = 1 ∧ B 1 2 = 0 ∧ B 2 1 = 0 := by
  have hent : ∀ k l, B k l * y l = c * (y k * B k l) := by
    intro k l
    have := congrFun (congrFun h k) l
    simpa [mul_diagonal, diagonal_mul, Matrix.smul_apply] using this
  have hB00 : B 0 0 ≠ 0 := by
    intro h0
    apply hB
    rw [Matrix.det_fin_three, h0, h01, h02]
    ring
  have hc : c = 1 := by
    have := hent 0 0
    have h2 : B 0 0 * y 0 * (1 - c) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 (mul_ne_zero hB00 hy0)
    · linear_combination -h3
  subst hc
  refine ⟨rfl, ?_, ?_⟩
  · have := hent 1 2
    have h2 : B 1 2 * (y 2 - y 1) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.1 h3).symm hy12
  · have := hent 2 1
    have h2 : B 2 1 * (y 1 - y 2) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.1 h3) hy12

theorem mul_conj_mul_inv {G : Type*} [Group G] (γ : MulAut G) (d : G) :
    γ * MulAut.conj d * γ⁻¹ = MulAut.conj (γ d) := by
  ext g
  simp [MulAut.conj_apply]

theorem apply_mul_inv_mem_center {G : Type*} [Group G] {γ : MulAut G} {d : G}
    (h : γ * MulAut.conj d = MulAut.conj d * γ) : γ d * d⁻¹ ∈ Subgroup.center G := by
  have h1 : MulAut.conj (γ d) = MulAut.conj d := by
    rw [← mul_conj_mul_inv, h, mul_inv_cancel_right]
  have hz : ∀ g, d⁻¹ * γ d * g = g * (d⁻¹ * γ d) := by
    intro g
    have h2 := congrArg (fun φ : MulAut G => φ g) h1
    simp only [MulAut.conj_apply] at h2
    calc d⁻¹ * γ d * g = d⁻¹ * (γ d * g * (γ d)⁻¹) * γ d := by group
      _ = d⁻¹ * (d * g * d⁻¹) * γ d := by rw [h2]
      _ = g * (d⁻¹ * γ d) := by group
  have hzc : d⁻¹ * γ d ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => (hz g).symm
  have h3 : γ d * d⁻¹ = d⁻¹ * γ d := by
    have h4 := (Subgroup.mem_center_iff.1 hzc d).symm
    calc γ d * d⁻¹ = d * (d⁻¹ * γ d) * d⁻¹ := by group
      _ = d⁻¹ * γ d * d * d⁻¹ := by rw [h4]
      _ = d⁻¹ * γ d := by group
  rw [h3]
  exact hzc

variable [Finite K]

theorem rel_of_commute {A : GL (Fin 3) K} {τ : K ≃+* K} {d : SpecialLinearGroup (Fin 3) K}
    (h : slC A * slF τ * MulAut.conj d = MulAut.conj d * (slC A * slF τ)) :
    ∃ c : K, c ^ 3 = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) K) * (d : Matrix (Fin 3) (Fin 3) K).map τ =
        c • ((d : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) := by
  have hz := apply_mul_inv_mem_center h
  rw [← scalars_eq_center] at hz
  obtain ⟨c, hc3, hc⟩ := mem_scalars.1 hz
  refine ⟨c, by simpa using congrArg Units.val hc3, ?_⟩
  have hrel : (slC A * slF τ) d = ((slC A * slF τ) d * d⁻¹) * d := by group
  have hmat : (((slC A * slF τ) d : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((((slC A * slF τ) d * d⁻¹) * d : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← hrel]
  rw [Matrix.SpecialLinearGroup.coe_mul _ d, hc, slC_mul_slF_coe] at hmat
  have hA : (A⁻¹ : GL (Fin 3) K).val * A.val = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  calc (A : Matrix (Fin 3) (Fin 3) K) * (d : Matrix (Fin 3) (Fin 3) K).map τ
      = (A.val * (d : Matrix (Fin 3) (Fin 3) K).map τ * (A⁻¹).val) * A.val := by
        rw [Matrix.mul_assoc _ (A⁻¹).val, hA, Matrix.mul_one]
    _ = (scalar (Fin 3) (c : K) * (d : Matrix (Fin 3) (Fin 3) K)) * A.val := by rw [hmat]
    _ = (c : K) • ((d : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) := by
        rw [scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_mul]

theorem apply_eq_of_pow_three {τ : K ≃+* K} (hτ : τ ^ 3 = 1) {u : K} (hu : u ^ 3 = 1) : τ u = u := by
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
  have hprim : IsPrimitiveRoot u 3 := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨hu, fun l hl => ?_⟩
    have := orderOf_dvd_of_pow_eq_one hu
    have h3 : orderOf u = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hu1
      · exact h
    rw [← h3]
    exact orderOf_dvd_of_pow_eq_one hl
  have hτu : (τ u) ^ 3 = 1 := by rw [← map_pow, hu, map_one]
  obtain ⟨i, hi, hiu⟩ := hprim.eq_pow_of_pow_eq_one hτu
  have hτ3 : (τ ^ 3) u = u := by rw [hτ]; rfl
  interval_cases i
  ·
    exfalso
    rw [pow_zero] at hiu
    apply hu1
    have := congrArg τ.symm hiu
    simpa using this.symm
  · simpa using hiu.symm
  · exfalso
    have h2 : ∀ k : ℕ, (τ ^ k) u = u ^ (2 ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', RingAut.mul_apply, ih, map_pow, ← hiu, ← pow_mul, pow_succ, mul_comm]
    have h8 := h2 3
    rw [hτ3] at h8
    have hu8 : u ^ 8 = u ^ 2 := by
      calc u ^ 8 = (u ^ 3) ^ 2 * u ^ 2 := by ring
        _ = u ^ 2 := by rw [hu, one_pow, one_mul]
    norm_num at h8
    rw [hu8] at h8
    apply hu1
    have hu0 : u ≠ 0 := by
      rintro rfl
      norm_num at hu
    have : u * (u - 1) = 0 := by linear_combination -h8
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hu0
    · exact sub_eq_zero.1 h

theorem eq_diag3_of_isDiag {g : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ∃ hd : ∏ i, (g : Matrix (Fin 3) (Fin 3) K) i i = 1,
      g = diag3 (fun i => (g : Matrix (Fin 3) (Fin 3) K) i i) hd := by
  have hmat : (g : Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => (g : Matrix (Fin 3) (Fin 3) K) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, hg i j hij]
  have hd : ∏ i, (g : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe g
    rw [hmat, det_diagonal] at this
    exact this
  exact ⟨hd, Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [coe_diag3, ← hmat]⟩

theorem mul_apply_of_isDiag {g h : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin 3) (Fin 3) K) i j = 0) (i : Fin 3) :
    ((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i =
      (g : Matrix (Fin 3) (Fin 3) K) i i * (h : Matrix (Fin 3) (Fin 3) K) i i := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb
    rw [hg i b (Ne.symm hb), zero_mul]
  · simp

theorem pow_apply_of_isDiag {g : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin 3) (Fin 3) K) i j = 0) (n : ℕ) :
    (∀ i j, i ≠ j → ((g ^ n : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧
      ∀ i, ((g ^ n : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i =
        (g : Matrix (Fin 3) (Fin 3) K) i i ^ n := by
  obtain ⟨hd, hgd⟩ := eq_diag3_of_isDiag hg
  rw [hgd, coe_diag3_pow]
  refine ⟨fun i j hij => by rw [diagonal_apply_ne _ hij], fun i => ?_⟩
  rw [diagonal_apply_eq, Pi.pow_apply]
  simp [coe_diag3]

theorem exists_scalar_of_mem_center {z : SpecialLinearGroup (Fin 3) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    ∃ c : K, c ^ 3 = 1 ∧ (z : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c := by
  rw [← scalars_eq_center] at hz
  obtain ⟨c, hc3, hc⟩ := mem_scalars.1 hz
  exact ⟨c, by simpa using congrArg Units.val hc3, hc⟩

section AM

variable {AM : Subgroup (SpecialLinearGroup (Fin 3) K)}
  (hdiag : ∀ d ∈ AM, ∀ i j, i ≠ j → (d : Matrix (Fin 3) (Fin 3) K) i j = 0)
  (hcube : ∀ d ∈ AM, d ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K))
include hdiag

theorem entry_pow_three {d : SpecialLinearGroup (Fin 3) K} (hd : d ∈ AM) (hd3 : d ^ 3 = 1)
    (i : Fin 3) : (d : Matrix (Fin 3) (Fin 3) K) i i ^ 3 = 1 := by
  have h := (pow_apply_of_isDiag (hdiag d hd) 3).2 i
  rw [hd3, Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at h
  exact h.symm

theorem exists_pow_three_ne_one (h27 : Nat.card AM = 27) :
    ∃ x ∈ AM, x ^ 3 ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  have hne : ∀ d : AM, ∀ i : Fin 3, ((d : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    intro d i h0
    have := entry_pow_three hdiag d.2 (hall d d.2) i
    rw [h0, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  let F : AM → rootsOfUnity 3 K × rootsOfUnity 3 K := fun d =>
    (⟨Units.mk0 _ (hne d 0), by
        rw [mem_rootsOfUnity]; exact Units.ext (by simpa using entry_pow_three hdiag d.2 (hall d d.2) 0)⟩,
     ⟨Units.mk0 _ (hne d 1), by
        rw [mem_rootsOfUnity]; exact Units.ext (by simpa using entry_pow_three hdiag d.2 (hall d d.2) 1)⟩)
  have hF : Function.Injective F := by
    intro d d' h
    have h0 : ((d : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
        ((d' : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 := by
      have := congrArg (fun q => ((q.1 : Kˣ) : K)) h
      simpa [F] using this
    have h1 : ((d : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 =
        ((d' : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 := by
      have := congrArg (fun q => ((q.2 : Kˣ) : K)) h
      simpa [F] using this
    obtain ⟨hd, hdd⟩ := eq_diag3_of_isDiag (hdiag d d.2)
    obtain ⟨hd', hdd'⟩ := eq_diag3_of_isDiag (hdiag d' d'.2)
    have hp : ∀ g : AM, ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 *
        ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 *
        ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      intro g
      obtain ⟨hg, -⟩ := eq_diag3_of_isDiag (hdiag g g.2)
      simpa [Fin.prod_univ_three] using hg
    have h2 : ((d : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
        ((d' : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
      have e1 := hp d
      have e2 := hp d'
      rw [h0, h1] at e1
      have hm : ((d' : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 *
          ((d' : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 :=
        mul_ne_zero (hne d' 0) (hne d' 1)
      exact mul_left_cancel₀ hm (e1.trans e2.symm)
    apply Subtype.ext
    rw [hdd, hdd']
    congr 1
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hcard := Nat.card_le_card_of_injective F hF
  rw [h27, Nat.card_prod] at hcard
  have h3 := card_rootsOfUnity (R := K) 3
  have : Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) ≤ 3 * 3 := Nat.mul_le_mul h3 h3
  omega

omit hdiag in
theorem mem_zpowers_of_mem_center {x z : SpecialLinearGroup (Fin 3) K} {cx : K}
    (hcx : ((x ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) cx)
    (hcxp : IsPrimitiveRoot cx 3) (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    z ∈ Subgroup.zpowers x := by
  obtain ⟨c, hc3, hc⟩ := exists_scalar_of_mem_center hz
  obtain ⟨m, -, hm⟩ := hcxp.eq_pow_of_pow_eq_one hc3
  have : z = (x ^ 3) ^ m := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hcx, hc, ← hm, ← map_pow]
  rw [this, ← pow_mul]
  exact Subgroup.npow_mem_zpowers x _

include hcube in
theorem exists_y0_aprime (hcomm : IsMulCommutative AM) (h27 : Nat.card AM = 27) :
    ∃ (s : K) (hs : s ≠ 0), (s ^ 3) ^ 3 = 1 ∧ s ^ 3 ≠ 1 ∧
      diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs) ∈ AM ∧
      ∃ y₀ ∈ AM, (∀ i, (y₀ : Matrix (Fin 3) (Fin 3) K) i i ^ 3 = 1) ∧
        (y₀ : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ (y₀ : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  classical
  obtain ⟨x, hxAM, hx3⟩ := exists_pow_three_ne_one hdiag h27
  obtain ⟨cx, hcx3, hcx⟩ := exists_scalar_of_mem_center (hcube x hxAM)
  have hcx1 : cx ≠ 1 := by
    rintro rfl
    apply hx3
    apply Subtype.ext
    rw [hcx, Matrix.SpecialLinearGroup.coe_one, map_one]
  have hcxp : IsPrimitiveRoot cx 3 := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨hcx3, fun l hl => ?_⟩
    have h1 := orderOf_dvd_of_pow_eq_one hcx3
    have h3 : orderOf cx = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hcx1
      · exact h
    rw [← h3]
    exact orderOf_dvd_of_pow_eq_one hl
  have hx9 : x ^ 9 = 1 := by
    apply Subtype.ext
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, Matrix.SpecialLinearGroup.coe_pow, hcx, ← map_pow,
      hcx3, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hxo : orderOf x = 9 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := orderOf_eq_prime_pow (p := 3) (n := 1) (x := x) (by simpa using hx3) (by simpa using hx9)
    simpa using this
  obtain ⟨v, hvAM, hvx⟩ : ∃ v ∈ AM, v ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have hle : AM ≤ Subgroup.zpowers x := fun v hv => h v hv
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hxo, h27] at this
    omega
  obtain ⟨cv, hcv3, hcv⟩ := exists_scalar_of_mem_center (hcube v hvAM)
  obtain ⟨k, -, hk⟩ := hcxp.eq_pow_of_pow_eq_one hcv3
  have hcommvx : Commute v x := by
    have := hcomm.is_comm.comm ⟨v, hvAM⟩ ⟨x, hxAM⟩
    exact congrArg Subtype.val this
  set y₀ := v * (x ^ k)⁻¹ with hy₀
  have hy₀AM : y₀ ∈ AM := AM.mul_mem hvAM (AM.inv_mem (AM.pow_mem hxAM k))
  have hv3 : v ^ 3 = (x ^ 3) ^ k := by
    apply Subtype.ext
    change ((v ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((x ^ 3) ^ k : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hcv, Matrix.SpecialLinearGroup.coe_pow (x ^ 3) k, hcx, ← map_pow, hk]
  have hcvk : Commute v (x ^ k)⁻¹ := (hcommvx.pow_right k).inv_right
  have hy₀3 : y₀ ^ 3 = 1 := by
    rw [hy₀, hcvk.mul_pow, hv3, inv_pow, ← pow_mul, ← pow_mul, mul_comm k 3, mul_inv_cancel]
  have hy₀x : y₀ ∉ Subgroup.zpowers x := by
    intro h
    apply hvx
    have : v = y₀ * x ^ k := by rw [hy₀, inv_mul_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ h (Subgroup.npow_mem_zpowers x k)
  set u : Fin 3 → K := fun i => (y₀ : Matrix (Fin 3) (Fin 3) K) i i with hu
  have hu3 : ∀ i, u i ^ 3 = 1 := entry_pow_three hdiag hy₀AM hy₀3
  have hu0 : ∀ i, u i ≠ 0 := by
    intro i h0
    have := hu3 i
    rw [h0, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  obtain ⟨hyd, hyeq⟩ := eq_diag3_of_isDiag (hdiag y₀ hy₀AM)
  have hu12 : u 1 ≠ u 2 := by
    intro h12
    apply hy₀x
    have hprod : u 0 * u 1 * u 2 = 1 := by simpa [Fin.prod_univ_three, hu] using hyd
    have h0 : u 0 = u 1 := by
      rw [← h12] at hprod
      have h1 := hu3 1
      have : u 0 * (u 1 * u 1) = u 1 * (u 1 * u 1) := by
        rw [← mul_assoc, hprod]
        linear_combination -h1
      exact mul_right_cancel₀ (mul_ne_zero (hu0 1) (hu0 1)) this
    refine mem_zpowers_of_mem_center hcx hcxp ?_
    rw [← scalars_eq_center]
    refine ⟨Units.mk0 (u 1) (hu0 1), Units.ext (by simpa using hu3 1), ?_⟩
    rw [hyeq, coe_diag3]
    ext i j
    rw [scalar_apply]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, diagonal_apply_eq, Units.val_mk0]
      fin_cases i
      · exact h0
      · rfl
      · exact h12.symm
    · rw [diagonal_apply_ne _ hij, diagonal_apply_ne _ hij]
  set xe : Fin 3 → K := fun i => (x : Matrix (Fin 3) (Fin 3) K) i i with hxe
  have hxe3 : ∀ i, xe i ^ 3 = cx := by
    intro i
    have h := (pow_apply_of_isDiag (hdiag x hxAM) 3).2 i
    rw [hcx, scalar_apply, diagonal_apply_eq] at h
    exact h.symm
  have hxe0 : ∀ i, xe i ≠ 0 := by
    intro i h0
    have := hxe3 i
    rw [h0, zero_pow (by norm_num)] at this
    exact hcx1 (by rw [← this]; exact absurd this.symm (by
      intro h
      apply hcx1
      have hc0 : cx = 0 := h
      rw [hc0] at hcx3
      norm_num at hcx3))
  set ε := u 2 / u 1 with hε
  have hε3 : ε ^ 3 = 1 := by rw [hε, div_pow, hu3, hu3, div_one]
  have hε1 : ε ≠ 1 := by
    intro h
    apply hu12
    rw [hε, div_eq_one_iff_eq (hu0 1)] at h
    exact h.symm
  have hεp : IsPrimitiveRoot ε 3 := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨hε3, fun l hl => ?_⟩
    have h1 := orderOf_dvd_of_pow_eq_one hε3
    have h3 : orderOf ε = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hε1
      · exact h
    rw [← h3]
    exact orderOf_dvd_of_pow_eq_one hl
  have hr3 : (xe 1 / xe 2) ^ 3 = 1 := by
    rw [div_pow, hxe3, hxe3, div_self (by
      intro h
      apply hcx1
      rw [h] at hcx3
      norm_num at hcx3)]
  obtain ⟨j, -, hj⟩ := hεp.eq_pow_of_pow_eq_one hr3
  set a := x * y₀ ^ j with ha
  have haAM : a ∈ AM := AM.mul_mem hxAM (AM.pow_mem hy₀AM j)
  have hadiag := hdiag a haAM
  have hae : ∀ i, (a : Matrix (Fin 3) (Fin 3) K) i i = xe i * u i ^ j := by
    intro i
    rw [ha, mul_apply_of_isDiag (hdiag x hxAM), (pow_apply_of_isDiag (hdiag y₀ hy₀AM) j).2 i]
  set sv := xe 1 * u 1 ^ j with hsv
  have hs0 : sv ≠ 0 := mul_ne_zero (hxe0 1) (pow_ne_zero j (hu0 1))
  have ha1 : (a : Matrix (Fin 3) (Fin 3) K) 1 1 = sv := hae 1
  have ha2 : (a : Matrix (Fin 3) (Fin 3) K) 2 2 = sv := by
    rw [hae 2, hsv]
    have hu2 : u 2 = u 1 * ε := by rw [hε, mul_div_cancel₀ _ (hu0 1)]
    rw [hu2, mul_pow, hj]
    field_simp [hxe0 2]
  have hs3 : sv ^ 3 = cx := by
    rw [hsv, mul_pow, hxe3, ← pow_mul, mul_comm j 3, pow_mul, hu3, one_pow, mul_one]
  obtain ⟨had, haeq⟩ := eq_diag3_of_isDiag hadiag
  have ha0 : (a : Matrix (Fin 3) (Fin 3) K) 0 0 = (sv ^ 2)⁻¹ := by
    have hprod : (a : Matrix (Fin 3) (Fin 3) K) 0 0 * (a : Matrix (Fin 3) (Fin 3) K) 1 1 *
        (a : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by simpa [Fin.prod_univ_three] using had
    rw [ha1, ha2] at hprod
    have hs2 : sv ^ 2 ≠ 0 := pow_ne_zero 2 hs0
    calc (a : Matrix (Fin 3) (Fin 3) K) 0 0
        = (a : Matrix (Fin 3) (Fin 3) K) 0 0 * sv * sv * (sv ^ 2)⁻¹ := by
          field_simp
      _ = (sv ^ 2)⁻¹ := by rw [hprod, one_mul]
  refine ⟨sv, hs0, by rw [hs3, hcx3], by rw [hs3]; exact hcx1, ?_, y₀, hy₀AM, hu3, hu12⟩
  have hdeq : diag3 ![(sv ^ 2)⁻¹, sv, sv] (prod_dr hs0) = a := by
    rw [haeq]
    congr 1
    funext i
    fin_cases i
    · exact ha0.symm
    · exact ha1.symm
    · exact ha2.symm
  rw [hdeq]
  exact haAM

end AM

section Frame

theorem slC_diagGL_mul_slF_apply (α : Fin 3 → Kˣ) (τ : K ≃+* K) (g : SpecialLinearGroup (Fin 3) K)
    (i j : Fin 3) :
    (((slC (diagGL α) * slF τ) g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      (α i : K) * τ ((g : Matrix (Fin 3) (Fin 3) K) i j) * (((α j)⁻¹ : Kˣ) : K) := by
  rw [MulAut.mul_apply]
  exact slConjugation_diagGL_apply α _ i j

theorem eq_diagGL_of_isDiag {A : GL (Fin 3) K}
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ∃ α : Fin 3 → Kˣ, A = diagGL α := by
  have hne : ∀ i, (A : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    intro i h0
    have hdet := A.det_ne_zero
    apply hdet
    apply det_eq_zero_of_row_eq_zero i
    intro j
    by_cases hij : i = j
    · subst hij
      exact h0
    · exact hA i j hij
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  rw [coe_diagGL]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, Units.val_mk0]
  · rw [diagonal_apply_ne _ hij, hA i j hij]


theorem pow_three_eq_one_of {A : GL (Fin 3) K} {τ : K ≃+* K} (h : (slC A * slF τ) ^ 3 = 1) :
    τ ^ 3 = 1 := by
  have h1 : (conjAut 3 K A * fieldAut 3 K τ) ^ 3 = 1 := by
    rw [← descendAut_slC, ← descendAut_slF, ← map_mul, ← map_pow, h, map_one]
  exact (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin.conjAut_mul_fieldAut_pow_eq_one
    (le_refl 3) h1).1

theorem exists_diag_form {E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hE : IsElemAbelian 3 E)
    {s : K} (hs : s ≠ 0) (hs3 : s ^ 3 ≠ 1)
    (haE : MulAut.conj (diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs)) ∈ E)
    {y₀ : SpecialLinearGroup (Fin 3) K}
    (hy₀d : ∀ i j, i ≠ j → (y₀ : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (hu3 : ∀ i, (y₀ : Matrix (Fin 3) (Fin 3) K) i i ^ 3 = 1)
    (hu12 : (y₀ : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ (y₀ : Matrix (Fin 3) (Fin 3) K) 2 2)
    (hyE : MulAut.conj y₀ ∈ E) {γ : MulAut (SpecialLinearGroup (Fin 3) K)} (hγ : γ ∈ E) :
    ∃ (α : Fin 3 → Kˣ) (τ : K ≃+* K), τ ^ 3 = 1 ∧ γ = slC (diagGL α) * slF τ := by
  have hγ3 : γ ^ 3 = 1 := hE.2 γ hγ
  have hodd : Odd (orderOf γ) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hγ3) with h | h
    · rw [h]; exact odd_one
    · rw [h]; decide
  obtain ⟨A, τ, rfl⟩ := exists_eq_slC_mul_slF hodd
  have hτ3 := pow_three_eq_one_of hγ3
  have hcommE : ∀ δ ∈ E, (slC A * slF τ) * δ = δ * (slC A * slF τ) := fun δ hδ =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hγ⟩ ⟨δ, hδ⟩)
  obtain ⟨c, hc3, hc⟩ := rel_of_commute (hcommE _ haE)
  set dr : Fin 3 → K := ![(s ^ 2)⁻¹, s, s] with hdr
  have hdr' : ∏ i, (fun i => τ (dr i)) i = 1 := by
    rw [← map_prod τ dr, prod_dr hs, map_one]
  rw [coe_diag3, Matrix.diagonal_map (map_zero τ)] at hc
  have h01 : dr 0 ≠ dr 1 := by
    intro h
    have h' : (s ^ 2)⁻¹ = s := h
    apply hs3
    calc s ^ 3 = s ^ 2 * s := by ring
      _ = s ^ 2 * (s ^ 2)⁻¹ := by rw [h']
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hs)
  obtain ⟨-, hA01, hA02, hA10, hA20⟩ := blockDiag_of_mul_eq_smul A.det_ne_zero (prod_dr hs) hdr' rfl
    rfl h01 hc3 hc
  obtain ⟨c', -, hc'⟩ := rel_of_commute (hcommE _ hyE)
  obtain ⟨hyd, hyeq⟩ := eq_diag3_of_isDiag hy₀d
  have hyτ : (y₀ : Matrix (Fin 3) (Fin 3) K).map τ = y₀ := by
    ext i j
    rw [Matrix.map_apply]
    by_cases hij : i = j
    · subst hij
      exact apply_eq_of_pow_three hτ3 (hu3 i)
    · rw [hy₀d i j hij, map_zero]
  rw [hyτ, hyeq, coe_diag3] at hc'
  have hy0 : (y₀ : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    have := hu3 0
    rw [h0, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  obtain ⟨-, hA12, hA21⟩ := diag_of_blockDiag (y := fun i => (y₀ : Matrix (Fin 3) (Fin 3) K) i i)
    A.det_ne_zero hA01 hA02 hA10 hA20 hy0 hu12 hc'
  have hAd : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | assumption
  obtain ⟨α, rfl⟩ := eq_diagGL_of_isDiag hAd
  exact ⟨α, τ, hτ3, rfl⟩


theorem slC_diagGL_mem_coordBlockSL (d : Fin 3 → Kˣ) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ coordBlockSL K blk) : slC (diagGL d) g ∈ coordBlockSL K blk := by
  rw [mem_coordBlockSL_iff] at hg ⊢
  intro i j hij
  rw [slConjugation_diagGL_apply, hg i j hij]
  by_cases hij' : i = j
  · subst hij'
    simp
  · simp [hij']

theorem slC_diagGL_mul_slF_x12 (α : Fin 3 → Kˣ) (τ : K ≃+* K) (c : K) :
    (slC (diagGL α) * slF τ) (x12 c) = x12 ((α 1 : K) * (((α 2)⁻¹ : Kˣ) : K) * τ c) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [slC_diagGL_mul_slF_apply]
  simp only [x12, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  fin_cases i <;> fin_cases j <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem glaPLayer_block_inf_fix_ne_bot {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {b : Fin 3 → Kˣ} {τ : K ≃+* K} (hτ : orderOf τ = 3)
    (ha3 : (slC (diagGL b) * slF τ) ^ 3 = 1) (h4 : 4 ≤ Nat.card (semilinearFixedSubfield τ))
    {ω : K} (hω : IsPrimitiveRoot ω 3) (hωτ : τ ω = ω) :
    GLAPLayer 3 (coordBlockSL K blk ⊓ fixSubgroup (slC (diagGL b) * slF τ)) ≠ ⊥ := by
  classical
  set a := slC (diagGL b) * slF τ with ha
  set ρ : K := (b 1 : K) * (((b 2)⁻¹ : Kˣ) : K) with hρ
  have hρ0 : ρ ≠ 0 := mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have haX : ∀ c : K, a (x12 c) = x12 (ρ * τ c) := fun c => slC_diagGL_mul_slF_x12 b τ c
  clear_value ρ
  have hN : ∏ i ∈ Finset.range 3, (τ ^ i) ρ = 1 := by
    have h1 : (a ^ 3) (x12 1) = x12 1 := by rw [ha3]; rfl
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, haX, haX, haX, map_one,
      mul_one] at h1
    have h2 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 2) h1
    simp [x12, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply] at h2
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one,
      sq, RingAut.mul_apply, RingAut.one_apply]
    linear_combination h2
  obtain ⟨c₀, hc₀, hρc⟩ := CFSG.LieType.SeitzGeneration.exists_hilbert90 Nat.prime_three hℓ hf hK τ hτ ρ hN
  set d₀ : Fin 3 → Kˣ := ![1, Units.mk0 c₀ hc₀, 1] with hd₀
  set D := diagGL d₀ with hD
  set D' := diagGL (fun i => (d₀ i)⁻¹) with hD'
  set K₀ := semilinearFixedSubfield τ with hK₀
  have hk : ∀ x : K, x ∈ K₀ ↔ τ x = x := fun x => Iff.rfl
  have haE : ∀ (g : SpecialLinearGroup (Fin 3) K) (i j : Fin 3),
      ((a g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
        (b i : K) * τ ((g : Matrix (Fin 3) (Fin 3) K) i j) * (((b j)⁻¹ : Kˣ) : K) :=
    fun g i j => slC_diagGL_mul_slF_apply b τ g i j
  have hDE : ∀ (g : SpecialLinearGroup (Fin 3) K) (i j : Fin 3),
      ((slC D g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
        (d₀ i : K) * (g : Matrix (Fin 3) (Fin 3) K) i j * (((d₀ j)⁻¹ : Kˣ) : K) :=
    fun g i j => slConjugation_diagGL_apply d₀ g i j
  have hD'E : ∀ (g : SpecialLinearGroup (Fin 3) K) (i j : Fin 3),
      ((slC D' g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
        (((d₀ i)⁻¹ : Kˣ) : K) * (g : Matrix (Fin 3) (Fin 3) K) i j * (d₀ j : K) := by
    intro g i j
    rw [hD', slConjugation_diagGL_apply, inv_inv]
  have hDD' : ∀ g, slC D (slC D' g) = g := by
    intro g
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hDE, hD'E, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv,
      mul_one]
  set b' : Fin 3 → Kˣ := fun i => (d₀ i)⁻¹ * b i * Units.map (τ : K →* K) (d₀ i) with hb'
  have e1 : ((d₀ 1 : Kˣ) : K) = c₀ := by simp [hd₀]
  have e2 : ((d₀ 2 : Kˣ) : K) = 1 := by simp [hd₀]
  have hb'12 : b' 1 = b' 2 := by
    apply Units.ext
    have hv : ∀ i, ((b' i : Kˣ) : K) = (((d₀ i)⁻¹ : Kˣ) : K) * (b i : K) * τ ((d₀ i : Kˣ) : K) := by
      intro i
      simp [hb', Units.coe_map]
    rw [hv 1, hv 2, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, e1, e2, inv_one, one_mul,
      map_one, mul_one]
    have h1 : (b 1 : K) = ρ * (b 2 : K) := by
      rw [hρ, mul_assoc, Units.inv_mul, mul_one]
    rw [h1, mul_comm ρ, mul_assoc, mul_assoc, hρc, ← mul_assoc, mul_comm c₀⁻¹, mul_assoc,
      inv_mul_cancel₀ hc₀, mul_one]
  have ha₀ : (slC D)⁻¹ * a * slC D = slC (diagGL b') * slF τ := by
    have e1 : slF τ * slC D = slC (Matrix.GeneralLinearGroup.map (τ : K →+* K) D) * slF τ := by
      rw [← slF_mul_slC_mul_inv, inv_mul_cancel_right]
    rw [ha, mul_assoc, mul_assoc, e1, ← mul_assoc, ← mul_assoc, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hD]
    change (((diagGL d₀)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (diagGL b : GL (Fin 3) K) *
      ((diagGL d₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ = (diagGL b' : GL (Fin 3) K)
    rw [coe_diagGL_inv, coe_diagGL, coe_diagGL, coe_diagGL, Matrix.diagonal_map (map_zero τ),
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1 <;> (funext i; simp [hb', Units.coe_map])
  have ha₀B : ∀ g ∈ coordBlockSL K blk, ((slC D)⁻¹ * a * slC D) g = slF τ g := by
    intro g hg
    rw [ha₀, MulAut.mul_apply]
    refine slConjugation_diagGL_fixes_coordBlockSL b' (J := blk) (fun i hi j hj => ?_) ?_
    · have hi' : i = 1 ∨ i = 2 := by rw [mem_blk] at hi; fin_cases i <;> simp_all
      have hj' : j = 1 ∨ j = 2 := by rw [mem_blk] at hj; fin_cases j <;> simp_all
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp [hb'12]
    · rw [mem_coordBlockSL_iff] at hg ⊢
      intro i j hij
      rw [slF_coe, Matrix.map_apply, hg i j hij]
      split_ifs <;> simp
  set a₀ := (slC D)⁻¹ * a * slC D with ha₀def
  set B₀ := (coordBlockSL K₀ blk).map (incl0 τ) with hB₀
  have hB0 : coordBlockSL K blk ⊓ fixSubgroup a₀ = B₀ := by
    apply le_antisymm
    · rintro g ⟨hgB, hgF⟩
      have hfix : slF τ g = g := by rw [← ha₀B g hgB]; exact hgF
      have hent : ∀ i j, τ ((g : Matrix (Fin 3) (Fin 3) K) i j) = (g : Matrix (Fin 3) (Fin 3) K) i j := by
        intro i j
        have := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) i j) hfix
        simpa [slF_coe] using this
      let g₀ : Matrix (Fin 3) (Fin 3) K₀ := Matrix.of fun i j => ⟨_, (hk _).2 (hent i j)⟩
      have hg₀ : g₀.map K₀.subtype = g := Matrix.ext fun _ _ => rfl
      have hdet : g₀.det = 1 := Subtype.val_injective (by
        change K₀.subtype g₀.det = K₀.subtype 1
        rw [RingHom.map_det, map_one]
        change (g₀.map K₀.subtype).det = 1
        rw [hg₀]
        exact g.2)
      let g₁ : SpecialLinearGroup (Fin 3) K₀ := ⟨g₀, hdet⟩
      have hg₁B : g₁ ∈ coordBlockSL K₀ blk := by
        have hg2 := mem_coordBlockSL_iff.1 hgB
        rw [mem_coordBlockSL_iff]
        intro i j hij
        apply Subtype.val_injective
        change (g : Matrix (Fin 3) (Fin 3) K) i j = _
        rw [hg2 i j hij]
        split_ifs <;> rfl
      exact ⟨g₁, hg₁B, Subtype.ext hg₀⟩
    · rintro _ ⟨g₁, hg₁, rfl⟩
      refine ⟨incl0_mem_coordBlockSL τ hg₁, ?_⟩
      show a₀ (incl0 τ g₁) = incl0 τ g₁
      rw [ha₀B _ (incl0_mem_coordBlockSL τ hg₁)]
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [slF_coe, Matrix.map_apply]
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact ((g₁ : Matrix (Fin 3) (Fin 3) K₀) i j).2
  have hcD : Function.Injective (slC D).toMonoidHom := (slC D).injective
  have hblock : (coordBlockSL K blk).map (slC D).toMonoidHom = coordBlockSL K blk := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact slC_diagGL_mem_coordBlockSL d₀ hg
    · intro g hg
      refine ⟨slC D' g, slC_diagGL_mem_coordBlockSL _ hg, ?_⟩
      exact hDD' g
  have hfixmap : fixSubgroup a = (fixSubgroup a₀).map (slC D).toMonoidHom := by
    ext g
    constructor
    · intro hg
      refine ⟨(slC D)⁻¹ g, ?_, by simp⟩
      show a₀ ((slC D)⁻¹ g) = (slC D)⁻¹ g
      rw [ha₀def, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
      have hg' : a g = g := hg
      rw [hg']
    · rintro ⟨h, hh, rfl⟩
      have hh' : a₀ h = h := hh
      show a ((slC D) h) = (slC D) h
      have : a = slC D * a₀ * (slC D)⁻¹ := by rw [ha₀def]; group
      rw [this, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hh']
  have hL : coordBlockSL K blk ⊓ fixSubgroup a = B₀.map (slC D).toMonoidHom := by
    rw [← hB0, Subgroup.map_inf_eq _ _ _ hcD, hblock, hfixmap]
  have e1 : ↥(coordBlockSL K₀ blk) ≃* ↥B₀ :=
    Subgroup.equivMapOfInjective _ (incl0 τ) (incl0_injective τ)
  have e2 : ↥B₀ ≃* ↥(B₀.map (slC D).toMonoidHom) := Subgroup.equivMapOfInjective _ _ hcD
  have hω₀ : IsPrimitiveRoot (⟨ω, hωτ⟩ : K₀) 3 :=
    (IsPrimitiveRoot.map_iff_of_injective (f := K₀.subtype) Subtype.val_injective).1 hω
  have hq0 : CFSG.Open.IsQuasisimple ↥(coordBlockSL K₀ blk) :=
    isQuasisimple_coordBlockSL (J := blk) (by decide) h4
  have hq : CFSG.Open.IsQuasisimple ↥(B₀.map (slC D).toMonoidHom) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv (e1.trans e2).symm hq0
  have hdvd : 3 ∣ Nat.card (↥(B₀.map (slC D).toMonoidHom) ⧸
      Subgroup.center ↥(B₀.map (slC D).toMonoidHom)) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.natCard_quotient_center_congr (e1.trans e2)]
    exact dvd_card_coordBlockSL_blk Nat.prime_three (by norm_num) hω₀
  rw [hL]
  refine CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple Nat.prime_three
    le_rfl ?_ hq hdvd
  rw [Subgroup.subgroupOf_self]
  infer_instance

end Frame

section Data

theorem x12_mul_inv (a b : K) : x12 a * (x12 b)⁻¹ = x12 (a - b) := by
  rw [x12, x12, x12, Matrix.SpecialLinearGroup.transvection_inv,
    ← Matrix.SpecialLinearGroup.transvection_add, sub_eq_add_neg]

theorem diagGL_mul (u v : Fin 3 → Kˣ) : diagGL u * diagGL v = diagGL (u * v) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagonal_mul_diagonal]
  congr 1

theorem slC_diagGL_pow (u : Fin 3 → Kˣ) (k : ℕ) : slC (diagGL u) ^ k = slC (diagGL (u ^ k)) := by
  induction k with
  | zero =>
    have h1 : diagGL (1 : Fin 3 → Kˣ) = 1 := by
      apply Units.ext
      rw [coe_diagGL, Units.val_one]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
    rw [pow_zero, pow_zero, h1, map_one]
  | succ k ih => rw [pow_succ, ih, ← map_mul, diagGL_mul, pow_succ]

theorem conj_diag3 (d : Fin 3 → K) (hd : ∏ i, d i = 1) :
    MulAut.conj (diag3 d hd) =
      slC (diagGL fun i => Units.mk0 (d i) (ne_zero_of_prod_eq_one hd i)) := by
  rw [← slC_toGL]
  congr 1
  apply Units.ext
  rw [coe_diagGL]
  simp [Matrix.SpecialLinearGroup.toGL, coe_diag3]

theorem fixSubgroup_conj {G : Type*} [Group G] (d : G) :
    fixSubgroup (MulAut.conj d) = Subgroup.centralizer ({d} : Set G) := by
  ext g
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc g * d = d * g * d⁻¹ * d := by rw [h]
      _ = d * g := by group
  · intro h
    rw [← h]
    group

theorem mem_center_of_conj_eq_one {G : Type*} [Group G] {d : G} (h : MulAut.conj d = 1) :
    d ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := DFunLike.congr_fun h g
  rw [MulAut.conj_apply, MulAut.one_apply] at h1
  calc g * d = d * g * d⁻¹ * d := by rw [h1]
    _ = d * g := by group

theorem slC_diagGL_mul_slF_du (α : Fin 3 → Kˣ) (τ : K ≃+* K) :
    (slC (diagGL α) * slF τ) (diag3 ![1, -1, -1] prod_du) = diag3 ![1, -1, -1] prod_du := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [slC_diagGL_mul_slF_apply, coe_diag3]
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq]
    fin_cases i <;> simp
  · rw [diagonal_apply_ne _ hij, map_zero, mul_zero, zero_mul]

theorem mem_zpowers_of_centMod {s : K} (hs : s ≠ 0) (hω : IsPrimitiveRoot (s ^ 3) 3)
    (hF : 4 ≤ Nat.card K) {α : Fin 3 → Kˣ} {τ : K ≃+* K} (h3 : (slC (diagGL α) * slF τ) ^ 3 = 1)
    (hcm : ∀ j ∈ coordBlockSL K blk,
      (slC (diagGL α) * slF τ) j * j⁻¹ ∈ GLAPPrimeCoreOf 3 (coordBlockSL K blk)) :
    slC (diagGL α) * slF τ ∈
      Subgroup.zpowers (MulAut.conj (diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs))) := by
  have hq := isQuasisimple_coordBlockSL_blk Nat.prime_three (by norm_num) hω hF
  have hdvd := dvd_card_coordBlockSL_blk (F := K) Nat.prime_three (by norm_num) hω
  have htest : ∀ c : K, (α 1 : K) * (((α 2)⁻¹ : Kˣ) : K) * τ c = c := by
    intro c
    have h1 := hcm _ (x12_mem_coordBlockSL c)
    rw [slC_diagGL_mul_slF_x12, x12_mul_inv] at h1
    have h2 := commute_of_mem_glaPPrimeCoreOf Nat.prime_three hq hdvd h1 (x21_mem_coordBlockSL 1)
    have h3 := Lin.eq_zero_of_proj_x12_commute (K := K) (by rw [← map_mul, ← map_mul, h2])
    exact sub_eq_zero.1 h3
  have hρ1 : (α 1 : K) * (((α 2)⁻¹ : Kˣ) : K) = 1 := by
    have := htest 1
    rwa [map_one, mul_one] at this
  have hτ1 : τ = 1 := by
    ext c
    have := htest c
    rw [hρ1, one_mul] at this
    rw [RingAut.one_apply]
    exact this
  subst hτ1
  have hα12 : α 1 = α 2 := by
    apply Units.ext
    rw [Units.val_inv_eq_inv_val] at hρ1
    exact (mul_inv_eq_one₀ (Units.ne_zero _)).1 hρ1
  rw [map_one, mul_one] at h3 ⊢
  rw [slC_diagGL_pow] at h3
  obtain ⟨c, hc⟩ := (slC_eq_one_iff _).1 h3
  have e : ∀ i, (c : K) = (α i : K) ^ 3 := by
    intro i
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i i) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar, coe_diagGL, Matrix.scalar_apply] using this
  have ht3 : ((α 0 : K) * ((α 1 : K))⁻¹) ^ 3 = 1 := by
    rw [mul_pow, inv_pow, ← e 0, ← e 1, mul_inv_cancel₀ (Units.ne_zero c)]
  obtain ⟨k, -, hk⟩ := hω.inv.eq_pow_of_pow_eq_one ht3
  have hα0 : (α 0 : K) = ((s ^ 3)⁻¹) ^ k * (α 1 : K) := by
    rw [hk, mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), mul_one]
  have key : (s ^ 3)⁻¹ ^ k = (s ^ k)⁻¹ * (s ^ 2)⁻¹ ^ k := by
    rw [inv_pow, inv_pow, ← mul_inv]
    congr 1
    ring
  have hγ : slC (diagGL α) = MulAut.conj (diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs)) ^ k := by
    rw [conj_diag3, slC_diagGL_pow]
    ext g : 1
    refine slConjugation_diagGL_congr α _ (α 1 * (Units.mk0 s hs ^ k)⁻¹) (fun i => ?_) g
    apply Units.ext
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val, Units.val_mk0, Pi.pow_apply, Matrix.cons_val_zero]
      rw [hα0, key]
      ring
    · simp only [Fin.mk_one, Fin.isValue, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val, Units.val_mk0, Pi.pow_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.reduceFinMk, Fin.isValue, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val, Units.val_mk0, Pi.pow_apply, Matrix.cons_val_two,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons]
      rw [← hα12]
      field_simp
  rw [hγ]
  exact Subgroup.npow_mem_zpowers _ k

theorem z3Data_of_diag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ4 : 4 ≤ ℓ)
    (h2K : (2 : K) ≠ 0) {E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))}
    (hE : IsElemAbelian 3 E) {AM : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hcomm : IsMulCommutative AM)
    (hEq : E ⊓ (MulAut.conj : SpecialLinearGroup (Fin 3) K →* MulAut (SpecialLinearGroup (Fin 3) K)).range =
      AM.map MulAut.conj)
    (hdiag : ∀ d ∈ AM, ∀ i j, i ≠ j → (d : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (h27 : Nat.card AM = 27) {a : MulAut (SpecialLinearGroup (Fin 3) K)} (haE : a ∈ E)
    (haD : a ∉ (slC (K := K)).range) :
    Z3Data 3 (SpecialLinearGroup (Fin 3) K) E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconjE : ∀ d ∈ AM, MulAut.conj d ∈ E := by
    intro d hd
    have h : MulAut.conj d ∈ E ⊓ (MulAut.conj : SpecialLinearGroup (Fin 3) K →*
        MulAut (SpecialLinearGroup (Fin 3) K)).range := by
      rw [hEq]
      exact Subgroup.mem_map_of_mem _ hd
    exact h.1
  have hcube : ∀ d ∈ AM, d ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := fun d hd =>
    mem_center_of_conj_eq_one (by rw [map_pow]; exact hE.2 _ (hconjE d hd))
  obtain ⟨s, hs, hs9, hs3, ha'AM, y₀, hy₀AM, hu3, hu12⟩ := exists_y0_aprime hdiag hcube hcomm h27
  have hβE := hconjE _ ha'AM
  have hyE := hconjE _ hy₀AM
  have hω : IsPrimitiveRoot (s ^ 3) 3 := by
    have h := IsPrimitiveRoot.orderOf (s ^ 3)
    rwa [orderOf_eq_prime hs9 hs3] at h
  have h01 : (![(s ^ 2)⁻¹, s, s] : Fin 3 → K) 0 ≠ ![(s ^ 2)⁻¹, s, s] 1 := by
    intro h
    have h' : (s ^ 2)⁻¹ = s := h
    apply hs3
    calc s ^ 3 = s ^ 2 * s := by ring
      _ = s ^ 2 * (s ^ 2)⁻¹ := by rw [h']
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hs)
  have hF : 4 ≤ Nat.card K := by
    rw [hK]
    exact hℓ4.trans (Nat.le_self_pow (by omega) ℓ)
  have hfix := fixSubgroup_conj (diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs))
  have hJ : GLAPLayer 3 (fixSubgroup (MulAut.conj (diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs)))) =
      coordBlockSL K blk := by
    rw [hfix]
    exact CFSG.LocalAnalysis.GLTheoremA.H81.layer_eq_of_unique
      (glaPComponent_cent_diag3 Nat.prime_three (by norm_num) hω hF (prod_dr hs) rfl h01)
      (fun _ hK' => eq_of_glaPComponent_cent_diag3 Nat.prime_three (by norm_num) hω hF (prod_dr hs) rfl
        h01 hK')
  set u := diag3 ![1, -1, -1] (prod_du (K := K)) with hu
  have hu1 : u ≠ 1 := by
    intro h
    have h11 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) h
    simp only [hu, coe_diag3, diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at h11
    apply h2K
    have h' : (-1 : K) = 1 := h11
    linear_combination -h'
  have hu2 : u ^ 2 = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hu, coe_diag3_pow, Matrix.SpecialLinearGroup.coe_one]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, one_apply_eq, Pi.pow_apply]
      fin_cases i <;> simp
    · rw [diagonal_apply_ne _ hij, one_apply_ne hij]
  obtain ⟨b, τ, hτ3, rfl⟩ := exists_diag_form hE hs hs3 hβE (hdiag y₀ hy₀AM) hu3 hu12 hyE haE
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact haD ⟨diagGL b, by rw [map_one, mul_one]⟩
  have hτ : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
  have h4 : 4 ≤ Nat.card (semilinearFixedSubfield τ) := by
    obtain ⟨h3f, hq₀⟩ := CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ hf hK hτ
    rw [hq₀]
    have : f / 3 ≠ 0 := by
      obtain ⟨m, hm⟩ := h3f
      omega
    exact hℓ4.trans (Nat.le_self_pow this ℓ)
  have hωτ : τ (s ^ 3) = s ^ 3 := apply_eq_of_pow_three hτ3 hs9
  refine ⟨MulAut.conj (diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs)), hβE, ?_, ?_, ?_,
    ⟨slC (diagGL b) * slF τ, haE, ?_, ?_⟩, ⟨Subgroup.zpowers u, ?_, ?_, ?_⟩, u, hu1, hu2, ?_, ?_⟩
  ·
    intro h
    obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_center (mem_center_of_conj_eq_one h)
    have e0 := congrFun (congrFun hc 0) 0
    have e1 := congrFun (congrFun hc 1) 1
    rw [coe_diag3, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at e0 e1
    exact h01 (e0.trans e1.symm)
  · rw [hJ, hfix]
    exact glaPComponent_cent_diag3 Nat.prime_three (by norm_num) hω hF (prod_dr hs) rfl h01
  · intro γ hγ hcm
    rw [hJ] at hcm
    obtain ⟨α, σ, -, rfl⟩ := exists_diag_form hE hs hs3 hβE (hdiag y₀ hy₀AM) hu3 hu12 hyE hγ
    exact mem_zpowers_of_centMod hs hω hF (hE.2 _ hγ) hcm
  ·
    intro h
    apply haD
    have hle : Subgroup.zpowers (MulAut.conj (diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs))) ≤
        (slC (K := K)).range :=
      Subgroup.zpowers_le.2 ⟨_, slC_toGL _⟩
    exact hle h
  · rw [hJ]
    exact glaPLayer_block_inf_fix_ne_bot hℓ hf hK hτ (hE.2 _ haE) h4 hω hωτ
  · intro h
    apply hu1
    have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers _
    rw [h] at this
    exact this
  · intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, hu2, _root_.one_zpow, Subgroup.coe_one]
  · intro γ hγ
    obtain ⟨α, σ, -, rfl⟩ := exists_diag_form hE hs hs3 hβE (hdiag y₀ hy₀AM) hu3 hu12 hyE hγ
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (slC_diagGL_mul_slF_du α σ)
  ·
    rw [MulAut.conj_apply, hu]
    have hc : diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs) * diag3 ![1, -1, -1] prod_du =
        diag3 ![1, -1, -1] prod_du * diag3 ![(s ^ 2)⁻¹, s, s] (prod_dr hs) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag3, diagonal_mul_diagonal, mul_comm]
    rw [hc, mul_inv_cancel_right]
  · intro j hj
    rw [hJ] at hj
    have hgc := coordBlockSL_le_centralizer_diag3 (d := ![1, -1, -1]) (hd := prod_du) rfl hj
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    exact hgc

end Data

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin3

end
