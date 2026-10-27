module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace PSLA6

theorem det_eq_one_of_perfect {Q : Type*} [Group Q] (hQ : commutator Q = ⊤) {n : ℕ} {K : Type*}
    [Field K] (f : Q →* GL (Fin n) K) (g : Q) : Matrix.GeneralLinearGroup.det (f g) = 1 := by
  have h := Abelianization.commutator_subset_ker
    ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K)).comp f)
  have hg : g ∈ commutator Q := by rw [hQ]; exact Subgroup.mem_top g
  exact MonoidHom.mem_ker.mp (h hg)

noncomputable def slHomOfPerfect {Q : Type*} [Group Q] (hQ : commutator Q = ⊤) {n : ℕ} {K : Type}
    [Field K] (f : Q →* GL (Fin n) K) : Q →* SpecialLinearGroup (Fin n) K :=
  (CatalogueBGeneralLinear.rangeEquivSpecialLinear n K).toMonoidHom.comp
    (f.codRestrict (CatalogueBGeneralLinear.specialLinearRange n K) (fun g => by
      rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel]
      exact det_eq_one_of_perfect hQ f g))

theorem toGL_slHomOfPerfect {Q : Type*} [Group Q] (hQ : commutator Q = ⊤) {n : ℕ} {K : Type}
    [Field K] (f : Q →* GL (Fin n) K) (g : Q) :
    SpecialLinearGroup.toGL (slHomOfPerfect hQ f g) = f g :=
  CatalogueBGeneralLinear.rangeEquivSpecialLinear_toGL n K _

abbrev slToPsl (n : ℕ) (K : Type) [Field K] :
    SpecialLinearGroup (Fin n) K →* ProjectiveSpecialLinearGroup (Fin n) K :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K))

theorem card_center_SL_le (n : ℕ) (K : Type) [Field K] (hn : 1 ≤ n) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K)) ≤ n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n)
    (R := K)).toEquiv]
  haveI : NeZero (max (Fintype.card (Fin n)) 1) := ⟨by simp⟩
  have := card_rootsOfUnity K (max (Fintype.card (Fin n)) 1)
  simpa [Fintype.card_fin, Nat.max_eq_left hn] using this

theorem ker_card_le_of_injective {n : ℕ} {K : Type} [Field K] [Finite K] {Q : Type} [Group Q]
    (ψ : Q →* SpecialLinearGroup (Fin n) K) (hψ : Function.Injective ψ) (hn : 1 ≤ n) :
    Nat.card ((slToPsl n K).comp ψ).ker ≤ n := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun g : ((slToPsl n K).comp ψ).ker => (⟨ψ g.1, ?_⟩ :
      Subgroup.center (SpecialLinearGroup (Fin n) K))) ?_) (card_center_SL_le n K hn)
  · have := g.2
    rw [MonoidHom.mem_ker] at this
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro g g' h
    exact Subtype.ext (hψ (congrArg Subtype.val h))

theorem card_SL_ge (n : ℕ) {K : Type*} [Field K] [Finite K] (hn : 1 ≤ n) :
    Nat.card K ^ (n * (n - 1)) * (Nat.card K - 1) ^ (n - 1) ≤
      Nat.card (SpecialLinearGroup (Fin n) K) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  letI : Fintype K := Fintype.ofFinite K
  have h1 := Matrix.card_SL_mul_card_units (n := Fin n) (R := K)
  rw [Matrix.card_GL_field, Nat.card_units] at h1
  simp only [← Nat.card_eq_fintype_card] at h1
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hprod : (q ^ (n - 1) * (q - 1)) ^ n ≤ ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) := by
    have hc : (q ^ (n - 1) * (q - 1)) ^ n = ∏ _i : Fin n, (q ^ (n - 1) * (q - 1)) := by
      simp [Finset.prod_const]
    rw [hc]
    refine Finset.prod_le_prod (fun i _ => ?_)
    have hi : (i : ℕ) ≤ n - 1 := by have := i.2; omega
    have h2 : q ^ (i : ℕ) ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) hi
    have h3 : q ^ n = q ^ (n - 1) * q := by
      rw [← pow_succ]; congr 1; omega
    rw [h3, Nat.mul_sub, mul_one]
    omega
  have h4 : (q ^ (n - 1) * (q - 1)) ^ n = (q - 1) * (q ^ (n * (n - 1)) * (q - 1) ^ (n - 1)) := by
    rw [mul_pow, ← pow_mul, mul_comm n (n - 1)]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  have h5 : (q - 1) * (q ^ (n * (n - 1)) * (q - 1) ^ (n - 1)) ≤
      (q - 1) * Nat.card (SpecialLinearGroup (Fin n) K) := by
    rw [← h4, mul_comm (q - 1) _, h1]
    exact hprod
  exact Nat.le_of_mul_le_mul_left h5 (by omega)

theorem lt_three_pow_mul_two_pow {t : ℕ} (ht : 3 ≤ t) :
    720 * t < 3 ^ (t * (t - 1)) * 2 ^ (t - 1) := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    have h1 : 3 ^ ((t + 1) * (t + 1 - 1)) * 2 ^ (t + 1 - 1) =
        (3 ^ (t * (t - 1)) * 2 ^ (t - 1)) * (3 ^ (2 * t) * 2) := by
      obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [show (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) by ring,
        show m + 1 = m + 1 from rfl, pow_add, pow_succ 2 m]
      ring
    have h2 : 2 ≤ 3 ^ (2 * t) * 2 := by
      have : 1 ≤ 3 ^ (2 * t) := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [h1]
    calc 720 * (t + 1) ≤ 720 * t * 2 := by omega
      _ < (3 ^ (t * (t - 1)) * 2 ^ (t - 1)) * 2 := by omega
      _ ≤ (3 ^ (t * (t - 1)) * 2 ^ (t - 1)) * (3 ^ (2 * t) * 2) := Nat.mul_le_mul_left _ h2

theorem lt_card_SL_of_three_le {t : ℕ} {K : Type*} [Field K] [Finite K] (ht : 3 ≤ t)
    (hK : 3 ≤ Nat.card K) : 720 * t < Nat.card (SpecialLinearGroup (Fin t) K) := by
  refine lt_of_lt_of_le (lt_three_pow_mul_two_pow ht) (le_trans ?_ (card_SL_ge t (by omega)))
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hK _) (Nat.pow_le_pow_left (by omega) _)

theorem card_SL_two (K : Type) [Field K] [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [← CFSG.Open.StatedAPI.card_statedSL]
  exact CFSG.Open.StatedAPI.card_statedSL_two K

theorem card_fixedSubgroup_dvd {X : Type} [Group X] [Finite X] (σ : MulAut X) :
    Nat.card (fixedSubgroup σ) ∣ Nat.card X :=
  Subgroup.card_subgroup_dvd_card (fixedSubgroup σ)

end PSLA6

open PSLA6

section Witness

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem A6Hyp.psl_witness {σ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K)}
    {D : Subgroup ↥(fixedSubgroup σ)} (h : A6Hyp σ D) {Q : Type} [Group Q] [Finite Q]
    (hQ : commutator Q = ⊤) (ψ : Q →* SpecialLinearGroup (Fin n) K)
    (hfix : ∀ g, σ (slToPsl n K (ψ g)) = slToPsl n K (ψ g)) {k : ℕ}
    (hk : Nat.card ((slToPsl n K).comp ψ).ker ≤ k) : Nat.card Q ≤ 360 * k := by
  let φ : Q →* ↥(fixedSubgroup σ) :=
    ((slToPsl n K).comp ψ).codRestrict (fixedSubgroup σ) (fun g => hfix g)
  have hker : φ.ker = ((slToPsl n K).comp ψ).ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hg
      exact congrArg Subtype.val hg
    · intro hg
      exact Subtype.ext hg
  exact h.perfect_card_le_mul φ hQ (by rw [hker]; exact hk)

end Witness

section OrderTests

variable {X : Type} [Group X] [Finite X] {σ : MulAut X} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.false_psl_three_three (h : A6Hyp σ D) (hO : LieOrderFormulasInput)
    (hadm : StatedLieAdmissible .PSL 3 3 1) (hm : LieModel X .PSL 3 3 1) : False := by
  obtain ⟨-, hord, -⟩ := hO X .PSL 3 3 1 hadm hm
  have h1 : lieOrderNumerator .PSL 3 (3 ^ 1) = 5616 := by decide
  have h2 : lieOrderDivisor .PSL 3 (3 ^ 1) = 1 := by decide
  rw [h1, h2] at hord
  have h3 := (h.dvd).trans (card_fixedSubgroup_dvd σ)
  rw [show Nat.card X = 5616 by omega] at h3
  omega

theorem A6Hyp.false_psl_two_two (h : A6Hyp σ D) (hσ : orderOf σ = 2) (hO : LieOrderFormulasInput)
    (hadm : StatedLieAdmissible .PSL 2 3 2) (hm : LieModel X .PSL 2 3 2) : False := by
  obtain ⟨-, hord, -⟩ := hO X .PSL 2 3 2 hadm hm
  have h1 : lieOrderNumerator .PSL 2 (3 ^ 2) = 720 := by decide
  have h2 : lieOrderDivisor .PSL 2 (3 ^ 2) = 2 := by decide
  rw [h1, h2] at hord
  have hX : Nat.card X = 360 := by omega
  have h3 := Nat.le_of_dvd Nat.card_pos (card_fixedSubgroup_dvd σ)
  have h4 : Nat.card (fixedSubgroup σ) = Nat.card X :=
    le_antisymm h3 (by rw [hX]; exact Nat.le_of_dvd Nat.card_pos h.dvd)
  have h5 : fixedSubgroup σ = ⊤ := Subgroup.eq_top_of_card_eq _ h4
  have h6 : σ = 1 := by
    ext x
    have : x ∈ fixedSubgroup σ := by rw [h5]; exact Subgroup.mem_top x
    exact this
  rw [h6, orderOf_one] at hσ
  omega

end OrderTests

end CFSG.ComponentClassification.CatFC
