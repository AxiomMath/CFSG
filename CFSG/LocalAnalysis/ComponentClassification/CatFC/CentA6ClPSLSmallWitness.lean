module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionQuotient

public section

namespace CFSG.ComponentClassification.CatFC.PSLSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  (ordinaryCentralizerScalar ordinaryCentralizerProjection)

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

section Witness

variable {n : ℕ} {K : Type} [Field K] [Finite K]

abbrev slToPsl (n : ℕ) (K : Type) [Field K] :
    SpecialLinearGroup (Fin n) K →* ProjectiveSpecialLinearGroup (Fin n) K :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K))

theorem psl_witness {σ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K)}
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

section Inner

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_one_of_scalar_eq_one {s : ℕ} (hs : 1 ≤ s) {c : Kˣ}
    (h : GeneralLinearGroup.scalar (Fin s) c = 1) : c = 1 := by
  have h1 := congrArg (fun M : GL (Fin s) K => (M : Matrix (Fin s) (Fin s) K) ⟨0, hs⟩ ⟨0, hs⟩) h
  apply Units.ext
  simpa using h1

theorem fixed_of_centralizer {Q : Type} [Group Q] (hQ : commutator Q = ⊤) (A : GL (Fin n) K)
    (χ : Q →* Subgroup.centralizer ({A} : Set (GL (Fin n) K))) (g : Q) :
    innerDiagonalAction n K A
        (slToPsl n K (slHomOfPerfect hQ ((Subgroup.centralizer ({A} : Set (GL (Fin n) K))).subtype.comp χ) g)) =
      slToPsl n K (slHomOfPerfect hQ ((Subgroup.centralizer ({A} : Set (GL (Fin n) K))).subtype.comp χ) g) := by
  rw [innerDiagonalAction_mk]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, toGL_slHomOfPerfect]
  exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp (χ g).2).symm

theorem inner_factor_card_le {A : GL (Fin n) K}
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction n K A))}
    (h : A6Hyp (innerDiagonalAction n K A) D) {r s : ℕ} (hs : 1 ≤ s)
    (e : Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ≃* GL (Fin r) K × GL (Fin s) K)
    (hsc : ∀ c : Kˣ, e (ordinaryCentralizerScalar A c) =
      (GeneralLinearGroup.scalar (Fin r) c, GeneralLinearGroup.scalar (Fin s) c))
    (hperf : commutator (SpecialLinearGroup (Fin r) K) = ⊤) :
    Nat.card (SpecialLinearGroup (Fin r) K) ≤ 360 := by
  let χ : SpecialLinearGroup (Fin r) K →* Subgroup.centralizer ({A} : Set (GL (Fin n) K)) :=
    e.symm.toMonoidHom.comp ((MonoidHom.inl _ _).comp SpecialLinearGroup.toGL)
  let f := (Subgroup.centralizer ({A} : Set (GL (Fin n) K))).subtype.comp χ
  let ψ := slHomOfPerfect hperf f
  have hψGL : ∀ g, SpecialLinearGroup.toGL (ψ g) = (χ g).val := fun g =>
    toGL_slHomOfPerfect hperf f g
  have hker : ((slToPsl n K).comp ψ).ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : ψ g ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hg)
    have h2 : (χ g).val ∈ Subgroup.center (GL (Fin n) K) := by
      rw [← hψGL]
      exact (Matrix.SpecialLinearGroup.toGL_mem_center_iff _).mpr h1
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨c, hc⟩ := h2
    have h3 : χ g = ordinaryCentralizerScalar A c := Subtype.ext hc.symm
    have h4 : e (χ g) = (SpecialLinearGroup.toGL g, 1) := by simp [χ]
    rw [h3, hsc] at h4
    have h5 := Prod.mk.inj h4
    have hc1 : c = 1 := eq_one_of_scalar_eq_one hs h5.2
    have h6 : SpecialLinearGroup.toGL g = 1 := by
      rw [← h5.1, hc1, map_one]
    exact Subgroup.mem_bot.mpr (SpecialLinearGroup.toGL_injective (by rw [h6, map_one]))
  have := psl_witness h hperf ψ (fun g => fixed_of_centralizer hperf A χ g) (k := 1)
    (by rw [hker]; simp)
  simpa using this

end Inner

end CFSG.ComponentClassification.CatFC.PSLSmall
