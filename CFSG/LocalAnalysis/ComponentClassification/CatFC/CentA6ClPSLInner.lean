module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticMatrix

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  (ordinaryCentralizerScalar ordinaryCentralizerProjection
    ordinaryCentralizerProjection_range_normal ordinaryCentralizerProjection_range_index_le_two)
open CFSG.ComponentClassification.CatalogueBHigherLinearInner (innerFixedCentralizerEquiv)

namespace PSLA6

section Inner

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_one_of_scalar_eq_one {s : ℕ} (hs : 1 ≤ s) {c : Kˣ}
    (h : GeneralLinearGroup.scalar (Fin s) c = 1) : c = 1 := by
  have h1 := congrArg (fun M : GL (Fin s) K => (M : Matrix (Fin s) (Fin s) K) ⟨0, hs⟩ ⟨0, hs⟩) h
  apply Units.ext
  simpa using h1

theorem fixed_of_centralizer {Q : Type} [Group Q] (hQ : commutator Q = ⊤) (A : GL (Fin n) K)
    (χ : Q →* Subgroup.centralizer ({A} : Set (GL (Fin n) K))) (g : Q) :
    let ψ := slHomOfPerfect hQ ((Subgroup.centralizer ({A} : Set (GL (Fin n) K))).subtype.comp χ)
    innerDiagonalAction n K A (slToPsl n K (ψ g)) = slToPsl n K (ψ g) := by
  intro ψ
  rw [innerDiagonalAction_mk]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, toGL_slHomOfPerfect]
  exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp (χ g).2).symm

theorem a6_psl_inner_factor {A : GL (Fin n) K}
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
  have := h.psl_witness hperf ψ (fun g => fixed_of_centralizer hperf A χ g) (k := 1)
    (by rw [hker]; simp)
  simpa using this

theorem a6_psl_inner_quad {A : GL (Fin n) K}
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction n K A))}
    (h : A6Hyp (innerDiagonalAction n K A) D) (hn : 1 ≤ n) {E : Type} [Field E] {m : ℕ}
    (e : Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ≃* GL (Fin m) E)
    (hperf : commutator (SpecialLinearGroup (Fin m) E) = ⊤) [Finite E] :
    Nat.card (SpecialLinearGroup (Fin m) E) ≤ 360 * n := by
  let χ : SpecialLinearGroup (Fin m) E →* Subgroup.centralizer ({A} : Set (GL (Fin n) K)) :=
    e.symm.toMonoidHom.comp SpecialLinearGroup.toGL
  let f := (Subgroup.centralizer ({A} : Set (GL (Fin n) K))).subtype.comp χ
  let ψ := slHomOfPerfect hperf f
  have hψGL : ∀ g, SpecialLinearGroup.toGL (ψ g) = (χ g).val := fun g =>
    toGL_slHomOfPerfect hperf f g
  have hinj : Function.Injective ψ := by
    intro g g' hgg
    have h1 : (χ g).val = (χ g').val := by rw [← hψGL, ← hψGL, hgg]
    have h2 : χ g = χ g' := Subtype.ext h1
    have h3 : SpecialLinearGroup.toGL g = SpecialLinearGroup.toGL g' := e.symm.injective h2
    exact SpecialLinearGroup.toGL_injective h3
  exact h.psl_witness hperf ψ (fun g => fixed_of_centralizer hperf A χ g)
    (ker_card_le_of_injective ψ hinj hn)

theorem isSolvable_of_card_le_two {Q : Type*} [Group Q] [Finite Q] (h : Nat.card Q ≤ 2) :
    Group.IsSolvable Q := by
  have hpos : 0 < Nat.card Q := Nat.card_pos
  rcases (by omega : Nat.card Q = 1 ∨ Nat.card Q = 2) with h1 | h2
  · haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := isCyclic_of_prime_card h2
    exact isSolvable_of_comm fun a b => (IsCyclic.commGroup (α := Q)).mul_comm a b

theorem isSolvable_fixed_of_comm (hn : 1 ≤ n) (A : GL (Fin n) K)
    (hsq : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    (hcomm : ∀ x y : Subgroup.centralizer ({A} : Set (GL (Fin n) K)), x * y = y * x) :
    Group.IsSolvable ↥(fixedSubgroup (innerDiagonalAction n K A)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set R := (ordinaryCentralizerProjection A).range with hR
  haveI : R.Normal := ordinaryCentralizerProjection_range_normal A
  have hRsolv : Group.IsSolvable R := by
    haveI : Group.IsSolvable ↥(Subgroup.centralizer ({A} : Set (GL (Fin n) K))) :=
      isSolvable_of_comm hcomm
    exact solvable_of_surjective (ordinaryCentralizerProjection A).rangeRestrict_surjective
  haveI : Finite (Matrix.ProjGenLinGroup (Fin n) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hQsolv : Group.IsSolvable (↥(Subgroup.centralizer ({Matrix.ProjGenLinGroup.mk A} :
      Set (Matrix.ProjGenLinGroup (Fin n) K))) ⧸ R) :=
    isSolvable_of_card_le_two (by
      have := ordinaryCentralizerProjection_range_index_le_two A hsq
      rwa [← hR, Subgroup.index] at this)
  haveI hZsolv : Group.IsSolvable ↥(Subgroup.centralizer ({Matrix.ProjGenLinGroup.mk A} :
      Set (Matrix.ProjGenLinGroup (Fin n) K))) :=
    solvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  let ι : ↥(fixedSubgroup (innerDiagonalAction n K A)) →*
      ↥(Subgroup.centralizer ({Matrix.ProjGenLinGroup.mk A} :
        Set (Matrix.ProjGenLinGroup (Fin n) K))) :=
    (Subgroup.subtype _).comp (innerFixedCentralizerEquiv n K A).toMonoidHom
  exact solvable_of_solvable_injective (f := ι)
    ((Subgroup.subtype_injective _).comp (innerFixedCentralizerEquiv n K A).injective)

theorem factor_cases {t : ℕ} (ht : 1 ≤ t) (hq : Nat.card K = 3 ∨ 9 ≤ Nat.card K)
    (hb : commutator (SpecialLinearGroup (Fin t) K) = ⊤ →
      Nat.card (SpecialLinearGroup (Fin t) K) ≤ 360) :
    t = 1 ∨ (t = 2 ∧ Nat.card K = 3) := by
  have hq3 : 3 ≤ Nat.card K := by omega
  by_cases ht1 : t = 1
  · exact Or.inl ht1
  by_cases ht2 : t = 2
  · subst ht2
    rcases hq with h3 | h9
    · exact Or.inr ⟨rfl, h3⟩
    · exfalso
      haveI := CatalogueBGeneralLinear.specialLinear_perfect 2 K le_rfl (Or.inr (by omega))
        (Or.inr (by omega))
      have h1 := hb Group.IsPerfect.commutator_eq_top
      rw [card_SL_two] at h1
      have h2 : 81 ≤ Nat.card K ^ 2 := by nlinarith
      have h3 : 9 * 80 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := Nat.mul_le_mul h9 (by omega)
      omega
  · exfalso
    have ht3 : 3 ≤ t := by omega
    haveI := CatalogueBGeneralLinear.specialLinear_perfect t K (by omega) (Or.inl (by omega))
      (Or.inl (by omega))
    have h1 := hb Group.IsPerfect.commutator_eq_top
    have h2 := lt_card_SL_of_three_le ht3 hq3
    omega

theorem gl_one_comm {E : Type*} [Field E] (a b : GL (Fin 1) E) : a * b = b * a := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem three_pow_cases {f : ℕ} (hf : 1 ≤ f) : 3 ^ f = 3 ∨ 9 ≤ 3 ^ f := by
  rcases Nat.lt_or_ge f 2 with h | h
  · left
    have : f = 1 := by omega
    subst this
    rfl
  · right
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) h

theorem eq_one_of_three_pow_eq_three {f : ℕ} (h : 3 ^ f = 3) : f = 1 := by
  have : 3 ^ f = 3 ^ 1 := by rw [h]; rfl
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this

theorem a6_psl_inner_split (hO : LieOrderFormulasInput) {f : ℕ}
    (hK : Nat.card K = 3 ^ f) (hf : 1 ≤ f) (hadm : StatedLieAdmissible .PSL n 3 f)
    (hm : LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 3 f) {A : GL (Fin n) K}
    (hsq : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    (hσ : orderOf (innerDiagonalAction n K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction n K A))}
    (hD : A6Hyp (innerDiagonalAction n K A) D) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hrs : r + s = n)
    (e : Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ≃* GL (Fin r) K × GL (Fin s) K)
    (hsc : ∀ c : Kˣ, e (ordinaryCentralizerScalar A c) =
      (GeneralLinearGroup.scalar (Fin r) c, GeneralLinearGroup.scalar (Fin s) c)) :
    n = 4 ∧ f = 1 := by
  have hq : Nat.card K = 3 ∨ 9 ≤ Nat.card K := by rw [hK]; exact three_pow_cases hf
  have hr' := factor_cases hr hq (fun hp => a6_psl_inner_factor hD hs e hsc hp)
  have hs' := factor_cases hs hq (fun hp => a6_psl_inner_factor hD hr
    (e.trans MulEquiv.prodComm) (fun c => by simp [hsc c]) hp)
  rcases hr' with rfl | ⟨rfl, h3⟩ <;> rcases hs' with rfl | ⟨rfl, h3'⟩
  · exfalso
    refine hD.not_solvable (isSolvable_fixed_of_comm (by omega) A hsq fun x y => e.injective ?_)
    rw [map_mul, map_mul]
    exact Prod.ext (gl_one_comm _ _) (gl_one_comm _ _)
  · exfalso
    have hn3 : n = 3 := by omega
    have hf1 : f = 1 := eq_one_of_three_pow_eq_three (hK ▸ h3')
    subst hn3 hf1
    exact hD.false_psl_three_three hO hadm hm
  · exfalso
    have hn3 : n = 3 := by omega
    have hf1 : f = 1 := eq_one_of_three_pow_eq_three (hK ▸ h3)
    subst hn3 hf1
    exact hD.false_psl_three_three hO hadm hm
  · exact ⟨by omega, eq_one_of_three_pow_eq_three (hK ▸ h3)⟩

theorem a6_psl_inner_quad_main {f : ℕ} (hK : Nat.card K = 3 ^ f) (hf : 1 ≤ f)
    {A : GL (Fin n) K} (hsq : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction n K A))}
    (hD : A6Hyp (innerDiagonalAction n K A) D) {E : Type} [Field E] [Finite E] {m : ℕ}
    (hm1 : 1 ≤ m) (hnm : n = 2 * m) (hE : Nat.card E = Nat.card K ^ 2)
    (e : Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ≃* GL (Fin m) E) :
    n = 4 ∧ f = 1 := by
  have hq : Nat.card K = 3 ∨ 9 ≤ Nat.card K := by rw [hK]; exact three_pow_cases hf
  have hE9 : 9 ≤ Nat.card E := by
    rw [hE]
    rcases hq with h | h <;> nlinarith
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · exfalso
    have hm1' : m = 1 := by omega
    subst hm1'
    exact hD.not_solvable (isSolvable_fixed_of_comm (by omega) A hsq fun x y =>
      e.injective (by rw [map_mul, map_mul]; exact gl_one_comm _ _))
  · have hperf : commutator (SpecialLinearGroup (Fin m) E) = ⊤ := by
      haveI := CatalogueBGeneralLinear.specialLinear_perfect m E hge
        (Or.inr (by omega)) (Or.inr (by omega))
      exact Group.IsPerfect.commutator_eq_top
    have hb := a6_psl_inner_quad hD (by omega) e hperf
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · have hm2 : m = 2 := by omega
      subst hm2
      rw [card_SL_two] at hb
      rcases hq with h3 | h9
      · exact ⟨by omega, eq_one_of_three_pow_eq_three (hK ▸ h3)⟩
      · exfalso
        have h1 : 81 ≤ Nat.card E := by rw [hE]; nlinarith
        have h2 : 81 * 6560 ≤ Nat.card E * (Nat.card E ^ 2 - 1) := by
          refine Nat.mul_le_mul h1 ?_
          have : 6561 ≤ Nat.card E ^ 2 := by nlinarith
          omega
        omega
    · exfalso
      have := lt_card_SL_of_three_le hm3 (by omega : 3 ≤ Nat.card E)
      omega

end Inner

end PSLA6

open PSLA6

section Main

open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic in
theorem a6_psl_inner (hO : LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (hadm : StatedLieAdmissible .PSL n 3 f)
    (hm : LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 3 f) (A : GL (Fin n) K)
    (hσ : orderOf (innerDiagonalAction n K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction n K A))}
    (hD : A6Hyp (innerDiagonalAction n K A) D) : n = 4 ∧ f = 1 := by
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hq : Nat.card K = 3 ∨ 9 ≤ Nat.card K := by rw [hK]; exact three_pow_cases hf
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · right
      have hn2 : n = 2 := by omega
      rcases hq with h | h
      · exfalso
        exact hadm.2.2.2.2 (by rw [hn2, hK] at *; simp [h] at *)
      · omega
    · exact Or.inl h3
  have hodd : Odd (Nat.card K) := by rw [hK]; exact Odd.pow (by decide)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero
    (CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd)
  have hne : innerDiagonalAction n K A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hsq2 : innerDiagonalAction n K A ^ 2 = 1 := by
    rw [← hσ, pow_orderOf_eq_one]
  obtain ⟨hmk, hmk2, c, hc⟩ :=
    CatalogueBHigherLinearInner.inner_involution_projective_data n K hn hparameter A hne hsq2
  by_cases hsquare : IsSquare c.val
  · obtain ⟨b, -, hr, hs, hrs, e, -, hsc, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A c h2 hmk hc
        hsquare
    exact a6_psl_inner_split hO hK hf hadm hm hmk2 hσ hD hr hs hrs e hsc
  · letI : Fact (¬ IsSquare c.val) := ⟨hsquare⟩
    haveI : Finite (extension c.val) := Module.finite_of_finite K
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have hEcard : Nat.card (extension c.val) = Nat.card K ^ 2 := by
      let _ : Fintype K := Fintype.ofFinite K
      let _ : Fintype (extension c.val) := Fintype.ofFinite _
      have h := Module.card_eq_pow_finrank (K := K) (V := extension c.val)
      rw [extension_finrank c.val, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
      exact h
    have hdim := matrixDimension_twice A c hc
    have hpos := matrixDimension_pos A c hc
    exact a6_psl_inner_quad_main hK hf hmk2 hD hpos (by simpa using hdim) hEcard
      (matrixCentralizerQuadraticEquiv A c hc)

end Main

end CFSG.ComponentClassification.CatFC
