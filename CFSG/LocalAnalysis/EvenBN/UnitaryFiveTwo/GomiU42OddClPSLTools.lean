module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
  (pslRange pslRange_eq_map pglAction innerDiagonalAction)
open CFSG.ComponentClassification.CatalogueBHigherLinearInner (localPSLRange
  fixedPSLCentralizerEquiv innerFixedCentralizerEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  (ordinaryCentralizerProjection ordinaryCentralizerScalar
    ordinaryCentralizerProjection_kernel_eq_scalar ordinaryCentralizerProjection_range_index_le_two)

@[expose] noncomputable def u42DetClass (n : ℕ) (K : Type) [Field K] :
    ProjGenLinGroup (Fin n) K →* Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range :=
  ProjGenLinGroup.lift ((QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range).comp
    GeneralLinearGroup.det) (by
      ext u
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MonoidHom.one_apply,
        QuotientGroup.eq_one_iff]
      refine ⟨u, ?_⟩
      simp [powMonoidHom])

theorem u42DetClass_mk {n : ℕ} {K : Type} [Field K] (g : GL (Fin n) K) :
    u42DetClass n K (ProjGenLinGroup.mk g) =
      (QuotientGroup.mk (GeneralLinearGroup.det g) : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :=
  rfl

theorem u42DetClass_ker (n : ℕ) (K : Type) [Field K] :
    (u42DetClass n K).ker = pslRange n K := by
  ext x
  induction x using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  rw [MonoidHom.mem_ker, u42DetClass_mk, QuotientGroup.eq_one_iff, pslRange_eq_map,
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinearRange_eq_detKernel]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨g * GeneralLinearGroup.scalar (Fin n) u⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, GeneralLinearGroup.det_scalar, ← hu]
      simp [powMonoidHom, Fintype.card_fin]
    · exact (ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨u⁻¹, rfl⟩).symm
  · rintro ⟨y, hy, hyg⟩
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hyg
    refine ⟨u, ?_⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
    have := congrArg GeneralLinearGroup.det hu
    rw [map_mul, hy, GeneralLinearGroup.det_scalar, one_mul] at this
    rw [Fintype.card_fin] at this
    simpa [powMonoidHom] using this

instance u42PGLFinite (n : ℕ) (K : Type) [Field K] [Finite K] : Finite (ProjGenLinGroup (Fin n) K) :=
  Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin n) K → _) ProjGenLinGroup.mk_surjective

theorem u42_psl_index_dvd (n : ℕ) (K : Type) [Field K] [Finite K] :
    (pslRange n K).index ∣ Nat.gcd n (Nat.card K - 1) := by
  set H : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range with hH
  have h1 : (pslRange n K).index = Nat.card (u42DetClass n K).range := by
    rw [← u42DetClass_ker, Subgroup.index_ker]
  have h2 : Nat.card (u42DetClass n K).range ∣ Nat.card (Kˣ ⧸ H) :=
    Subgroup.card_subgroup_dvd_card _
  haveI : IsCyclic (Kˣ ⧸ H) := isCyclic_of_surjective (QuotientGroup.mk' H)
    QuotientGroup.mk_surjective
  have h3 : Nat.card (Kˣ ⧸ H) ∣ n := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ ⧸ H)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    apply orderOf_dvd_of_pow_eq_one
    induction g using QuotientGroup.induction_on with | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨u, rfl⟩
  have h4 : Nat.card (Kˣ ⧸ H) ∣ Nat.card K - 1 := by
    rw [← Subgroup.index_eq_card, ← Nat.card_units]
    exact Subgroup.index_dvd_card H
  rw [h1]
  exact h2.trans (Nat.dvd_gcd h3 h4)

theorem u42_card_centralizer_eq (n : ℕ) (K : Type) [Field K] [Finite K]
    (a : ProjGenLinGroup (Fin n) K) :
    ∃ e : ℕ, e ∣ Nat.gcd n (Nat.card K - 1) ∧
      Nat.card (Subgroup.centralizer ({a} : Set (ProjGenLinGroup (Fin n) K))) =
        Nat.card ↥(fixedSubgroup (pglAction n K a)) * e := by
  refine ⟨(localPSLRange n K a).index, ?_, ?_⟩
  · have h1 : (localPSLRange n K a).index ∣ (pslRange n K).index :=
      Subgroup.relIndex_dvd_index_of_normal (pslRange n K) _
    exact h1.trans (u42_psl_index_dvd n K)
  · rw [Nat.card_congr (fixedPSLCentralizerEquiv n K a).toEquiv]
    exact (Subgroup.card_mul_index (localPSLRange n K a)).symm

theorem u42_ordinaryCentralizerScalar_injective {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    (A : GL (Fin n) K) : Function.Injective (ordinaryCentralizerScalar A) := by
  intro c d h
  have h1 := congrArg (fun B : Subgroup.centralizer ({A} : Set (GL (Fin n) K)) =>
    (B.val : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
  apply Units.ext
  simpa [ordinaryCentralizerScalar] using h1

theorem u42_psl_inner_eq {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (A : GL (Fin n) K) (hsq : ProjGenLinGroup.mk A ^ 2 = 1) :
    ∃ ε e : ℕ, (ε = 1 ∨ ε = 2) ∧ e ∣ Nat.gcd n (Nat.card K - 1) ∧
      Nat.card ↥(fixedSubgroup (innerDiagonalAction n K A)) * e * (Nat.card K - 1) =
        ε * Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨e, he, hG⟩ := u42_card_centralizer_eq n K (ProjGenLinGroup.mk A)
  have hidx := ordinaryCentralizerProjection_range_index_le_two A hsq
  have hidx0 : 0 < (ordinaryCentralizerProjection A).range.index := Nat.pos_of_ne_zero
    Subgroup.index_ne_zero_of_finite
  have hcard1 : Nat.card (Subgroup.centralizer ({ProjGenLinGroup.mk A} :
      Set (ProjGenLinGroup (Fin n) K))) =
      Nat.card (ordinaryCentralizerProjection A).range *
        (ordinaryCentralizerProjection A).range.index :=
    (Subgroup.card_mul_index _).symm
  have hcard2 : Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) =
      Nat.card (ordinaryCentralizerProjection A).range *
        Nat.card (ordinaryCentralizerProjection A).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (ordinaryCentralizerProjection A).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (ordinaryCentralizerProjection A)).toEquiv]
  have hker : Nat.card (ordinaryCentralizerProjection A).ker = Nat.card K - 1 := by
    rw [ordinaryCentralizerProjection_kernel_eq_scalar,
      Nat.card_congr (MonoidHom.ofInjective (u42_ordinaryCentralizerScalar_injective hn A)).toEquiv.symm,
      Nat.card_units]
  refine ⟨(ordinaryCentralizerProjection A).range.index, e, by omega, he, ?_⟩
  rw [hcard2, hker]
  have : Nat.card ↥(fixedSubgroup (innerDiagonalAction n K A)) * e =
      Nat.card (ordinaryCentralizerProjection A).range *
        (ordinaryCentralizerProjection A).range.index := by
    rw [← hcard1, hG]
    rfl
  rw [this]
  ring

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
