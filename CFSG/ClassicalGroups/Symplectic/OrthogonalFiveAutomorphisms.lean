module

public import CFSG.ClassicalGroups.Symplectic.OrthogonalFiveModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentation
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLCore

public noncomputable section

open Matrix QuadraticMap
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalFive
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace CFSG.ClassicalGroups.Symplectic
variable {K : Type} [Field K]

private theorem formJ_submatrix_eq_symplecticGram :
    symplecticGram K = (formJ 2 K).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [symplecticGram_eq_neg_JFin,
    show formJ 2 K = -J (Fin 2) K from blueprintGram_eq_neg_J]
  simp only [Matrix.submatrix_neg]
  have hJ : (J (Fin 2) K).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
      TauCeti.JFin 2 K := by
    have h := congrArg (fun M => M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
      (TauCeti.JFin_submatrix (m := 2) (R := K))
    simpa [Matrix.submatrix_submatrix] using h.symm
  change -TauCeti.JFin 2 K =
    -((J (Fin 2) K).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
  rw [hJ]

private theorem reindex_equation_iff (A : GL (Fin 2 ⊕ Fin 2) K) (μ : Kˣ) :
    (((Equiv.reindexGL finSumFinEquiv K A : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)ᵀ *
        symplecticGram K *
        (((Equiv.reindexGL finSumFinEquiv K A : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
        (μ : K) • symplecticGram K ↔
      ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ * formJ 2 K *
        (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (μ : K) • formJ 2 K := by
  let r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K ≃ₗ[K]
      Matrix (Fin 4) (Fin 4) K := Matrix.reindexLinearEquiv K K finSumFinEquiv finSumFinEquiv
  have hrA : r (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((Equiv.reindexGL finSumFinEquiv K A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Equiv.coe_reindexGL]
  have hrJ : r (formJ 2 K) = symplecticGram K := by
    rw [Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply]
    exact formJ_submatrix_eq_symplecticGram.symm
  have htrans : r ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ) =
      (r (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ := by
    rw [Matrix.reindexLinearEquiv_apply, Matrix.reindexLinearEquiv_apply,
      Matrix.reindex_apply, Matrix.reindex_apply]
    exact (Matrix.transpose_reindex finSumFinEquiv finSumFinEquiv
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).symm
  have hmul : r (((A : Matrix _ _ K))ᵀ * formJ 2 K * (A : Matrix _ _ K)) =
      (r (A : Matrix _ _ K))ᵀ * symplecticGram K * r (A : Matrix _ _ K) := by
    rw [← Matrix.reindexLinearEquiv_mul K K finSumFinEquiv finSumFinEquiv finSumFinEquiv
      (((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ * formJ 2 K)
      ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))]
    rw [← Matrix.reindexLinearEquiv_mul K K finSumFinEquiv finSumFinEquiv finSumFinEquiv
      ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ (formJ 2 K)]
    rw [htrans, hrJ]
  constructor
  · intro h
    apply r.injective
    rw [hmul, map_smul, hrJ, hrA]
    exact h
  · intro h
    have h' := congrArg r h
    rw [hmul, map_smul, hrJ, hrA] at h'
    exact h'

theorem reindex_mem_symplecticSimilitudes_iff (A : GL (Fin 2 ⊕ Fin 2) K) :
    Equiv.reindexGL finSumFinEquiv K A ∈ symplecticSimilitudes K ↔ A ∈ gsp 2 K := by
  constructor
  · rintro ⟨μ, hμ⟩
    exact mem_gsp.mpr ⟨μ, (reindex_equation_iff A μ).mp hμ⟩
  · rintro ⟨μ, hμ⟩
    exact ⟨μ, (reindex_equation_iff A μ).mpr hμ⟩

@[expose] noncomputable def gspFourEquivSelfAdjointSimilitudes :
    gsp 2 K ≃* symplecticSimilitudes K := by
  let f : gsp 2 K →* symplecticSimilitudes K :=
    MonoidHom.codRestrict
      ((Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)) K).toMonoidHom.comp
        (gsp 2 K).subtype)
      (symplecticSimilitudes K)
      (fun A => (reindex_mem_symplecticSimilitudes_iff
        (A : GL (Fin 2 ⊕ Fin 2) K)).mpr A.property)
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro A B hAB
    apply Subtype.ext
    apply (Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)) K).injective
    exact congrArg Subtype.val hAB
  · intro B
    let A : GL (Fin 2 ⊕ Fin 2) K :=
      Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)).symm K B
    have hAsymm : Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)).symm K B =
        (Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)) K).symm B := by
      rw [Equiv.reindexGL_symm]
    have hreindex : Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)) K A = B := by
      dsimp [A]
      rw [hAsymm, MulEquiv.apply_symm_apply]
    have hA : A ∈ gsp 2 K :=
      (reindex_mem_symplecticSimilitudes_iff A).mp (hreindex ▸ B.property)
    refine ⟨⟨A, hA⟩, ?_⟩
    apply Subtype.ext
    exact hreindex

theorem gspFourEquivSelfAdjointSimilitudes_val (A : gsp 2 K) :
    ((gspFourEquivSelfAdjointSimilitudes A : symplecticSimilitudes K) : GL (Fin 4) K) =
      Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)) K
        (A : GL (Fin 2 ⊕ Fin 2) K) := rfl

theorem gspFourEquivSelfAdjointSimilitudes_statedSp (y : StatedSp 2 K) :
    gspFourEquivSelfAdjointSimilitudes ⟨y, statedSp_le_gsp y.property⟩ =
      (statedSpEquivSymplecticKernel y : symplecticSimilitudes K) := by
  apply Subtype.ext
  apply Units.ext
  change (((gspFourEquivSelfAdjointSimilitudes ⟨y, statedSp_le_gsp y.property⟩ :
      symplecticSimilitudes K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    (((statedSpEquivSymplecticKernel y :
      (symplecticMultiplier (K := K)).ker) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  rw [gspFourEquivSelfAdjointSimilitudes_val, statedSpEquivSymplecticKernel_val]

noncomputable def gspSelfAdjointAction (h2 : (2 : K) ≠ 0) :
    gsp 2 K →* TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) :=
  (selfAdjointOrthogonalAction h2).comp
    (gspFourEquivSelfAdjointSimilitudes (K := K)).toMonoidHom

theorem gspSelfAdjointAction_ker [Finite K] (h2 : (2 : K) ≠ 0) :
    (conjAut 2 K).ker = (gspSelfAdjointAction h2).ker := by
  ext A
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hA
    have h1 : conjAut 2 K A * fieldAut 2 K (1 : K ≃+* K) = 1 := by
      simpa using hA
    obtain ⟨-, c, hc⟩ :=
      (CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff
        (r := 2) (K := K) (by norm_num) A 1).mp h1
    have hval : gspFourEquivSelfAdjointSimilitudes A = selfAdjointScalarSimilitude c := by
      apply Subtype.ext
      apply Units.ext
      change (((gspFourEquivSelfAdjointSimilitudes A : symplecticSimilitudes K) :
          GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (((selfAdjointScalarSimilitude c : symplecticSimilitudes K) :
          GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      rw [show (((gspFourEquivSelfAdjointSimilitudes A : symplecticSimilitudes K) :
          GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)) K
            (A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 4) (Fin 4) K) from
        congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K))
          (gspFourEquivSelfAdjointSimilitudes_val A)]
      rw [hc, reindexGL_finSumFinEquiv_scalar]
      rfl
    change selfAdjointOrthogonalAction h2 (gspFourEquivSelfAdjointSimilitudes A) = 1
    rw [hval]
    exact selfAdjointOrthogonalAction_scalar h2 c
  · intro hA
    have hA' : selfAdjointOrthogonalAction h2 (gspFourEquivSelfAdjointSimilitudes A) = 1 := hA
    obtain ⟨c, hc⟩ := (selfAdjointOrthogonalAction_eq_one_iff h2 _).mp hA'
    have hcleq : gspFourEquivSelfAdjointSimilitudes A = selfAdjointScalarSimilitude c :=
      Subtype.ext hc
    have hAeq : (A : GL (Fin 2 ⊕ Fin 2) K) =
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
      apply (Equiv.reindexGL (finSumFinEquiv (m := 2) (n := 2)) K).injective
      rw [← gspFourEquivSelfAdjointSimilitudes_val A]
      rw [show ((gspFourEquivSelfAdjointSimilitudes A : symplecticSimilitudes K) :
          GL (Fin 4) K) = (GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) from
        congrArg Subtype.val hcleq]
      rw [reindexGL_finSumFinEquiv_scalar]
    have h1 : conjAut 2 K A * fieldAut 2 K (1 : K ≃+* K) = 1 :=
      (CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff
        (r := 2) (K := K) (by norm_num) A 1).mpr ⟨rfl, c, hAeq⟩
    simpa using h1

theorem gspSelfAdjointAction_range [Finite K] (hodd : Odd (Nat.card K)) :
    (gspSelfAdjointAction (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).range =
      QuadraticMap.specialOrthogonalWithin (selfAdjointForm K) := by
  let h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  rw [← selfAdjointOrthogonalAction_range hodd]
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨gspFourEquivSelfAdjointSimilitudes A, rfl⟩
  · rintro ⟨B, rfl⟩
    obtain ⟨A, rfl⟩ := (gspFourEquivSelfAdjointSimilitudes (K := K)).surjective B
    exact ⟨A, rfl⟩

@[expose] noncomputable def pgspFourEquivSpecialOrthogonal [Finite K]
    (hodd : Odd (Nat.card K)) :
    (conjAut 2 K).range ≃*
      QuadraticMap.specialOrthogonalWithin (selfAdjointForm K) :=
  (QuotientGroup.quotientKerEquivRange (conjAut 2 K)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
        (gspSelfAdjointAction_ker
          (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd))).trans
      ((QuotientGroup.quotientKerEquivRange
          (gspSelfAdjointAction
            (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd))).trans
        (MulEquiv.subgroupCongr (gspSelfAdjointAction_range hodd))))

theorem pgspFourEquivSpecialOrthogonal_conjAut [Finite K] (hodd : Odd (Nat.card K))
    (A : gsp 2 K) :
    (pgspFourEquivSpecialOrthogonal (K := K) hodd ⟨conjAut 2 K A, ⟨A, rfl⟩⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) =
      gspSelfAdjointAction (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) A := by
  have h : (QuotientGroup.quotientKerEquivRange (conjAut 2 K)) (QuotientGroup.mk A) =
      ⟨conjAut 2 K A, ⟨A, rfl⟩⟩ := rfl
  rw [pgspFourEquivSpecialOrthogonal, MulEquiv.trans_apply]
  rw [← h, MulEquiv.symm_apply_apply]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem pgspFourEquivSpecialOrthogonal_conj_proj [Finite K] (hodd : Odd (Nat.card K))
    (y : StatedSp 2 K) :
    (pgspFourEquivSpecialOrthogonal (K := K) hodd
      ⟨MulAut.conj (proj 2 K y),
        ⟨⟨y, statedSp_le_gsp y.property⟩,
          conjAut_statedSp y⟩⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) =
      (pspFourEquivDerivedOrthogonal (K := K) hodd (proj 2 K y) :
        TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) := by
  let A : gsp 2 K := ⟨y, statedSp_le_gsp y.property⟩
  let a : (conjAut 2 K).range := ⟨conjAut 2 K A, ⟨A, rfl⟩⟩
  have h_input : (⟨MulAut.conj (proj 2 K y),
      ⟨A, conjAut_statedSp y⟩⟩ : (conjAut 2 K).range) = a :=
    Subtype.ext (conjAut_statedSp y).symm
  rw [h_input, pgspFourEquivSpecialOrthogonal_conjAut]
  rw [pspFourEquivDerivedOrthogonal_proj]
  rw [gspSelfAdjointAction, MonoidHom.comp_apply]
  dsimp [A]
  rw [gspFourEquivSelfAdjointSimilitudes_statedSp]

theorem conjAut_range_eq_top_of_prime_card [Finite K]
    (hp : (Nat.card K).Prime) (hodd : Odd (Nat.card K)) :
    (conjAut 2 K).range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  intro α
  obtain ⟨A, σ, hα⟩ :=
    CFSG.RankThree.PartTwo.KFacts.psp4_odd_automorphism_normal_form
      (CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd) α
  have hσ : σ = 1 :=
    CFSG.ComponentClassification.Burgoyne.PSL.ringEquiv_eq_one_of_prime_card hp σ
  refine ⟨A, ?_⟩
  rw [hα, hσ, map_one, mul_one]

@[expose] noncomputable def pspFourAutEquivSpecialOrthogonal [Finite K]
    (hp : (Nat.card K).Prime) (hodd : Odd (Nat.card K)) :
    MulAut (StatedProj (StatedSp 2 K)) ≃*
      QuadraticMap.specialOrthogonalWithin (selfAdjointForm K) :=
  ((MulEquiv.subgroupCongr (conjAut_range_eq_top_of_prime_card hp hodd)).trans
    Subgroup.topEquiv).symm.trans (pgspFourEquivSpecialOrthogonal hodd)

theorem pspFourAutEquivSpecialOrthogonal_conj [Finite K]
    (hp : (Nat.card K).Prime) (hodd : Odd (Nat.card K))
    (x : StatedProj (StatedSp 2 K)) :
    (pspFourAutEquivSpecialOrthogonal (K := K) hp hodd (MulAut.conj x) :
        TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) =
      (pspFourEquivDerivedOrthogonal (K := K) hodd x :
        TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) := by
  obtain ⟨y, rfl⟩ := proj_surjective x
  have h_input :
      ((MulEquiv.subgroupCongr (conjAut_range_eq_top_of_prime_card hp hodd)).trans
        Subgroup.topEquiv).symm (MulAut.conj (proj 2 K y)) =
        ⟨MulAut.conj (proj 2 K y),
          ⟨⟨y, statedSp_le_gsp y.property⟩,
            conjAut_statedSp y⟩⟩ :=
    Subtype.ext rfl
  rw [pspFourAutEquivSpecialOrthogonal, MulEquiv.trans_apply, h_input,
    pgspFourEquivSpecialOrthogonal_conj_proj]

end CFSG.ClassicalGroups.Symplectic
