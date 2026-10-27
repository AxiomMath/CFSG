module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
public import CFSG.Open.StatedAPI
import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
import CFSG.StronglyEmbedded.BenderBinaryHermitian
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_4
import Mathlib.Tactic.NoncommRing
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.RankTwoShapes

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

noncomputable section

export CFSG.Open.StatedAPI (statedScalars_eq_center)

theorem statedScalars_subgroupOf_eq_ker {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) :
    (CFSG.Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H =
      (ProjGenLinGroup.mk.comp H.subtype).ker :=
  (CFSG.Open.StatedAPI.ker_mk_comp_subtype H).symm

def statedProjEquivMap {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) :
    CFSG.Assembly.LowTwoRank.StatedProj H ≃* H.map (ProjGenLinGroup.mk : GL ι K →* _) :=
  (CFSG.Open.StatedAPI.mapMkEquivStatedProj H).symm

theorem exists_quadraticFrobenius (K : Type) [Field K] [Finite K] (f : ℕ) (hf : f ≠ 0)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ σ : K ≃+* K, (∀ x, σ x = x ^ 2 ^ f) ∧ Function.Involutive σ ∧
      Nat.card {x : K // σ x = x} = 2 ^ f := by
  classical
  let k := GaloisField 2 f
  let E := FiniteField.Extension k 2 2
  let c : E ≃+* E := (FiniteField.Extension.frob k 2 2).toRingEquiv
  have hk : Nat.card k = 2 ^ f := GaloisField.card 2 f hf
  have hE : Nat.card E = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, hk]
  let : Fintype K := Fintype.ofFinite K
  let : Fintype E := Fintype.ofFinite E
  let e : K ≃+* E := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hE])
  have hc (y : E) : c y = y ^ 2 ^ f := by
    change (FiniteField.Extension.frob k 2 2) y = y ^ 2 ^ f
    rw [FiniteField.Extension.frob_apply, hk]
  let σ : K ≃+* K := (e.trans c).trans e.symm
  have hσ (x : K) : σ x = x ^ 2 ^ f := by
    change e.symm (c (e x)) = x ^ 2 ^ f
    rw [hc, ← map_pow, RingEquiv.symm_apply_apply]
  refine ⟨σ, hσ, ?_, ?_⟩
  · intro x
    rw [hσ, hσ, ← pow_mul, ← pow_two, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  · rw [← quadraticBinaryFrobenius_fixed_card f (Nat.pos_of_ne_zero hf)]
    apply Nat.card_congr
    refine e.toEquiv.subtypeEquiv ?_
    intro x
    change σ x = x ↔ c (e x) = e x
    rw [hσ, hc, ← map_pow]
    exact e.injective.eq_iff.symm

@[expose] def identityHermitianForm {K : Type} [Field K] (σ : K ≃+* K)
    (hσ : Function.Involutive σ) : HermitianForm 3 K where
  conj := σ
  conj_involutive := hσ
  form := 1
  form_hermitian i j := by
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  form_nondegenerate := by simp

@[expose] def antidiagonalHermitianForm {K : Type} [Field K] (σ : K ≃+* K)
    (hσ : Function.Involutive σ) : HermitianForm 3 K where
  conj := σ
  conj_involutive := hσ
  form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by simp [Matrix.det_fin_three]

theorem statedSU_eq_specialSubgroup {K : Type} [Field K] (q : ℕ) (σ : K ≃+* K)
    (hσ : Function.Involutive σ) (hσq : ∀ x, σ x = x ^ q) :
    CFSG.Assembly.LowTwoRank.StatedSU 3 q K = (identityHermitianForm σ hσ).specialSubgroup := by
  rw [CFSG.Assembly.LowTwoRank.StatedSU,
    ← Subgroup.closure_eq (identityHermitianForm σ hσ).specialSubgroup]
  congr 1
  ext A
  rw [Set.mem_ofPred_eq, SetLike.mem_coe, HermitianForm.mem_specialSubgroup_iff]
  have hadj : (identityHermitianForm σ hσ).conjTranspose (A : Matrix (Fin 3) (Fin 3) K) =
      ((A : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ := by
    ext i j
    simp [HermitianForm.conjTranspose, identityHermitianForm, hσq]
  rw [hadj, and_comm, Units.ext_iff]
  change _ ↔ _ * 1 * _ = 1 ∧ _
  rw [Matrix.mul_one]
  simp

theorem nonempty_projectiveSpecialUnitary_equiv_of_gram {K : Type} [Field K] {n : ℕ}
    (J J₀ : HermitianForm n K) (P : GL (Fin n) K) (hconj : J₀.conj = J.conj)
    (hgram : J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
      (P : Matrix (Fin n) (Fin n) K) = J₀.form) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* ProjectiveSpecialUnitaryMatrixGroup J₀) := by
  classical
  let eGL : GL (Fin n) K ≃* GL (Fin n) K := MulAut.conj P⁻¹
  let ePGL : Matrix.ProjGenLinGroup (Fin n) K ≃* Matrix.ProjGenLinGroup (Fin n) K :=
    MulAut.conj (Matrix.ProjGenLinGroup.mk P⁻¹)
  have hadj_mul (A B : Matrix (Fin n) (Fin n) K) :
      J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
    ext i j
    simp only [HermitianForm.conjTranspose, Matrix.mul_apply, map_sum, map_mul]
    apply Finset.sum_bij (fun k _ => k) <;> simp [mul_comm]
  have hadj_one : J.conjTranspose (1 : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [HermitianForm.conjTranspose]
    · have hji : j ≠ i := fun hji => hij hji.symm
      simp [HermitianForm.conjTranspose, hij, hji]
  have hP_inv_mul : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 :=
    congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) (inv_mul_cancel P)
  have hP_mul_inv : (P : Matrix (Fin n) (Fin n) K) *
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) (mul_inv_cancel P)
  have hadj_inv_mul : J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      J.conjTranspose (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← hadj_mul, hP_mul_inv, hadj_one]
  have hadj_mul_inv : J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
      J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← hadj_mul, hP_inv_mul, hadj_one]
  have hgram_inv : J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      J₀.form * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = J.form := by
    calc J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * J₀.form *
          ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
            (P : Matrix (Fin n) (Fin n) K)) *
          ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hgram]
      _ = (J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            J.conjTranspose (P : Matrix (Fin n) (Fin n) K)) * J.form *
          ((P : Matrix (Fin n) (Fin n) K) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
      _ = J.form := by rw [hadj_inv_mul, hP_mul_inv]; simp
  have hJ₀adj (A : Matrix (Fin n) (Fin n) K) : J₀.conjTranspose A = J.conjTranspose A := by
    ext i j
    simp [HermitianForm.conjTranspose, hconj]
  have hforward (A : GL (Fin n) K) (hA : A ∈ J.specialSubgroup) :
      P⁻¹ * A * P ∈ J₀.specialSubgroup := by
    rw [J₀.mem_specialSubgroup_iff]
    constructor
    · have hAunit := (J.mem_specialSubgroup_iff A).mp hA |>.1
      change J₀.conjTranspose (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K)) * J₀.form *
          (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K)) = J₀.form
      rw [hJ₀adj, hadj_mul, hadj_mul]
      calc J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            J₀.form * (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (A : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K)) =
          J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
              (P : Matrix (Fin n) (Fin n) K)) *
            (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (A : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K)) := by
            rw [hgram]
        _ = J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
              J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose (P : Matrix (Fin n) (Fin n) K)) * J.form *
              ((P : Matrix (Fin n) (Fin n) K) *
                ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              (A : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K) := by
            noncomm_ring
        _ = J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) * J.form *
                (A : Matrix (Fin n) (Fin n) K)) * (P : Matrix (Fin n) (Fin n) K) := by
            rw [hadj_inv_mul, hP_mul_inv]
            simp only [mul_one]
            noncomm_ring
        _ = J₀.form := by rw [hAunit, hgram]
    · have hAdet := (J.mem_specialSubgroup_iff A).mp hA |>.2
      change Matrix.GeneralLinearGroup.det (P⁻¹ * A * P) = 1
      simp [hAdet]
  have hbackward (A : GL (Fin n) K) (hA : A ∈ J₀.specialSubgroup) :
      P * A * P⁻¹ ∈ J.specialSubgroup := by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · have hAunit := (J₀.mem_specialSubgroup_iff A).mp hA |>.1
      rw [hJ₀adj] at hAunit
      change J.conjTranspose ((P : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * J.form *
          ((P : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = J.form
      rw [hadj_mul, hadj_mul]
      calc J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose (P : Matrix (Fin n) (Fin n) K)) * J.form *
            ((P : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) *
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
          J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose (P : Matrix (Fin n) (Fin n) K)) *
            (J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * J₀.form *
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((P : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) *
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            rw [hgram_inv]
        _ = J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              J₀.form * (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
                (P : Matrix (Fin n) (Fin n) K)) * (A : Matrix (Fin n) (Fin n) K) *
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            noncomm_ring
        _ = J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) * J₀.form *
              (A : Matrix (Fin n) (Fin n) K)) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            rw [hadj_mul_inv, hP_inv_mul]
            simp only [mul_one]
            noncomm_ring
        _ = J.form := by rw [hAunit, hgram_inv]
    · have hAdet := (J₀.mem_specialSubgroup_iff A).mp hA |>.2
      change Matrix.GeneralLinearGroup.det (P * A * P⁻¹) = 1
      simp [hAdet]
  have hspecial : J.specialSubgroup.map eGL.toMonoidHom = J₀.specialSubgroup := by
    ext A
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hA
      have := hforward (eGL.symm A) hA
      have heq : P⁻¹ * eGL.symm A * P = A := by
        change eGL (eGL.symm A) = A
        exact eGL.apply_symm_apply A
      rw [← heq]
      exact this
    · intro hA
      simpa [eGL, Matrix.mul_assoc] using hbackward A hA
  have hcomp : ePGL.toMonoidHom.comp Matrix.ProjGenLinGroup.mk =
      Matrix.ProjGenLinGroup.mk.comp eGL.toMonoidHom := by
    ext A
    simp [ePGL, eGL]
  have hprojective : (J.specialSubgroup.map Matrix.ProjGenLinGroup.mk).map ePGL.toMonoidHom =
      J₀.specialSubgroup.map Matrix.ProjGenLinGroup.mk := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hspecial]
  exact ⟨(ePGL.subgroupMap (J.specialSubgroup.map Matrix.ProjGenLinGroup.mk)).trans
    (MulEquiv.subgroupCongr hprojective)⟩

theorem nonempty_statedProj_statedSU_equiv_PSU3Model (K : Type) [Field K] [Finite K] (f : ℕ)
    (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nonempty (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K) ≃* PSU3Model f) := by
  obtain ⟨σ, hσ, hinv, hfix⟩ := exists_quadraticFrobenius K f (by omega) hK
  obtain ⟨P, hP⟩ := External.huppert_II_10_4_b_standard_hermitian_basis
    (identityHermitianForm σ hinv) (2 ^ f) hK hfix
  obtain ⟨e₂⟩ := nonempty_projectiveSpecialUnitary_equiv_of_gram (identityHermitianForm σ hinv)
    (antidiagonalHermitianForm σ hinv) P rfl hP
  obtain ⟨e₃⟩ := projectiveSpecialUnitary_equiv_PSU3Model (antidiagonalHermitianForm σ hinv) f hf
    rfl hK hfix
  refine ⟨(statedProjEquivMap _).trans ((MulEquiv.subgroupCongr ?_).trans (e₂.trans e₃))⟩
  rw [statedSU_eq_specialSubgroup (2 ^ f) σ hinv hσ]

theorem statedLieAdmissible_PSU_three_two (f : ℕ) (hf : 2 ≤ f) :
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 2 f := by
  refine ⟨Nat.prime_two, by omega, le_rfl, ?_⟩
  intro h
  have h2 : 2 ^ f = 2 ^ 1 := by
    simpa using congrArg Prod.snd h
  have := Nat.pow_right_injective le_rfl h2
  omega

theorem statedClassicalModel_PSU_three_two_iff (G : Type) [Group G] (f : ℕ) (hf : 2 ≤ f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 f ↔
      Nonempty (G ≃* CFSG.Theory.Comparator.PSU3Model f) := by
  constructor
  · rintro ⟨-, K, _, _, hK, ⟨e⟩⟩
    obtain ⟨e'⟩ := nonempty_statedProj_statedSU_equiv_PSU3Model K f hf hK
    exact ⟨e.trans e'⟩
  · rintro ⟨e⟩
    have hcard : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
      rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
    obtain ⟨e'⟩ := nonempty_statedProj_statedSU_equiv_PSU3Model (GaloisField 2 (2 * f)) f hf hcard
    exact ⟨statedLieAdmissible_PSU_three_two f hf, GaloisField 2 (2 * f), inferInstance,
      inferInstance, hcard, ⟨e.trans e'.symm⟩⟩

theorem open_statedClassicalModel_PSU_iff (G : Type) [Group G] (n p f : ℕ) :
    CFSG.Open.StatedClassicalModel G .PSU n p f ↔
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU n p f :=
  Iff.rfl

theorem open_statedClassicalModel_PSU_three_two_iff (G : Type) [Group G] (f : ℕ) (hf : 2 ≤ f) :
    CFSG.Open.StatedClassicalModel G .PSU 3 2 f ↔
      Nonempty (G ≃* CFSG.Theory.Comparator.PSU3Model f) :=
  (open_statedClassicalModel_PSU_iff G 3 2 f).trans (statedClassicalModel_PSU_three_two_iff G f hf)

end

end CFSG.RankTwoShapes
