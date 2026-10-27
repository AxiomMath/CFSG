module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaLow
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Klein
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.Assembly.LowTwoRank
open CFSG.Adapters.RankTwoModelTransports
  (glCongr glCongr_statedSU glCongr_statedScalars statedProjCongr)
open CFSG.ComponentClassification.CatFC (omega_five_model)
open CFSG.ComponentClassification.HarrisLit.T1.P54.Klein
  (isQuasisimple_commutator_orthogonalSix lieModel_of_orthogonalSix_cover
    mem_center_of_forall_commutator_mem_center)

theorem glaPPrimeCore_le_center_of_dvd_card {J : Type*} [Group J] [Finite J] {p : ℕ}
    (hp : p.Prime) (hq : CFSG.Open.IsQuasisimple J) (hdvd : p ∣ Nat.card J) :
    GLAPPrimeCore p J ≤ Subgroup.center J := by
  by_cases htop : GLAPPrimeCore p J = ⊤
  · exfalso
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p J)) := CFSG.coprime_card_pPrimeCore p J
    rw [htop, Subgroup.card_top] at hcop
    exact (hp.coprime_iff_not_dvd.1 hcop) hdvd
  · exact le_center_of_normal_of_isQuasisimple hq inferInstance htop

theorem ker_chevQuotHom_eq_center_of_dvd_card {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {J : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥J) (hdvd : p ∣ Nat.card J) :
    (chevQuotHom p J).ker = Subgroup.center ↥J := by
  have hN := glaPPrimeCore_le_center_of_dvd_card hp hq hdvd
  haveI : Group.IsPerfect ↥J := ⟨hq.1⟩
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxc : (pQuotHom p J x : PQuot p J) ∈ Subgroup.center (PQuot p J) :=
      (QuotientGroup.eq_one_iff _).1 hx
    refine mem_center_of_forall_commutator_mem_center fun g => hN ?_
    rw [← ker_pQuotHom, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 hxc (pQuotHom p J g)).symm
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hc : (pQuotHom p J z : PQuot p J) ∈ Subgroup.center (PQuot p J) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := pQuotHom_surjective p J y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz l]
    exact (QuotientGroup.eq_one_iff _).2 hc

noncomputable def centerQuotEquivPSimple_of_dvd_card {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {J : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥J) (hdvd : p ∣ Nat.card J) :
    ↥J ⧸ Subgroup.center ↥J ≃* PSimple p J :=
  (QuotientGroup.quotientMulEquivOfEq
    (ker_chevQuotHom_eq_center_of_dvd_card hp hq hdvd).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (chevQuotHom p J) (chevQuotHom_surjective p J))

private theorem card_ne_two {Q : PrimePower} (hQ2 : Q.p ≠ 2) : Q.card ≠ 2 := by
  intro h
  apply hQ2
  have hd : Q.p ∣ 2 := h ▸ dvd_pow_self Q.p Q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq Q.prime_p Nat.prime_two).1 hd

private theorem valid_B2 {Q : PrimePower} (h2 : Q.card ≠ 2) (h3 : Q.card ≠ 3) :
    (LieTypeIndex.B 2 Q).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [true_and, le_refl]
  exact ⟨h2, h3⟩

private theorem valid_A3 {Q : PrimePower} (h2 : Q.card ≠ 2) : (LieTypeIndex.A 3 Q).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [Nat.reduceEqDiff, OfNat.ofNat_ne_one, IsEmpty.forall_iff, and_true, false_and,
    or_false, h2, not_false_eq_true, and_self, true_and, le_refl]
  omega

private theorem valid_twistedA3 (Q : PrimePower) : (LieTypeIndex.twistedA 3 Q).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp

theorem catalogIs_B2_of_lieModel {X : Type} [Group X] (Q : PrimePower) (hQ2 : Q.p ≠ 2)
    (h3 : Q.card ≠ 3) (h : CFSG.Blueprint.LieModel X .PSp 2 Q.p Q.exponent) :
    catalogIs X (onLie fun d => d = .B 2 Q) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  have hv := valid_B2 (card_ne_two hQ2) h3
  let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩)
  have _ : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card K = Nat.card Fd := by
    rw [hK, ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder]
  let φ : K ≃+* Fd := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 2 ⊕ Fin 2) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2) (glCongr_statedScalars φ)
  let eT := CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj Q hv
  exact ⟨.lie ⟨.B 2 Q, hv⟩, rfl, ⟨(θ.trans e1).trans eT.symm⟩⟩

theorem catalogIs_A3_of_lieModel {X : Type} [Group X] (Q : PrimePower) (hQ2 : Q.p ≠ 2)
    (h : CFSG.Blueprint.LieModel X .PSL 4 Q.p Q.exponent) :
    catalogIs X (onLie fun d => d = .A 3 Q) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hv := valid_A3 (card_ne_two hQ2)
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 4 Q.p Q.exponent
    Q.exponent_pos hK
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 Q hv
  exact ⟨.lie ⟨.A 3 Q, hv⟩, rfl, ⟨(θ.trans eK).trans eC.symm⟩⟩

theorem catalogIs_twistedA3_of_lieModel {X : Type} [Group X] (Q : PrimePower)
    (h : CFSG.Blueprint.LieModel X .PSU 4 Q.p Q.exponent) :
    catalogIs X (onLie fun d => d = .twistedA 3 Q) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hv := valid_twistedA3 Q
  have hcard : Nat.card K = Nat.card (GaloisField Q.p (2 * Q.exponent)) := by
    rw [hK, GaloisField.card Q.p (2 * Q.exponent) (by have := Q.exponent_pos; omega), ← pow_mul,
      mul_comm]
  let φ : K ≃+* GaloisField Q.p (2 * Q.exponent) :=
    CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 4) φ)
    (glCongr_statedSU φ 4 (Q.p ^ Q.exponent)) (glCongr_statedScalars φ)
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 Q hv
  exact ⟨.lie ⟨.twistedA 3 Q, hv⟩, rfl, ⟨(θ.trans e1).trans eT.symm⟩⟩

private theorem ker_le_center {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    e.toMonoidHom.ker ≤ Subgroup.center A := by
  rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
  exact bot_le

private theorem open_isQuasisimple {J : Type*} [Group J] (h : CFSG.IsQuasisimple J) :
    CFSG.Open.IsQuasisimple J :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem card_ne_three_of_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : PrimePower}
    (h : p ∣ Q.card ^ 2 - 1) : Q.card ≠ 3 := by
  intro h3
  rw [h3] at h
  have h8 : p ∣ 2 ^ 3 := by simpa using h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h8))

theorem isOmegaType_of_mulEquiv_five {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (J : Subgroup G) (Q : TauCeti.PrimePower) (hQ2 : Q.p ≠ 2) (_hpQ : p ≠ Q.p)
    (hQ3 : Q.card ≠ 3) {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hK : Nat.card K = Q.card) (Q₀ : QuadraticForm K W)
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 5)
    (e : ↥J ≃* ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)))
    (hpJ : p ∣ Nat.card J) : IsOmegaType p Q.p J := by
  obtain ⟨hq, -, hlie⟩ := omega_five_model Q.prime_p hQ2 Q.exponent_pos hK Q₀ hQ₀ hdim
  have hqJ : CFSG.Open.IsQuasisimple ↥J := open_isQuasisimple (CFSG.IsQuasisimple.of_mulEquiv e hq)
  have hlieJ : CFSG.Blueprint.LieModel (PSimple p J) .PSp 2 Q.p Q.exponent :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      ((QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).trans
        (centerQuotEquivPSimple_of_dvd_card hp hqJ hpJ)) hlie
  exact ⟨Q, rfl, Or.inl (catalogIs_B2_of_lieModel Q hQ2 hQ3 hlieJ)⟩

theorem isOmegaType_of_mulEquiv_six {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (J : Subgroup G) (Q : TauCeti.PrimePower) (hQ2 : Q.p ≠ 2) (_hpQ : p ≠ Q.p)
    {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hK : Nat.card K = Q.card) (Q₀ : QuadraticForm K W)
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 6)
    (e : ↥J ≃* ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)))
    (hpJ : p ∣ Nat.card J) : IsOmegaType p Q.p J := by
  have hodd : Odd (Nat.card K) := by
    rw [hK, PrimePower.card_def]
    exact (Q.prime_p.odd_of_ne_two hQ2).pow
  have hq := isQuasisimple_commutator_orthogonalSix hodd Q₀ hQ₀ hdim
  have hqJ : CFSG.IsQuasisimple ↥J := CFSG.IsQuasisimple.of_mulEquiv e hq
  obtain ⟨hlin, huni⟩ := lieModel_of_orthogonalSix_cover Q.prime_p hQ2 Q.exponent_pos hK Q₀ hQ₀
    hdim hqJ e.toMonoidHom e.surjective (ker_le_center e)
  have hiso := centerQuotEquivPSimple_of_dvd_card hp (open_isQuasisimple hqJ) hpJ
  refine ⟨Q, rfl, ?_⟩
  by_cases hT : ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q₀ x = 0
  · exact Or.inr (Or.inl (catalogIs_A3_of_lieModel Q hQ2
      (CFSG.Blueprint.LieModel.of_mulEquiv hiso (hlin hT))))
  · exact Or.inr (Or.inr (catalogIs_twistedA3_of_lieModel Q
      (CFSG.Blueprint.LieModel.of_mulEquiv hiso (huni hT))))

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
