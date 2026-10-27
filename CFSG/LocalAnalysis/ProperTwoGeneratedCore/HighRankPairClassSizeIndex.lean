module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairClassSizeUnitary
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.CentralExtension
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryInvolutionIndex
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem relIndex_centralizer_subgroupOf {L A : Subgroup G} (hAL : A ≤ L) {t : G} (htL : t ∈ L) :
    (A.subgroupOf L ⊓ Subgroup.centralizer {(⟨t, htL⟩ : L)}).relIndex (A.subgroupOf L) =
      (A ⊓ Subgroup.centralizer {t}).relIndex A := by
  have hcent : A.subgroupOf L ⊓ Subgroup.centralizer {(⟨t, htL⟩ : L)} =
      (A ⊓ Subgroup.centralizer {t}).subgroupOf L := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxt⟩
      exact ⟨hx, congrArg Subtype.val hxt⟩
    · rintro ⟨hx, hxt⟩
      exact ⟨hx, Subtype.ext hxt⟩
  rw [hcent, Subgroup.relIndex_subgroupOf hAL]

theorem isPGroup_subgroupOf {L A : Subgroup G} (hAL : A ≤ L) {p : ℕ} (hA : IsPGroup p A) :
    IsPGroup p (A.subgroupOf L) :=
  hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm

theorem mem_normalizer_subgroupOf {L A : Subgroup G} {t : G} (htL : t ∈ L)
    (htA : t ∈ Subgroup.normalizer (A : Set G)) :
    (⟨t, htL⟩ : L) ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp htA y

variable [Finite G] {p q : ℕ}

theorem relIndex_centralizer_le_of_mulEquiv_specialLinearGroup {L A : Subgroup G} (hAL : A ≤ L)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (hA : IsPGroup p A) {F : Type*} [Field F]
    [Finite F] (hF : Nat.card F = q ∨ Nat.card F = q ^ 2) (φ : L ≃* SL(2, F)) {t : G}
    (htL : t ∈ L) :
    (A ⊓ Subgroup.centralizer {t}).relIndex A ≤ p ^ (q + 1).factorization p := by
  rw [← relIndex_centralizer_subgroupOf hAL htL]
  let π : L →* SL(2, F) ⧸ signScalars F :=
    (QuotientGroup.mk' (signScalars F)).comp φ.toMonoidHom
  have hker : π.ker ≤ Subgroup.center L := by
    intro x hx
    have h1 : φ x ∈ signScalars F := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨c, -, hc⟩ := h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply φ.injective
    rw [map_mul, map_mul]
    have hmat : ((φ y * φ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((φ x * φ y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc]
      exact ((scalar_commute (c : F) (fun r => Commute.all _ r) _).eq).symm
    exact Subtype.ext hmat
  exact relIndex_centralizer_le_of_mulEquiv_linear hp hp2 hpq π hker F hF (MulEquiv.refl _)
    (A.subgroupOf L) (isPGroup_subgroupOf hAL hA) ⟨t, htL⟩

theorem center_specialLinearGroup_eq_signScalars (K : Type*) [Field K] :
    Subgroup.center (SL(2, K)) = signScalars K := by
  ext A
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hrA⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    refine ⟨Units.mk0 r hr0, by ext; simpa using hr, ?_⟩
    rw [← hrA]
    rfl
  · rintro ⟨c, hc, hcA⟩
    refine ⟨c, by simpa using congrArg Units.val hc, hcA.symm⟩


theorem relIndex_centralizer_le_of_quotient_psl2 {L A : Subgroup G} (hAL : A ≤ L)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (hA : IsPGroup p A) (N : Subgroup L)
    [N.Normal] (hN : N ≤ Subgroup.center L) {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = q) (E : L ⧸ N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) {t : G}
    (htL : t ∈ L) :
    (A ⊓ Subgroup.centralizer {t}).relIndex A ≤ p ^ (q + 1).factorization p := by
  rw [← relIndex_centralizer_subgroupOf hAL htL]
  have hker : (QuotientGroup.mk' N).ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact hN
  exact relIndex_centralizer_le_of_mulEquiv_linear hp hp2 hpq (QuotientGroup.mk' N) hker K
    (Or.inl hK)
    (E.trans (QuotientGroup.quotientMulEquivOfEq (center_specialLinearGroup_eq_signScalars K)))
    (A.subgroupOf L) (isPGroup_subgroupOf hAL hA) ⟨t, htL⟩

theorem relIndex_centralizer_le_of_quotient_unitary {L A : Subgroup G} (hAL : A ≤ L)
    (hq : IsPrimePow q) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (hA : IsPGroup p A)
    (N : Subgroup L) [N.Normal] (hN : N ≤ Subgroup.center L) (hNodd : Odd (Nat.card N))
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K) (hK : Nat.card K = q ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = q)
    (E : L ⧸ N ≃* ProjectiveSpecialUnitaryMatrixGroup J) {t : G} (htL : t ∈ L) (ht : t ^ 2 = 1)
    (htA : t ∈ Subgroup.normalizer (A : Set G)) :
    (A ⊓ Subgroup.centralizer {t}).relIndex A ≤ 3 * p ^ (q + 1).factorization p := by
  rw [← relIndex_centralizer_subgroupOf hAL htL]
  have hσ : ∀ c, J.conj.toRingHom c = c ^ q :=
    CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hK hfix
  have hker : (QuotientGroup.mk' N).ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have hodd : Odd (Nat.card (QuotientGroup.mk' N).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hNodd
  have ht' : (⟨t, htL⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using ht)
  exact (relIndex_centralizer_le_of_mulEquiv_unitary hq hp hp2 hpq (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hker hodd hK hσ (hermitianSesquilinear_nondegenerate J)
    (E.trans (projectiveSpecialUnitaryMulEquiv J)) (A.subgroupOf L)
    (isPGroup_subgroupOf hAL hA) ⟨t, htL⟩ ht' (mem_normalizer_subgroupOf htL htA)).1

theorem not_dvd_card_suzukiMatrixGroup (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m)
    (hpq : p ∣ 2 ^ (2 * m + 1) + 1) : ¬ p ∣ Nat.card (SuzukiMatrixGroup m) := by
  let K := CFSG.BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := fun x => iterateFrobeniusEquiv_def K 2 (m + 1) x
  obtain ⟨-, -, -, -, -, -, hcard, -⟩ :=
    CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_3 m (by omega) pi hpi
  rw [hcard]
  set q := 2 ^ (2 * m + 1) with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hnq : ¬ p ∣ q := fun h => hp2' (hp.dvd_of_dvd_pow h)
  have hnq1 : ¬ p ∣ q - 1 := by
    intro h
    apply hp2'
    have h2 : q + 1 = (q - 1) + 2 := by omega
    rw [h2] at hpq
    exact (Nat.dvd_add_right h).mp hpq
  have hnq2 : ¬ p ∣ q ^ 2 + 1 := by
    intro h
    apply hp2'
    have h2 : q ^ 2 + 1 = (q + 1) * (q - 1) + 2 := by
      zify [hq1]
      ring
    rw [h2] at h
    exact (Nat.dvd_add_right (Dvd.dvd.mul_right hpq _)).mp h
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hnq2 h
    · exact hnq (hp.dvd_of_dvd_pow h)
  · exact hnq1 h

theorem relIndex_centralizer_eq_one_of_quotient_suzuki {L A : Subgroup G} (hAL : A ≤ L)
    (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m) (hpq : p ∣ 2 ^ (2 * m + 1) + 1)
    (hA : IsPGroup p A) (N : Subgroup L) [N.Normal] (hN : N ≤ Subgroup.center L)
    (E : L ⧸ N ≃* SuzukiMatrixGroup m) {t : G} (htL : t ∈ L) :
    (A ⊓ Subgroup.centralizer {t}).relIndex A = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← relIndex_centralizer_subgroupOf hAL htL]
  have hker : (QuotientGroup.mk' N).ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have hle := relIndex_centralizer_le_card_map (QuotientGroup.mk' N) hker (A.subgroupOf L)
    ⟨t, htL⟩
  have hP : IsPGroup p ((A.subgroupOf L).map (QuotientGroup.mk' N)) :=
    (isPGroup_subgroupOf hAL hA).map _
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  have hdvd : p ^ j ∣ Nat.card (SuzukiMatrixGroup m) := by
    rw [← hj, ← Nat.card_congr E.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hj0 : j = 0 := by
    by_contra hj0
    exact not_dvd_card_suzukiMatrixGroup hp hp2 hm hpq ((dvd_pow_self p hj0).trans hdvd)
  rw [hj, hj0, pow_zero] at hle
  have hpos : (A.subgroupOf L ⊓ Subgroup.centralizer {(⟨t, htL⟩ : L)}).relIndex
      (A.subgroupOf L) ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  omega

end CFSG.ProperTwoGeneratedCore.HighRankPair
