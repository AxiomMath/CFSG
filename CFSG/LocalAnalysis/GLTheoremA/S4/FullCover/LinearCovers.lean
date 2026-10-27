module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.FibreProduct
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.Defs
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Open.StatedCenterThree
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.SUSixCenter
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FullCover

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA

@[expose] def centralProj {Q S : Type} [Group Q] [Group S] (e : Q ⧸ Subgroup.center Q ≃* S) :
    Q →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))

theorem centralProj_surjective {Q S : Type} [Group Q] [Group S]
    (e : Q ⧸ Subgroup.center Q ≃* S) : Function.Surjective (centralProj e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem centralProj_ker {Q S : Type} [Group Q] [Group S] (e : Q ⧸ Subgroup.center Q ≃* S) :
    (centralProj e).ker = Subgroup.center Q := by
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
  rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem exists_mulEquiv_of_listed {i : TauCeti.CFSGIndex} (hM : ListedMultiplierBound 3)
    (hi : k2 3 i ∨ k3 3 i) {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (hQ : CFSG.Open.IsQuasisimple Q) (hQ' : CFSG.Open.IsQuasisimple Q')
    (e : Q ⧸ Subgroup.center Q ≃* i.Group) (e' : Q' ⧸ Subgroup.center Q' ≃* i.Group)
    (hZ : Nat.card (Subgroup.center Q) = 3) (hZ' : Nat.card (Subgroup.center Q') = 3) :
    Nonempty (Q ≃* Q') := by
  obtain ⟨f, -⟩ := exists_mulEquiv_of_centre_prime (π₁ := centralProj e) (π₂ := centralProj e') hQ
    hQ' (centralProj_surjective e) (centralProj_surjective e') (centralProj_ker e)
    (centralProj_ker e') hZ hZ' (fun D _ _ hD ρ hρ hρk hpD => by
      by_cases hbot : Subgroup.center D = ⊥
      · rw [hbot, Subgroup.card_bot]
        norm_num
      · exact (hM i hi D hD ρ hρ hρk hpD hbot).2.1.le)
  exact ⟨f⟩

theorem three_dvd_two_pow_sub_one_of_even {n : ℕ} (h : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := h
  have h1 : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
  have h2 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [h1]
  omega

theorem three_dvd_two_pow_add_one_of_odd {n : ℕ} (h : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨m, rfl⟩ := h
  have h1 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by rw [pow_succ, pow_mul]; norm_num; ring
  have h2 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [h1]
  omega

theorem isQuasisimple_open_of_foundations {G : Type} [Group G] (h : CFSG.IsQuasisimple G) :
    CFSG.Open.IsQuasisimple G :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem isQuasisimple_of_mulEquiv_open {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple H := by
  refine ⟨?_, ?_⟩
  · have h : (commutator G).map e.toMonoidHom = commutator H := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
        ← commutator_def]
    rw [← h, hG.1, Subgroup.map_top_of_surjective _ e.surjective]
  · haveI := hG.2
    exact (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.isSimpleGroup

section SL

open TauCeti

theorem isQuasisimple_statedSL_three {K : Type} [Field K] :
    CFSG.Open.IsQuasisimple (StatedSL 3 K) := by
  have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect
    (K := K) (n := 3) le_rfl
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3)
    (by norm_num) (Or.inl le_rfl)
  have hq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) K) :=
    ⟨hperf.commutator_eq_top, hsimple⟩
  exact isQuasisimple_of_mulEquiv_open
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K) hq

noncomputable def statedSLThreeEquivCatalog (q : PrimePower) [Fact q.p.Prime]
    (hv : (LieTypeIndex.A 2 q).Valid) :
    StatedSL 3 (GaloisField q.p q.exponent) ⧸
        Subgroup.center (StatedSL 3 (GaloisField q.p q.exponent)) ≃*
      (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩).Group :=
  let e₁ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
    (GaloisField q.p q.exponent)).symm
  (QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm

theorem fullLinearCover_false_of_cover (hM : ListedMultiplierBound 3) (q : PrimePower)
    (hv : (LieTypeIndex.A 2 q).Valid)
    (hi : k2 3 (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩) ∨
      k3 3 (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩))
    (h3 : 3 ∣ q.card - 1) {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (e : Q ⧸ Subgroup.center Q ≃* (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩).Group)
    (hZ : Nat.card (Subgroup.center Q) = 3) :
    FullLinearCover false 3 q.card Q := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have h3' : 3 ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by rwa [hK]
  obtain ⟨f⟩ := exists_mulEquiv_of_listed hM hi hQ
    (isQuasisimple_statedSL_three (K := GaloisField q.p q.exponent)) e
    (statedSLThreeEquivCatalog q hv) hZ
    (CFSG.Open.StatedCenterThree.card_center_statedSL_three h3')
  exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hK, ⟨f⟩⟩

end SL

section SU

open TauCeti

theorem three_le_card_of_valid_twistedA_two {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) : 3 ≤ q.card :=
  (((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).2 rfl)

theorem card_galoisField_two_mul_exponent (q : PrimePower) [Fact q.p.Prime] :
    Nat.card (GaloisField q.p (2 * q.exponent)) = (q.p ^ q.exponent) ^ 2 := by
  rw [GaloisField.card _ _ (by have := q.exponent_pos; omega), ← pow_mul, mul_comm]

theorem isQuasisimple_statedSU_three (q : PrimePower) [Fact q.p.Prime]
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    CFSG.Open.IsQuasisimple (StatedSU 3 (q.p ^ q.exponent) (GaloisField q.p (2 * q.exponent))) ∧
      Subgroup.center (StatedSU 3 (q.p ^ q.exponent) (GaloisField q.p (2 * q.exponent))) =
        (StatedScalars (Fin 3) (GaloisField q.p (2 * q.exponent))).subgroupOf
          (StatedSU 3 (q.p ^ q.exponent) (GaloisField q.p (2 * q.exponent))) := by
  have hq3 := three_le_card_of_valid_twistedA_two hv
  have hnq : ((3 : ℕ), q.p ^ q.exponent) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    simp only [PrimePower.card_def] at hq3
    omega
  have h := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (card_galoisField_two_mul_exponent q) le_rfl hnq
  exact ⟨isQuasisimple_open_of_foundations h.1, h.2⟩

noncomputable def statedSUThreeEquivCatalog (q : PrimePower) [Fact q.p.Prime]
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    StatedSU 3 (q.p ^ q.exponent) (GaloisField q.p (2 * q.exponent)) ⧸
        Subgroup.center
          (StatedSU 3 (q.p ^ q.exponent) (GaloisField q.p (2 * q.exponent))) ≃*
      (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩).Group :=
  (QuotientGroup.quotientMulEquivOfEq (isQuasisimple_statedSU_three q hv).2).trans
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv).symm

theorem fullLinearCover_true_of_cover (hM : ListedMultiplierBound 3) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (hi : k2 3 (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩) ∨
      k3 3 (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩))
    (h3 : 3 ∣ q.card + 1) {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (e : Q ⧸ Subgroup.center Q ≃* (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩).Group)
    (hZ : Nat.card (Subgroup.center Q) = 3) :
    FullLinearCover true 3 q.card Q := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨f⟩ := exists_mulEquiv_of_listed hM hi hQ (isQuasisimple_statedSU_three q hv).1 e
    (statedSUThreeEquivCatalog q hv) hZ
    (CFSG.Open.StatedCenterThree.card_center_statedSU_three (card_galoisField_two_mul_exponent q) h3)
  exact ⟨GaloisField q.p (2 * q.exponent), inferInstance, inferInstance,
    card_galoisField_two_mul_exponent q, ⟨f⟩⟩

end SU

section SUSix

open TauCeti

noncomputable def statedSUEquivCatalogOf (q : PrimePower) [Fact q.p.Prime] (r : ℕ)
    (hv : (LieTypeIndex.twistedA r q).Valid) {m : ℕ} (hm : q.p ^ q.exponent = m)
    (hcen : Subgroup.center (StatedSU (r + 1) m (GaloisField q.p (2 * q.exponent))) =
      (StatedScalars (Fin (r + 1)) (GaloisField q.p (2 * q.exponent))).subgroupOf
        (StatedSU (r + 1) m (GaloisField q.p (2 * q.exponent)))) :
    StatedSU (r + 1) m (GaloisField q.p (2 * q.exponent)) ⧸
        Subgroup.center (StatedSU (r + 1) m (GaloisField q.p (2 * q.exponent))) ≃*
      (CFSGIndex.lie ⟨LieTypeIndex.twistedA r q, hv⟩).Group := by
  subst hm
  exact (QuotientGroup.quotientMulEquivOfEq hcen).trans
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv).symm

theorem fullLinearCover_true_six_of_cover (hM : ListedMultiplierBound 3) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 5 q).Valid)
    (hi : k2 3 (CFSGIndex.lie ⟨LieTypeIndex.twistedA 5 q, hv⟩) ∨
      k3 3 (CFSGIndex.lie ⟨LieTypeIndex.twistedA 5 q, hv⟩))
    (hq : q.card = 2) {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (e : Q ⧸ Subgroup.center Q ≃* (CFSGIndex.lie ⟨LieTypeIndex.twistedA 5 q, hv⟩).Group)
    (hZ : Nat.card (Subgroup.center Q) = 3) :
    FullLinearCover true 6 2 Q := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK4 : Nat.card (GaloisField q.p (2 * q.exponent)) = 4 := by
    rw [card_galoisField_two_mul_exponent q, show q.p ^ q.exponent = 2 from hq]
    norm_num
  obtain ⟨f⟩ := exists_mulEquiv_of_listed hM hi hQ (isQuasisimple_statedSU_six_two hK4).1 e
    (statedSUEquivCatalogOf q 5 hv (m := 2) hq (isQuasisimple_statedSU_six_two hK4).2) hZ
    (card_center_statedSU_six_two hK4)
  exact ⟨GaloisField q.p (2 * q.exponent), inferInstance, inferInstance, by rw [hK4]; norm_num,
    ⟨f⟩⟩

end SUSix

end CFSG.LocalAnalysis.GLTheoremA.FullCover
