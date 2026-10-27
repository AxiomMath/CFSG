module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Adapters.StatedQuasisimple
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

noncomputable section

private theorem coverrec_isCyclic_of_card {G : Type} [Group G]
    (h : Nat.card G = 1 ∨ Nat.card G = 3) : IsCyclic G := by
  rcases h with h | h
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h).1
    exact inferInstance
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card h

private theorem coverrec_valid_A_two {q : TauCeti.PrimePower} (h2 : q.card ≠ 2) :
    (TauCeti.LieTypeIndex.A 2 q).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  refine ⟨⟨by norm_num, fun h => absurd h (by norm_num)⟩, ?_⟩
  rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
  · exact absurd h (by norm_num)
  · exact h2 h
  · exact absurd h (by norm_num)

private theorem coverrec_valid_twistedA_two {q : TauCeti.PrimePower} (h3 : 3 ≤ q.card) :
    (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  exact ⟨⟨le_rfl, fun _ => h3⟩, fun h => h⟩

private theorem coverrec_valid_A_one {q : TauCeti.PrimePower} (hq : q.card = 7) :
    (TauCeti.LieTypeIndex.A 1 q).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  refine ⟨⟨le_rfl, fun _ => by omega⟩, ?_⟩
  rintro (⟨-, h | h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega

theorem native_SL3_recognition
    (r f : ℕ) (hr : r.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = r ^ f) :
    IsQuasisimple (StatedSL 3 K) ∧
      (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) =
        Subgroup.center (StatedSL 3 K) ∧
      IsCyclic (Subgroup.center (StatedSL 3 K)) ∧
      Nat.card (Subgroup.center (StatedSL 3 K)) = Nat.gcd 3 (r ^ f - 1) ∧
      catalogIs (StatedProj (StatedSL 3 K))
        (if r ^ f = 2 then onLie (isL2 7) else onLie fun d =>
          match d with
          | .A 2 q => q.card = r ^ f
          | _ => False) := by
  have hfpos : 0 < f := by omega
  haveI : Fact r.Prime := ⟨hr⟩
  have hcen : Subgroup.center (StatedSL 3 K) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) := by
    rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 K,
      Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)]
  have hcard : Nat.card (Subgroup.center (StatedSL 3 K)) = Nat.gcd 3 (r ^ f - 1) := by
    by_cases h3 : 3 ∣ r ^ f - 1
    · rw [Nat.gcd_eq_left h3]
      exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (by rw [hK]; exact h3)
    · have hcop : Nat.gcd 3 (r ^ f - 1) = 1 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
      have hsub : ∀ z : Subgroup.center (StatedSL 3 K), z = 1 := by
        intro z
        have hz : (z : StatedSL 3 K) ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) := by
          rw [← hcen]
          exact z.2
        rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
        obtain ⟨c, hc⟩ := hz
        have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL (z : StatedSL 3 K).2
        rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
        have hc3 : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
        have hord : c ^ (r ^ f - 1) = 1 := by
          have h := orderOf_dvd_natCard c
          rw [Nat.card_units, hK] at h
          exact orderOf_dvd_iff_pow_eq_one.1 h
        have hc1 : c = 1 := by
          have h := pow_gcd_eq_one.2 ⟨hc3, hord⟩
          rw [hcop, pow_one] at h
          exact h
        apply Subtype.ext
        apply Subtype.ext
        show ((z : StatedSL 3 K) : Matrix.GeneralLinearGroup (Fin 3) K) = 1
        rw [← hc, hc1, map_one]
      haveI : Subsingleton (Subgroup.center (StatedSL 3 K)) :=
        ⟨fun a b => (hsub a).trans (hsub b).symm⟩
      haveI : Nonempty (Subgroup.center (StatedSL 3 K)) := ⟨1⟩
      rw [hcop]
      exact Nat.card_unique
  refine ⟨CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl K, hcen.symm, ?_,
    hcard, ?_⟩
  · apply coverrec_isCyclic_of_card
    rw [hcard]
    exact (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (r ^ f - 1))
  · let q : TauCeti.PrimePower := ⟨r, f, hr, hfpos⟩
    haveI : Fact q.p.Prime := ⟨hr⟩
    by_cases h2 : r ^ f = 2
    · rw [if_pos h2]
      have hK2 : Nat.card K = 2 ^ 1 := by simp [hK, h2]
      have hadm3 : StatedLieAdmissible .PSL 3 2 1 :=
        ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
      have hmodel : CFSG.Blueprint.LieModel (StatedProj (StatedSL 3 K)) .PSL 3 2 1 :=
        Or.inl ⟨by decide, hadm3, K, inferInstance, inferInstance, hK2, ⟨MulEquiv.refl _⟩⟩
      rcases CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _
          hmodel with ⟨-, hc7⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · obtain ⟨-, K7, _, _, hK7, ⟨e7⟩⟩ := hc7
        haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
        let q7 : TauCeti.PrimePower := ⟨7, 1, Nat.prime_seven, by norm_num⟩
        haveI : Fact q7.p.Prime := ⟨Nat.prime_seven⟩
        have hq7 : q7.card = 7 := by
          rw [TauCeti.PrimePower.card_def]
          norm_num [q7]
        have hv7 : (TauCeti.LieTypeIndex.A 1 q7).Valid := coverrec_valid_A_one hq7
        let eK7 := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K7 2 7 1 (by norm_num) hK7
        refine ⟨.lie ⟨TauCeti.LieTypeIndex.A 1 q7, hv7⟩, hq7, ⟨(e7.trans eK7).trans
          (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q7 hv7).symm⟩⟩
      · exact absurd h0 (by norm_num)
      · exact absurd h0 (by norm_num)
      · exact absurd h0 (by norm_num)
    · rw [if_neg h2]
      have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := coverrec_valid_A_two (q := q) h2
      let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 3 r f hfpos hK
      refine ⟨.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩, rfl, ⟨eK.trans
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm⟩⟩

theorem native_SU3_recognition
    (r f : ℕ) (hr : r.Prime) (hf : 1 ≤ f) (hq : 2 < r ^ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (r ^ f) ^ 2) :
    IsQuasisimple (StatedSU 3 (r ^ f) K) ∧
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (r ^ f) K) =
        Subgroup.center (StatedSU 3 (r ^ f) K) ∧
      IsCyclic (Subgroup.center (StatedSU 3 (r ^ f) K)) ∧
      Nat.card (Subgroup.center (StatedSU 3 (r ^ f) K)) = Nat.gcd 3 (r ^ f + 1) ∧
      catalogIs (StatedProj (StatedSU 3 (r ^ f) K)) (onLie fun d =>
        match d with
        | .twistedA 2 q => q.card = r ^ f
        | _ => False) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hnq : ((3 : ℕ), r ^ f) ≠ (3, 2) := by
    intro h
    have h2 : r ^ f = 2 := (Prod.mk.inj h).2
    omega
  obtain ⟨hQ, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK le_rfl hnq
  have hcard : Nat.card (Subgroup.center (StatedSU 3 (r ^ f) K)) = Nat.gcd 3 (r ^ f + 1) := by
    rw [hZ]
    exact (CFSG.LinearGroups.unitary_scalar_kernel hr hK (by norm_num)).2.2
  refine ⟨hQ, hZ.symm, ?_, hcard, ?_⟩
  · apply coverrec_isCyclic_of_card
    rw [hcard]
    exact (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (r ^ f + 1))
  · let q : TauCeti.PrimePower := ⟨r, f, hr, by omega⟩
    have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid :=
      coverrec_valid_twistedA_two (q := q) (by change 3 ≤ r ^ f; omega)
    have hGF : Nat.card (GaloisField r (2 * f)) = (r ^ f) ^ 2 := by
      rw [GaloisField.card r (2 * f) (by omega), ← pow_mul, mul_comm]
    letI : Fintype K := Fintype.ofFinite K
    letI : Fintype (GaloisField r (2 * f)) := Fintype.ofFinite _
    have hfc : Fintype.card K = Fintype.card (GaloisField r (2 * f)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hGF]
    let φ : K ≃+* GaloisField r (2 * f) := FiniteField.ringEquivOfCardEq hfc
    exact ⟨.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩, rfl,
      ⟨(CFSG.Open.StatedSUFieldChange.statedProjSUEquiv φ 3 (r ^ f)).trans
        (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv).symm⟩⟩

end

end CFSG.LocalAnalysis.GLTheoremA
