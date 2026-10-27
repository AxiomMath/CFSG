module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I714FourCyc
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I714FourLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.HardMathSupport.Lang.Coordinator (OuterFixedOrderBoundCyc)
open scoped commutatorElement

theorem kFactI714Four_of_inputs
    (h8 : KFactI713Out)
    (hgood : ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], (∃ a b : K, a * b ≠ b * a) →
      IsCatalogGroup K → ∀ T : Sylow 5 K, IsCyclic (T : Subgroup K) → PGoodOut 5 K)
    (hbound : OuterFixedOrderBoundCyc) (hord : LieOrderFormulasInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hspor : ∀ s : TauCeti.SporadicName, Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group))
    (hsporOut : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)) :
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
      (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
      ∀ Q : Sylow 5 X, ¬ (Q : Subgroup X) ≤ K → Nat.card (Q : Subgroup X) = 125 →
        ¬ IsMulCommutative (Q : Subgroup X) → (∀ q ∈ (Q : Subgroup X), q ^ 25 = 1) →
        (∃ q ∈ (Q : Subgroup X), q ^ 5 ≠ 1) →
        (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ), ℓ ≠ 5 ∧
          CFSG.Blueprint.LieModel ↥K t n ℓ f) ∧
        (Nat.card (((Q : Subgroup X) ⊓ K : Subgroup X)) = 25 ∧
          IsCyclic (((Q : Subgroup X) ⊓ K : Subgroup X))) := by
  intro X _ _ K hKn hKs hKnab hKcat hKc Q hQK hQc hQnab hQe hQb
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ3 : Nat.card (Q : Subgroup X) = 5 ^ 3 := by rw [hQc]; norm_num
  have hM : NoM125.IsM125 5 (Q : Subgroup X) :=
    ⟨Nat.prime_five, by norm_num, hQ3, hQnab, fun s hs => by simpa using hQe s hs, hQb⟩
  have hcyc : IsCyclic ↥((Q : Subgroup X) ⊓ K) := isCyclic_inf_of_isM125 hKs hKnab Q hM
  have hQsyl : IsSylowOf 5 (Q : Subgroup X) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
  have hsyl : IsSylowOf 5 ((Q : Subgroup X) ⊓ K) K :=
    hQsyl.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr hKn).ge
  obtain ⟨T, hT⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hTcyc : IsCyclic (T : Subgroup ↥K) := by
    rw [hT]
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe inf_le_right).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hQle : ¬ 5 ∣ Nat.card (Outer ↥K) → False := fun hout =>
    hQK fun q hq => mem_of_pow_eq_one_of_not_dvd_outer (m := 2) Nat.prime_five hout hKc
      (by simpa using hQe q hq)
  obtain ⟨v, hv⟩ : ∃ v, v = (Nat.card ↥K).factorization 5 := ⟨_, rfl⟩
  have hcard : Nat.card ↥((Q : Subgroup X) ⊓ K) = 5 ^ v := by rw [hv]; exact hsyl.card_eq
  have hv3 : v ≤ 3 := by
    have hdvd : 5 ^ v ∣ 5 ^ 3 := by
      rw [← hcard, ← hQ3]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  interval_cases v
  ·
    exfalso
    have hPG : PGoodOut 5 ↥K := hgood ↥K hKnab hKcat T hTcyc
    have hbot : (Q : Subgroup X) ⊓ K = ⊥ := Subgroup.eq_bot_of_card_eq _ (by simpa using hcard)
    apply hQnab
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    have hQ2 : ∀ g ∈ (Q : Subgroup X), g ^ (5 ^ 2) = 1 := fun g hg => by simpa using hQe g hg
    have hmemQ : ⁅(b : X), (a : X)⁆ ∈ (Q : Subgroup X) := by
      rw [commutatorElement_def]
      exact (Q : Subgroup X).mul_mem ((Q : Subgroup X).mul_mem ((Q : Subgroup X).mul_mem b.2 a.2)
        ((Q : Subgroup X).inv_mem b.2)) ((Q : Subgroup X).inv_mem a.2)
    have hmemK : ⁅(b : X), (a : X)⁆ ∈ K :=
      commutator_mem_of_pGoodOut hPG hKc (hQ2 a a.2) (hQ2 _ hmemQ)
    have h1 : ⁅(b : X), (a : X)⁆ ∈ (Q : Subgroup X) ⊓ K := ⟨hmemQ, hmemK⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    exact h2.symm
  ·
    exfalso
    have hrk : CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) ≤ 1 :=
      CFSG.SectionRank.pRank_le Nat.prime_five.one_lt fun E _ hE =>
        (CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow T hTcyc hE).trans (by simp)
    have hS : ∀ S : Sylow 5 ↥K, Nat.card (S : Subgroup ↥K) = 5 := fun S => by
      rw [S.card_eq_multiplicity, ← hv, pow_one]
    exact hQle ((h8 5 Nat.prime_five (by norm_num) ↥K hKs hKnab hKcat hrk).1 hS)
  ·
    refine ⟨?_, by simpa using hcard, hcyc⟩
    rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases (hbridge ↥K hKnab hKcat) with
      ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
    · exfalso
      obtain ⟨a, b, hab⟩ := hKnab
      exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
    · exfalso
      apply hQle
      rw [Nat.card_congr (equivalence e).toEquiv]
      exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 5 Nat.prime_five
        (by norm_num)
    · by_cases hℓ : ℓ = 5
      · exfalso
        subst hℓ
        obtain ⟨a, -, haK, ha5⟩ := exists_pow_five_eq_one_not_mem hM hcyc (by simpa using hcard)
        exact false_of_lieModel_char_five hbound hord hKc hadm hmodel hv.symm haK ha5
      · exact ⟨t, n, ℓ, f, hℓ, hmodel⟩
    · exfalso
      apply hQle
      obtain ⟨e'⟩ := hspor s
      rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
      exact hsporOut s 5 Nat.prime_five (by norm_num)
  ·
    exfalso
    apply hQK
    have hQK' : (Q : Subgroup X) ⊓ K = Q :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hQ3])
    exact hQK'.ge.trans inf_le_right

section Heavy


theorem kFactI714Four_core :
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
      (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
      ∀ Q : Sylow 5 X, ¬ (Q : Subgroup X) ≤ K → Nat.card (Q : Subgroup X) = 125 →
        ¬ IsMulCommutative (Q : Subgroup X) → (∀ q ∈ (Q : Subgroup X), q ^ 25 = 1) →
        (∃ q ∈ (Q : Subgroup X), q ^ 5 ≠ 1) →
        (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ), ℓ ≠ 5 ∧
          CFSG.Blueprint.LieModel ↥K t n ℓ f) ∧
        (Nat.card (((Q : Subgroup X) ⊓ K : Subgroup X)) = 25 ∧
          IsCyclic (((Q : Subgroup X) ⊓ K : Subgroup X))) :=
  kFactI714Four_of_inputs kFactI713Out_holds
    (fun _ _ _ _ hnab hcat T hT =>
      CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.pGoodOut_of_cyclic_odd hnab hcat
        Nat.prime_five (by norm_num) T hT)
    CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    (CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group)

theorem kFactI714Four'_holds : KFactI714Four' := kFactI714Four_core

end Heavy

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
