module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsL28
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Dichotomy
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Linear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Small
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI122FiveOut
public import CFSG.Open.MonsterY443Finiteness

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28

open CFSG.Open CFSG.RankThree.PartOne Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 (pGoodOut_three_or_of_catalog
  d4ThreeRankFour_holds e6ThreeRankFour_holds twistedE6ThreeRankFour_holds)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (exists_normal_index_pow_of_pGoodOut)

variable {X : Type} [Group X] [Finite X]

theorem ThreeQuotient.false_of_le_lie (hLie : Sylow3OmegaLie) (K : Subgroup X) [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K)
    (hmodel : ∃ (t : StatedLieTag) (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f ∧ LieModel K t n ℓ f)
    (S : Sylow 3 X) {Q₀ : Subgroup X} (hD : ShapeData (S : Subgroup X) Q₀)
    (hSK : (S : Subgroup X) ≤ K) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : ((S.subtype hSK : Sylow 3 K) : Subgroup K) = (S : Subgroup X).subgroupOf K := rfl
  have hTcard : Nat.card ((S.subtype hSK : Sylow 3 K) : Subgroup K) = 3 ^ 5 := by
    rw [hT, ← hD.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3 := by
    apply le_antisymm
    · exact (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) K.subtype
        K.subtype_injective).trans (hD.pRank_le_three S)
    · obtain ⟨E, hES, hE, hEcard, -⟩ := hD.exists_omega
      refine CFSG.SectionRank.le_pRank (by norm_num) le_top (E := E.subgroupOf K) ?_ ?_
      · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
        · have h2 := congrArg Subtype.val (hE.1.1.comm ⟨((a : K) : X), a.2⟩ ⟨((b : K) : X), b.2⟩)
          simp only [Subgroup.coe_mul, Subgroup.coe_mk] at h2 ⊢
          exact h2
        · exact hE.2 _ hx
      · rw [← hEcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hES.trans hSK)).toEquiv
  have hΩ : ∀ x ∈ ((S.subtype hSK : Sylow 3 K) : Subgroup K),
      ∀ y ∈ ((S.subtype hSK : Sylow 3 K) : Subgroup K), x ^ 3 = 1 → y ^ 3 = 1 →
        x * y = y * x := by
    intro x hx y hy hx3 hy3
    rw [hT, Subgroup.mem_subgroupOf] at hx hy
    apply Subtype.ext
    have hx3' : (x : X) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    have hy3' : (y : X) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
    simpa using hD.omega_comm hx hy hx3' hy3'
  have hab := hLie K inferInstance hnab hcat hmodel hrank (S.subtype hSK) hTcard hΩ
  apply hD.not_comm
  intro a ha b hb
  have haT : (⟨a, hSK ha⟩ : K) ∈ ((S.subtype hSK : Sylow 3 K) : Subgroup K) := by
    rw [hT, Subgroup.mem_subgroupOf]
    exact ha
  have hbT : (⟨b, hSK hb⟩ : K) ∈ ((S.subtype hSK : Sylow 3 K) : Subgroup K) := by
    rw [hT, Subgroup.mem_subgroupOf]
    exact hb
  have h := hab.1.comm ⟨_, haT⟩ ⟨_, hbT⟩
  have h2 := congrArg (fun k : ((S.subtype hSK : Sylow 3 K) : Subgroup K) => ((k : K) : X)) h
  simp only [Subgroup.coe_mul, Subgroup.coe_mk] at h2
  exact h2

section Heavy


theorem ThreeQuotient.false_of_le (hLie : Sylow3OmegaLie) (K : Subgroup X) [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K) (S : Sylow 3 X)
    {Q₀ : Subgroup X} (hD : ShapeData (S : Subgroup X) Q₀) (hSK : (S : Subgroup X) ≤ K) :
    False := by
  rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, -, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact false_of_le_alt K hn5 e S hD hSK
  · exact false_of_le_lie hLie K hnab hcat ⟨t, n, ℓ, f, hadm, hmodel⟩ S hD hSK
  · have hcard : Nat.card K = CFSG.AGLEmbedding.sporOrd s :=
      (Nat.card_congr e.toEquiv).trans
        (CFSG.AGLEmbedding.card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card s)
    have h5 : 3 ^ 5 ∣ CFSG.AGLEmbedding.sporOrd s :=
      hcard ▸ (hD.card ▸ Subgroup.card_dvd_of_le hSK)
    have h6 : ¬ 3 ^ 6 ∣ CFSG.AGLEmbedding.sporOrd s := fun h =>
      hD.not_dvd_card S ((hcard ▸ h).trans (Subgroup.card_subgroup_dvd_card K))
    obtain rfl := sporOrd_eq_J3 s h5 h6
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
    exact false_of_le_J3 K (e.trans b) S hD hSK

theorem kFactL28ThreeQuotient_of_sylow3OmegaLie (hLie : Sylow3OmegaLie) :
    KFactL28ThreeQuotient := by
  intro X _ _ K hKn hs hnab hcat hKC _ Q hQ hshape hQX
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup K := hs
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, rfl⟩ := exists_sylow_eq_of_isSylowOf_top hQ
  obtain ⟨Q₀, hD⟩ := ThreeQuotient.L28Shape.shapeData hshape
  rcases pGoodOut_three_or_of_catalog d4ThreeRankFour_holds e6ThreeRankFour_holds
      twistedE6ThreeRankFour_holds hnab hcat with hP | hLU | h4
  · by_cases hSK : (S : Subgroup X) ≤ K
    · exact false_of_le hLie K hnab hcat S hD hSK
    · obtain ⟨q, hqS, hqK⟩ := SetLike.not_le_iff_exists.1 hSK
      have hq3 : ∃ k : ℕ, q ^ (3 ^ k) = 1 := by
        obtain ⟨k, hk⟩ := S.isPGroup' ⟨q, hqS⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      obtain ⟨N, hN, hidx, hNtop⟩ :=
        exists_normal_index_pow_of_pGoodOut Nat.prime_three K hKC hP hq3 hqK
      haveI := hN
      exact not_le_commutator_of_normal_index S N hidx hNtop hQX
  · exact false_of_linearOrUnitary K hKC hnab S hD hQX hLU
  · have h1 := CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) K.subtype
      K.subtype_injective
    have := hD.pRank_le_three S
    omega

theorem kFactL28ThreeQuotient_of_lieThreeDich (h : LieThreeDich) : KFactL28ThreeQuotient :=
  kFactL28ThreeQuotient_of_sylow3OmegaLie (sylow3OmegaLie_of_lieThreeDich h)

end Heavy

end CFSG.LocalAnalysis.RankThreeTheoremC.L28
