module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G]

section Generic

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G} {J : Subgroup G}
  {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}

theorem tits_two_le_pRank (hp : 1 < p) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) : 2 ≤ CFSG.Open.pRank p E :=
  CFSG.SectionRank.le_pRank hp le_rfl hE hcard

theorem tits_normalizer_T_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hc : PointConfig Typ G p P M x J) (hcard : Nat.card (u3T P x J) = p ^ 2)
    (hE : IsElemAbelian p (u3T P x J)) :
    Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTp : IsPGroup p (u3T P x J) := P.isPGroup'.to_le hTP
  exact normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core hTp (hTP.trans hPM)
    (tits_two_le_pRank hc.prime.one_lt hE hcard)

theorem tits_ker_coprime {Q : Type} [Group Q] (ψ : ↥J →* Q)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) :
    Nat.Coprime p (Nat.card ψ.ker) := by
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hOcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  rw [hker]
  have : Nat.card ((rankThreePrimeCore p J).subgroupOf J) = Nat.card (rankThreePrimeCore p J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
  rw [this]
  exact hOcop

theorem tits_trans_of_quotient
    (htrans : ∀ (K : Type) [Group K] [Finite K], Typ p K → NormalizerTransitive p K)
    (hc : PointConfig Typ G p P M x J) :
    ∀ a ∈ u3T P x J, a ≠ 1 → ∀ b ∈ u3T P x J, b ≠ 1 →
      ∃ n ∈ J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), n * a * n⁻¹ = b := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := tits_ker_coprime ψ hker
  have hcop' : ¬ p ∣ Nat.card ψ.ker := (hc.prime.coprime_iff_not_dvd).mp hcop
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hSylJ : IsSylowOf p (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ.exists_sylow_eq_subgroupOf
  have hTinj : ∀ t ∈ (Tsyl : Subgroup ↥J), ψ t = 1 → t = 1 :=
    u3main_eq_one_of_ker ψ hcop' Tsyl.isPGroup'
  let Tsyl' : Sylow p Q := Tsyl.mapSurjective hψ
  have hTsyl' : (Tsyl' : Subgroup Q) = (Tsyl : Subgroup ↥J).map ψ :=
    Sylow.coe_mapSurjective hψ Tsyl
  intro a ha ha1 b hb hb1
  have haJ : a ∈ J := hTJ ha
  have hbJ : b ∈ J := hTJ hb
  have ha0 : (⟨a, haJ⟩ : ↥J) ∈ (Tsyl : Subgroup ↥J) := by
    rw [hTsyl]; exact ha
  have hb0 : (⟨b, hbJ⟩ : ↥J) ∈ (Tsyl : Subgroup ↥J) := by
    rw [hTsyl]; exact hb
  have hψa : ψ ⟨a, haJ⟩ ≠ 1 := fun h => ha1 (congrArg Subtype.val (hTinj _ ha0 h))
  have hψb : ψ ⟨b, hbJ⟩ ≠ 1 := fun h => hb1 (congrArg Subtype.val (hTinj _ hb0 h))
  obtain ⟨n, hn, hnab⟩ := htrans Q hQ Tsyl' (ψ ⟨a, haJ⟩)
    (by rw [hTsyl']; exact ⟨_, ha0, rfl⟩) hψa (ψ ⟨b, hbJ⟩)
    (by rw [hTsyl']; exact ⟨_, hb0, rfl⟩) hψb
  obtain ⟨j, rfl⟩ := hψ n
  rw [hTsyl'] at hn
  obtain ⟨n₁, hn₁, hψn₁⟩ := typeII_frattini_ker ψ hcop Tsyl.isPGroup' hn
  refine ⟨(n₁ : G), Subgroup.mem_inf.mpr ⟨n₁.2, ?_⟩, ?_⟩
  · have := CFSG.LocalAnalysis.RankThreeTheoremC.u3main_mem_normalizer_map hn₁
    rwa [hTsyl, Subgroup.map_subgroupOf_eq_of_le hTJ] at this
  · have hcc : n₁ * ⟨a, haJ⟩ * n₁⁻¹ ∈ (Tsyl : Subgroup ↥J) :=
      (Subgroup.mem_normalizer_iff.mp hn₁ _).mp ha0
    have hψeq : ψ (n₁ * ⟨a, haJ⟩ * n₁⁻¹) = ψ ⟨b, hbJ⟩ := by
      rw [map_mul, map_mul, map_inv, hψn₁]
      exact hnab
    have h1 := hTinj ((n₁ * ⟨a, haJ⟩ * n₁⁻¹) * (⟨b, hbJ⟩ : ↥J)⁻¹)
      ((Tsyl : Subgroup ↥J).mul_mem hcc ((Tsyl : Subgroup ↥J).inv_mem hb0))
      (by rw [map_mul, map_inv, hψeq, mul_inv_cancel])
    exact congrArg Subtype.val (mul_inv_eq_one.mp h1)

end Generic

variable {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem tits_NJ_trans_of_plane (hS : Setting G) (hU0 : FullCoreLocal G) (hX : TitsFacts)
    (hc : PointConfig IsTitsType G 5 P M x J) (hcard : Nat.card (u3T P x J) = 5 ^ 2)
    (hE : IsElemAbelian 5 (u3T P x J)) :
    (J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M) ∧
      ∀ a ∈ u3T P x J, a ≠ 1 → ∀ b ∈ u3T P x J, b ≠ 1 →
        ∃ n ∈ J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), n * a * n⁻¹ = b :=
  ⟨inf_le_right.trans (tits_normalizer_T_le hS hU0 hc hcard hE), tits_trans_of_quotient hX.trans hc⟩

theorem tits_NJ_trans (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : TitsFacts)
    (hc : PointConfig IsTitsType G 5 P M x J) :
    (J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M) ∧
      ∀ a ∈ u3T P x J, a ≠ 1 → ∀ b ∈ u3T P x J, b ≠ 1 →
        ∃ n ∈ J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), n * a * n⁻¹ = b := by
  obtain ⟨hcard, hE, -⟩ := plane_T_structure hX.sylow hc
  exact tits_NJ_trans_of_plane hS hU0 hX hc hcard hE

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
