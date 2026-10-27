module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_torus_elt (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSz' : Sz32OpenFacts) (hdata : Sz32DataFacts)
    (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G} (hA : Sz32QDecomp P x J a c y) :
    ∃ n ∈ J, n * a ^ 5 * n⁻¹ = (a ^ 5) ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, _, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective _ hψ
  obtain ⟨Tsyl, hTsyl, hTinj⟩ := sps_sylow_data hc.generic hc.le_cent hc.cent_le ψ hker
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Sylow 5 Q, (Tb : Subgroup Q) = (Tsyl : Subgroup ↥J).map ψ :=
    ⟨Tsyl.mapSurjective hψ, Sylow.coe_mapSurjective hψ Tsyl⟩
  have haT : a ∈ u3T P x J := hA.T_eq ▸ Subgroup.mem_zpowers a
  have heaT : a ^ 5 ∈ u3T P x J := (u3T P x J).pow_mem haT 5
  obtain ⟨ea, hea⟩ : ∃ ea : ↥J, (ea : G) = a ^ 5 := ⟨⟨a ^ 5, J.pow_mem hA.a_J 5⟩, rfl⟩
  have heaTsyl : ea ∈ (Tsyl : Subgroup ↥J) := by
    rw [hTsyl, Subgroup.mem_subgroupOf, hea]
    exact heaT
  have hea2Tsyl : ea ^ 2 ∈ (Tsyl : Subgroup ↥J) := (Tsyl : Subgroup ↥J).pow_mem heaTsyl 2
  have hfinj : Function.Injective (ψ.comp (Tsyl : Subgroup ↥J).subtype) :=
    (injective_iff_map_eq_one _).mpr fun t ht => Subtype.ext (hTinj t t.2 ht)
  have hordψ : ∀ t : ↥J, t ∈ (Tsyl : Subgroup ↥J) → orderOf (ψ t) = orderOf t := by
    intro t ht
    have h := orderOf_injective (ψ.comp (Tsyl : Subgroup ↥J).subtype) hfinj ⟨t, ht⟩
    simpa [Subgroup.orderOf_mk] using h
  have hordea : orderOf ea = 5 := by
    rw [← Subgroup.orderOf_coe, hea, orderOf_pow_of_dvd (by norm_num) (by rw [hA.pres.ord_a]; norm_num),
      hA.pres.ord_a]
  have hordea2 : orderOf (ea ^ 2) = 5 := by
    rw [orderOf_pow' _ (by norm_num), hordea]
    norm_num
  obtain ⟨nb, hnb, hnbe⟩ := hSz'.transOmega Q hQ Tb (ψ ea)
    (by rw [hTb]; exact Subgroup.mem_map_of_mem ψ heaTsyl) (by rw [hordψ ea heaTsyl, hordea])
    (ψ (ea ^ 2)) (by rw [hTb]; exact Subgroup.mem_map_of_mem ψ hea2Tsyl)
    (by rw [hordψ _ hea2Tsyl, hordea2])
  obtain ⟨n₀, hn₀⟩ := hψ nb
  have hkcop : Nat.Coprime 5 (Nat.card ψ.ker) := by
    rw [hker]
    have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
    have h : Nat.card ((rankThreePrimeCore 5 J).subgroupOf J) = Nat.card (rankThreePrimeCore 5 J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [h]
    exact CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J
  have hnorm : ψ n₀ ∈ Subgroup.normalizer (((Tsyl : Subgroup ↥J).map ψ : Subgroup Q) : Set Q) := by
    rw [hn₀, ← hTb]
    exact hnb
  obtain ⟨n, hn, hψn⟩ := typeII_frattini_ker ψ hkcop Tsyl.isPGroup' hnorm
  have hnea : n * ea * n⁻¹ ∈ (Tsyl : Subgroup ↥J) :=
    (Subgroup.mem_normalizer_iff.mp hn ea).mp heaTsyl
  have hψeq : ψ (n * ea * n⁻¹) = ψ (ea ^ 2) := by
    rw [map_mul, map_mul, map_inv, hψn, hn₀]
    exact hnbe
  have heq : n * ea * n⁻¹ = ea ^ 2 := by
    have hmem : (n * ea * n⁻¹) * (ea ^ 2)⁻¹ ∈ (Tsyl : Subgroup ↥J) :=
      (Tsyl : Subgroup ↥J).mul_mem hnea ((Tsyl : Subgroup ↥J).inv_mem hea2Tsyl)
    have h1 : ψ ((n * ea * n⁻¹) * (ea ^ 2)⁻¹) = 1 := by
      rw [map_mul, map_inv, hψeq, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hTinj _ hmem h1)
  refine ⟨(n : G), n.2, ?_⟩
  have h := congrArg Subtype.val heq
  simpa [hea] using h

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
