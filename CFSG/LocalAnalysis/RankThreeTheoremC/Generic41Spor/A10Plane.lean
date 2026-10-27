module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Cent
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupWitness
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_plane (hX : A10Facts) (hXe : A10Ext) (hc : PointConfig IsA10Type G 5 P M x J)
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J) (hQ : IsA10Type 5 Q) :
    ∃ U : Subgroup G, IIPlane 5 P x J U ∧ A10PlaneShape J (u3T P x J) ψ U := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : (5 : ℕ).Prime := by norm_num
  have hJC : J ≤ Subgroup.centralizer ({x} : Set G) := hc.le_cent
  have hCJ : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
  have hOcop : (5 : ℕ).Coprime (Nat.card (rankThreePrimeCore 5 J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J
  have hOcop' : ¬ 5 ∣ Nat.card (rankThreePrimeCore 5 J) := (hp.coprime_iff_not_dvd).mp hOcop
  have hkcop : ¬ 5 ∣ Nat.card ψ.ker := by
    rw [hker]
    have : Nat.card ((rankThreePrimeCore 5 J).subgroupOf J) = Nat.card (rankThreePrimeCore 5 J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [this]
    exact hOcop'
  obtain ⟨Tsyl, hTsyl⟩ : CFSG.ABGLocalTools.IsSylowOf 5 (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hJC hCJ
  set T0 : Subgroup J := (Tsyl : Subgroup J) with hT0
  let Tsyl' : Sylow 5 Q := Tsyl.mapSurjective hψ
  have hTsyl' : (Tsyl' : Subgroup Q) = T0.map ψ := Sylow.coe_mapSurjective hψ Tsyl
  obtain ⟨A₁, A₂, hne, hA₁S, hA₂S, hc1, hc2, hsup, h300, h25⟩ := a10_centFacts Q hQ Tsyl'
  have hA₁ne : A₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc1
    norm_num at hc1
  have hA₂ne : A₂ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc2
    norm_num at hc2
  obtain ⟨a₁, ha₁⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA₁ne
  obtain ⟨a₂, ha₂⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA₂ne
  have hgen₂ : A₂ = Subgroup.zpowers (a₂ : Q) :=
    eq_zpowers_of_card_prime hp hc2 a₂.2 (fun h => ha₂ (Subtype.ext h))
  have hgen₁ : A₁ = Subgroup.zpowers (a₁ : Q) :=
    eq_zpowers_of_card_prime hp hc1 a₁.2 (fun h => ha₁ (Subtype.ext h))
  set s : Q := (a₁ : Q) * (a₂ : Q) with hs
  have hsS : s ∈ (Tsyl' : Subgroup Q) := (Subgroup.mul_mem _ (hA₁S a₁.2) (hA₂S a₂.2))
  have hs1 : s ∉ A₁ := by
    intro h
    have h2 : (a₂ : Q) ∈ A₁ := by
      have := A₁.mul_mem (A₁.inv_mem a₁.2) h
      simpa [hs, mul_assoc] using this
    have : A₂ ≤ A₁ := by rw [hgen₂]; exact Subgroup.zpowers_le.2 h2
    exact hne (Subgroup.eq_of_le_of_card_ge this (by rw [hc1, hc2])).symm
  have hs2 : s ∉ A₂ := by
    intro h
    have h2 : (a₁ : Q) ∈ A₂ := by
      have := A₂.mul_mem h (A₂.inv_mem a₂.2)
      simpa [hs, mul_assoc] using this
    have : A₁ ≤ A₂ := by rw [hgen₁]; exact Subgroup.zpowers_le.2 h2
    exact hne (Subgroup.eq_of_le_of_card_ge this (by rw [hc1, hc2]))
  have hs3 : s ≠ 1 := fun h => hs1 (h ▸ A₁.one_mem)
  have hcs := h25 s hsS hs1 hs2 hs3
  rw [hTsyl'] at hsS
  obtain ⟨t0, ht0, hψt0⟩ := hsS
  have hdT : ((t0 : J) : G) ∈ u3T P x J := by
    rw [← hTsyl]
    exact ⟨t0, ht0, rfl⟩
  have hd1 : ((t0 : J) : G) ≠ 1 := by
    intro h
    apply hs3
    rw [← hψt0]
    have : t0 = 1 := Subtype.ext h
    rw [this, map_one]
  have hUP := plane_iiplane (fun K _ _ hK => hX.sylow K hK) (fun K _ _ hK => hX.noOuter K hK) hc hdT hd1
  refine ⟨_, hUP, (t0 : J), t0.2, ⟨?_, hdT⟩, ?_, ?_⟩
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · rw [hψt0]; exact hs3
  · rw [hψt0]; exact hcs

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
