module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Fusion
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC TypeSE Lemma33Data U3Lemma33
  lemma33_gen fus_exists_mul_of_sup_eq fus_mem_zpowers_of_isCyclic_of_pow_prime)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}

theorem plane_abelian
    (hsyl : ∀ (K : Type) [Group K] [Finite K], Typ p K → SylowIsPlane p K)
    (hno : ∀ (K : Type) [Group K] [Finite K], Typ p K → NoOuterP p K)
    (hc : PointConfig Typ G p P M x J) :
    ∀ a ∈ u3S P x, ∀ b ∈ u3S P x, a * b = b * a := by
  obtain ⟨-, hTel, -⟩ := plane_T_structure hsyl hc
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := plane_S_decomp hsyl hno hc
  haveI : IsMulCommutative (u3T P x J) := hTel.1
  haveI : IsMulCommutative Z := IsCyclic.isMulCommutative
  have hTc : ∀ a ∈ u3T P x J, ∀ b ∈ u3T P x J, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : u3T P x J) ⟨b, hb⟩)
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Z) ⟨b, hb⟩)
  intro a ha b hb
  obtain ⟨t₁, ht₁, z₁, hz₁, rfl⟩ := fus_exists_mul_of_sup_eq hZT hsup a ha
  obtain ⟨t₂, ht₂, z₂, hz₂, rfl⟩ := fus_exists_mul_of_sup_eq hZT hsup b hb
  have h1 : z₁ * t₂ = t₂ * z₁ := hZT z₁ hz₁ t₂ ht₂
  have h2 : z₂ * t₁ = t₁ * z₂ := hZT z₂ hz₂ t₁ ht₁
  have h3 : t₁ * t₂ = t₂ * t₁ := hTc t₁ ht₁ t₂ ht₂
  have h4 : z₁ * z₂ = z₂ * z₁ := hZc z₁ hz₁ z₂ hz₂
  calc t₁ * z₁ * (t₂ * z₂) = t₁ * (z₁ * t₂) * z₂ := by group
    _ = (t₁ * t₂) * (z₁ * z₂) := by rw [h1]; group
    _ = (t₂ * t₁) * (z₂ * z₁) := by rw [h3, h4]
    _ = t₂ * (t₁ * z₂) * z₁ := by group
    _ = t₂ * (z₂ * t₁) * z₁ := by rw [h2]
    _ = t₂ * z₂ * (t₁ * z₁) := by group

theorem plane_omega
    (hsyl : ∀ (K : Type) [Group K] [Finite K], Typ p K → SylowIsPlane p K)
    (hno : ∀ (K : Type) [Group K] [Finite K], Typ p K → NoOuterP p K)
    (hc : PointConfig Typ G p P M x J) :
    ∀ y ∈ u3S P x, y ^ p = 1 → ∃ t ∈ u3T P x J, ∃ z ∈ Subgroup.zpowers x, y = t * z := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  obtain ⟨-, hTel, -⟩ := plane_T_structure hsyl hc
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := plane_S_decomp hsyl hno hc
  intro y hyS hyp
  obtain ⟨t, htT, z, hzZ, hyt⟩ := fus_exists_mul_of_sup_eq hZT hsup y hyS
  have hcz : Commute t z := (hZT z hzZ t htT).symm
  have htp : t ^ p = 1 := hTel.2 t htT
  have hzp : z ^ p = 1 := by
    have h := hyp
    rw [hyt, hcz.mul_pow, htp, one_mul] at h
    exact h
  exact ⟨t, htT, z, fus_mem_zpowers_of_isCyclic_of_pow_prime hZcyc hxZ hzZ hx1 hxp hzp, hyt⟩

theorem plane_lemma33 (hS : Setting G) (hD1 : TheoremD1 G) (hSig : SignalizerTwoGroupKFact)
    (hsyl : ∀ (K : Type) [Group K] [Finite K], Typ p K → SylowIsPlane p K)
    (hno : ∀ (K : Type) [Group K] [Finite K], Typ p K → NoOuterP p K)
    (hSE : TypeSE Typ p) (hc : PointConfig Typ G p P M x J) : U3Lemma33 p x := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTcard, hTel, hxJ⟩ := plane_T_structure hsyl hc
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := plane_S_decomp hsyl hno hc
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hSab := plane_abelian hsyl hno hc
  exact lemma33_gen hS hD1 hSig hc hSE
    { not_mem := hxJ
      exp := fun t ht => hTel.2 t ht
      rank := fun E hE _ => (Subgroup.card_le_of_le hE).trans hTcard.le
      decomp := ⟨Z, hZcyc, hxZ, hZS, hZT, hsup⟩
      plane := ⟨u3T P x J, hTel, hTcard, hTS, fun s hs a ha => hSab s hs a (hTS ha)⟩ }

theorem plane_quotient_data (hc : PointConfig Typ G p P M x J) {Q : Type} [Group Q] [Finite Q]
    (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) :
    ∃ S' : Sylow p Q,
      (∀ t (ht : t ∈ u3T P x J), ψ ⟨t, (inf_le_right : u3T P x J ≤ J) ht⟩ ∈ (S' : Subgroup Q)) ∧
      (∀ s ∈ (S' : Subgroup Q), ∃ t, ∃ ht : t ∈ u3T P x J,
        ψ ⟨t, (inf_le_right : u3T P x J ≤ J) ht⟩ = s) ∧
      (∀ t (ht : t ∈ u3T P x J) t' (ht' : t' ∈ u3T P x J),
        ψ ⟨t, (inf_le_right : u3T P x J ≤ J) ht⟩ = ψ ⟨t', (inf_le_right : u3T P x J ≤ J) ht'⟩ →
          t = t') ∧
      (∀ nb ∈ Subgroup.normalizer ((S' : Subgroup Q) : Set Q), ∃ n, ∃ hnJ : n ∈ J,
        n ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ∧ ψ ⟨n, hnJ⟩ = nb) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := tits_ker_coprime ψ hker
  have hcop' : ¬ p ∣ Nat.card ψ.ker := (hc.prime.coprime_iff_not_dvd).mp hcop
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hSylJ : IsSylowOf p (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ.exists_sylow_eq_subgroupOf
  have hTinj : ∀ t ∈ (Tsyl : Subgroup ↥J), ψ t = 1 → t = 1 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.u3main_eq_one_of_ker ψ hcop' Tsyl.isPGroup'
  let Tsyl' : Sylow p Q := Tsyl.mapSurjective hψ
  have hTsyl' : (Tsyl' : Subgroup Q) = (Tsyl : Subgroup ↥J).map ψ :=
    Sylow.coe_mapSurjective hψ Tsyl
  have hmem : ∀ t (ht : t ∈ u3T P x J), (⟨t, hTJ ht⟩ : ↥J) ∈ (Tsyl : Subgroup ↥J) := by
    intro t ht
    rw [hTsyl]
    exact ht
  refine ⟨Tsyl', ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hTsyl']
    exact ⟨_, hmem t ht, rfl⟩
  · intro s hs
    rw [hTsyl'] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    rw [hTsyl] at hj
    exact ⟨(j : G), hj, rfl⟩
  · intro t ht t' ht' h
    have h1 : (⟨t, hTJ ht⟩ : ↥J) * (⟨t', hTJ ht'⟩ : ↥J)⁻¹ = 1 :=
      hTinj _ ((Tsyl : Subgroup ↥J).mul_mem (hmem t ht) ((Tsyl : Subgroup ↥J).inv_mem (hmem t' ht')))
        (by rw [map_mul, map_inv, h, mul_inv_cancel])
    exact congrArg Subtype.val (mul_inv_eq_one.mp h1)
  · intro nb hn
    obtain ⟨j, rfl⟩ := hψ nb
    rw [hTsyl'] at hn
    obtain ⟨n₁, hn₁, hψn₁⟩ := typeII_frattini_ker ψ hcop Tsyl.isPGroup' hn
    refine ⟨(n₁ : G), n₁.2, ?_, hψn₁⟩
    have := CFSG.LocalAnalysis.RankThreeTheoremC.u3main_mem_normalizer_map hn₁
    rwa [hTsyl, Subgroup.map_subgroupOf_eq_of_le hTJ] at this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
