module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open

variable {K : Type} [Group K] [Finite K] {p : ℕ}

omit [Finite K] in
theorem eq_one_of_mem_inf_of_pGroup {S U : Subgroup K} (hS : IsPGroup p S) (hU : IsPGroup 2 U)
    (hp : p.Prime) (hp2 : p ≠ 2) {x : K} (hxS : x ∈ S) (hxU : x ∈ U) : x = 1 := by
  obtain ⟨a, ha⟩ := hU ⟨x, hxU⟩
  obtain ⟨b, hb⟩ := hS ⟨x, hxS⟩
  have h1 : x ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have h2 : x ^ p ^ b = 1 := congrArg Subtype.val hb
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h3 : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf x ∣ p ^ b := orderOf_dvd_of_pow_eq_one h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h4))

theorem two_le_pRank_of_exponent (hp : p.Prime) (S : Subgroup K) (hdvd : p ^ 2 ∣ Nat.card S)
    (hexp : ∀ s ∈ S, s ^ p = 1) : 2 ≤ Open.pRank p S := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) p hdvd
  set E : Subgroup K := E'.map S.subtype with hE
  have hEcard : Nat.card E = p ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective S.subtype_injective, hE']
  have hcomm : IsMulCommutative E' := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hE'
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : K) * b = b * a
      rw [← ha, ← hb]
      have := hcomm.is_comm.comm (⟨a', ha'⟩ : E') ⟨b', hb'⟩
      exact congrArg (fun z : E' => ((z : S) : K)) this
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
      exact hexp _ x'.2
  have hES : E ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  exact CFSG.SectionRank.le_pRank hp.one_lt hES hEab hEcard

theorem noTwo_of_gamma_le_normalizer (hp : p.Prime) (hp2 : p ≠ 2) (S : Sylow p K)
    (hdvd : p ^ 2 ∣ Nat.card S) (hexp : ∀ s ∈ (S : Subgroup K), s ^ p = 1)
    (hΓ : GLBCore p 1 (S : Subgroup K) ≤ Subgroup.normalizer ((S : Subgroup K) : Set K))
    (hC : ∀ g : K, (∀ s ∈ (S : Subgroup K), g * s = s * g) → g ∈ (S : Subgroup K))
    (U : Subgroup K) (hU : IsPGroup 2 U)
    (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  have hrank : 2 ≤ Open.pRank p (S : Subgroup K) :=
    two_le_pRank_of_exponent hp (S : Subgroup K) hdvd hexp
  have hcop : p.Coprime (Nat.card U) := by
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hUΓ : U ≤ rankThreeGamma 1 p (S : Subgroup K) :=
    CFSG.RankThreeCoreUniqueness.Helpers.rank_two_signalizer_le_gamma_one p hp
      (S : Subgroup K) (S : Subgroup K) U le_rfl hrank hSU hcop
  have hUN : U ≤ Subgroup.normalizer ((S : Subgroup K) : Set K) := hUΓ.trans hΓ
  have hSp : IsPGroup p (S : Subgroup K) := S.2
  rw [eq_bot_iff]
  intro u hu
  have hcomm : ∀ s ∈ (S : Subgroup K), u * s = s * u := by
    intro s hs
    have h1 : u * s * u⁻¹ ∈ (S : Subgroup K) := (Subgroup.mem_normalizer_iff.1 (hUN hu) s).1 hs
    have h2 : s * u * s⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hSU hs) u).1 hu
    have h3 : u * s * u⁻¹ * s⁻¹ ∈ (S : Subgroup K) :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hs)
    have h4 : u * s * u⁻¹ * s⁻¹ ∈ U := by
      have : u * s * u⁻¹ * s⁻¹ = u * (s * u * s⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ h2)
    have h5 := eq_one_of_mem_inf_of_pGroup hSp hU hp hp2 h3 h4
    calc u * s = (u * s * u⁻¹ * s⁻¹) * (s * u) := by group
      _ = s * u := by rw [h5, one_mul]
  exact Subgroup.mem_bot.2 (eq_one_of_mem_inf_of_pGroup hSp hU hp hp2 (hC u hcomm) hu)

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
