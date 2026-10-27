module

public import CFSG.GH74.Generic.Shapes
import CFSG.RankThree.PerfectCover.HopfCentralCoversLift
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.GH74.Generic

open Subgroup CFSG CFSG.RankThree.PerfectCover

@[expose] def centralQuotientMap {K X : Type} [Group K] [Group X] (e : K ⧸ center K ≃* X) :
    K →* X :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))

theorem centralQuotientMap_surjective {K X : Type} [Group K] [Group X] (e : K ⧸ center K ≃* X) :
    Function.Surjective (centralQuotientMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem centralQuotientMap_ker {K X : Type} [Group K] [Group X] (e : K ⧸ center K ≃* X) :
    (centralQuotientMap e).ker = center K := by
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
  rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem centralQuotientMap_apply {K X : Type} [Group K] [Group X] (e : K ⧸ center K ≃* X)
    (x : K) : centralQuotientMap e x = e (QuotientGroup.mk x) := rfl

theorem card_eq_card_mul_card_ker {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : Nat.card G = Nat.card H * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

theorem card_ker_dvd_hopfMultiplier {E J : Type} [Group E] [Group J] [Finite E]
    (hE : Group.IsPerfect E) (q : E →* J) (hqs : Function.Surjective q)
    (hker : q.ker ≤ center E) : Nat.card q.ker ∣ Nat.card (hopfMultiplier J) := by
  have := hE
  set h₀ := hopfLift q hqs hker
  have hmap : (hopfMultiplier J).map h₀ = q.ker := map_hopfMultiplier_hopfLift q hqs hker
  let ψ : hopfMultiplier J →* q.ker :=
    (h₀.comp (hopfMultiplier J).subtype).codRestrict q.ker fun m => by
      rw [← hmap]
      exact ⟨m, m.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨m, hm, rfl⟩ := hc
    exact ⟨⟨m, hm⟩, rfl⟩
  exact Subgroup.card_dvd_of_surjective hψs

theorem card_center_dvd_hopfMultiplier {K X : Type} [Group K] [Group X] [Finite K]
    (hK : IsQuasisimple K) (e : K ⧸ center K ≃* X) :
    Nat.card (center K) ∣ Nat.card (hopfMultiplier X) := by
  have h1 := card_ker_dvd_hopfMultiplier hK.1 (centralQuotientMap e)
    (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
  rwa [centralQuotientMap_ker e] at h1

theorem eq_bot_of_isPGroup_two_of_odd {G : Type} [Group G] [Finite G] (h2 : IsPGroup 2 G)
    (hodd : Odd (Nat.card G)) : Subsingleton G := by
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n = 0 := by
    by_contra hne
    rw [hn] at hodd
    have : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hn0, pow_zero] at hn
  exact (Nat.card_eq_one_iff_unique.1 hn).1

theorem noTwoCover_of_odd_hopfMultiplier {X : Type} [Group X]
    (hodd : Odd (Nat.card (hopfMultiplier X))) : NoTwoCover X := by
  intro K _ _ hK hK2 ⟨e⟩
  have hdvd := card_center_dvd_hopfMultiplier hK e
  have hoddc : Odd (Nat.card (center K)) := Odd.of_dvd_nat hodd hdvd
  have := eq_bot_of_isPGroup_two_of_odd hK2 hoddc
  exact Subgroup.eq_bot_of_subsingleton _

theorem exists_lift_of_odd_index
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀] [Finite E]
    (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (p : E →* J) (hp : Function.Surjective p) (hk : p.ker ≤ center E)
    (hE2 : IsPGroup 2 p.ker) (m : ℕ) (hm : Odd m)
    (hcard : Nat.card (hopfMultiplier J) = Nat.card p₀.ker * m) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ p.comp α = p₀ :=
  CFSG.RankThree.PerfectCover.exists_lift_of_odd_index hS₀ hE p₀ hp₀ hk₀ p hp hk hE2 m hm hcard

end CFSG.GH74.Generic
