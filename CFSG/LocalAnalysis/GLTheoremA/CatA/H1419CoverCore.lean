module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup

theorem exists_lift_of_coprime_index3
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀] [Finite E]
    (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (p : E →* J) (hp : Function.Surjective p) (hk : p.ker ≤ center E)
    (hE3 : IsPGroup 3 p.ker) (m : ℕ) (hm : Nat.Coprime 3 m)
    (hcard : Nat.card (hopfMultiplier J) = Nat.card p₀.ker * m) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ p.comp α = p₀ := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h0 => by subst h0; norm_num at hm)
  set h₀ := hopfLift p₀ hp₀ hk₀ with hh₀
  set h := hopfLift p hp hk with hh
  have h₀s : Function.Surjective h₀ := hopfLift_surjective p₀ hp₀ hk₀
  have hs : Function.Surjective h := hopfLift_surjective p hp hk
  have hcomp₀ : p₀.comp h₀ = hopfCoverMap J := comp_hopfLift p₀ hp₀ hk₀
  have hcomp : p.comp h = hopfCoverMap J := comp_hopfLift p hp hk
  have hmap₀ : (hopfMultiplier J).map h₀ = p₀.ker := map_hopfMultiplier_hopfLift p₀ hp₀ hk₀
  have hmap : (hopfMultiplier J).map h = p.ker := map_hopfMultiplier_hopfLift p hp hk
  have hker₀ : ∀ u ∈ h₀.ker, u ∈ hopfMultiplier J ∧ u ^ m = 1 := by
    let ψ : hopfMultiplier J →* p₀.ker :=
      (h₀.comp (hopfMultiplier J).subtype).codRestrict p₀.ker fun x ↦ by
        rw [← hmap₀]
        exact ⟨x, x.2, rfl⟩
    have hψs : Function.Surjective ψ := by
      rintro ⟨c, hc⟩
      rw [← hmap₀] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfin : Finite (hopfMultiplier J) := Nat.finite_of_card_ne_zero (by
      rw [hcard]
      exact (Nat.mul_pos Nat.card_pos hm0).ne')
    have hcardk : Nat.card ψ.ker * Nat.card p₀.ker = Nat.card (hopfMultiplier J) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv] at h1
      rw [mul_comm]
      exact h1.symm
    have hkm : Nat.card ψ.ker = m := by
      have hpos : 0 < Nat.card p₀.ker := Nat.card_pos
      have h2 : Nat.card ψ.ker * Nat.card p₀.ker = m * Nat.card p₀.ker := by
        rw [hcardk, hcard, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hpos h2
    intro u hu
    have hu0 : p₀ (h₀ u) = 1 := by rw [MonoidHom.mem_ker.1 hu, map_one]
    have hum : u ∈ hopfMultiplier J := by
      change hopfCoverMap J u = 1
      rw [← hcomp₀, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hu, map_one]
    refine ⟨hum, ?_⟩
    have hψu : ψ ⟨u, hum⟩ = 1 := Subtype.ext (MonoidHom.mem_ker.1 hu)
    have hmem : (⟨u, hum⟩ : hopfMultiplier J) ∈ ψ.ker := hψu
    have := orderOf_dvd_natCard (⟨⟨u, hum⟩, hmem⟩ : ψ.ker)
    rw [hkm] at this
    have h3 : (⟨⟨u, hum⟩, hmem⟩ : ψ.ker) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.1 this
    exact congrArg (fun z : ψ.ker ↦ ((z : hopfMultiplier J) : HopfCover J)) h3
  have hle : h₀.ker ≤ h.ker := by
    intro u hu
    obtain ⟨hum, hu3⟩ := hker₀ u hu
    rw [MonoidHom.mem_ker]
    have hhu : h u ∈ p.ker := by
      rw [← hmap]
      exact ⟨u, hum, rfl⟩
    have hpow : (⟨h u, hhu⟩ : p.ker) ^ m = 1 := Subtype.ext (by
      change (h u) ^ m = 1
      rw [← map_pow, hu3, map_one])
    obtain ⟨k, hk2⟩ := hE3 ⟨h u, hhu⟩
    have hcop : Nat.Coprime (3 ^ k) m := Nat.Coprime.pow_left _ hm
    have h1 : (⟨h u, hhu⟩ : p.ker) = 1 := by
      have hp1 : (⟨h u, hhu⟩ : p.ker) ^ (3 ^ k) = 1 := hk2
      have := (pow_gcd_eq_one (a := (⟨h u, hhu⟩ : p.ker))).2 ⟨hp1, hpow⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
    exact congrArg Subtype.val h1
  let α : S₀ →* E := (h₀.liftOfRightInverse (Function.surjInv h₀s)
    (Function.rightInverse_surjInv h₀s)) ⟨h, hle⟩
  have hα : ∀ u, α (h₀ u) = h u := fun u ↦
    h₀.liftOfRightInverse_comp_apply (Function.surjInv h₀s) (Function.rightInverse_surjInv h₀s)
      ⟨h, hle⟩ u
  refine ⟨α, ?_, ?_⟩
  · intro e
    obtain ⟨u, rfl⟩ := hs e
    exact ⟨h₀ u, hα u⟩
  · refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨u, rfl⟩ := h₀s x
    rw [MonoidHom.comp_apply, hα, ← MonoidHom.comp_apply, hcomp, ← MonoidHom.comp_apply, hcomp₀]

theorem unique_three_cover {C₁ C₂ L : Type} [Group C₁] [Group C₂] [Group L] [Finite C₁] [Finite C₂]
    (h₁ : Group.IsPerfect C₁) (h₂ : Group.IsPerfect C₂)
    (q₁ : C₁ →* L) (hq₁ : Function.Surjective q₁) (hk₁ : q₁.ker ≤ center C₁)
    (q₂ : C₂ →* L) (hq₂ : Function.Surjective q₂) (hk₂ : q₂.ker ≤ center C₂)
    (hc₁ : Nat.card q₁.ker = 3) (hc₂ : Nat.card q₂.ker = 3)
    (hM : ¬ 9 ∣ Nat.card (hopfMultiplier L)) : Nonempty (C₁ ≃* C₂) := by
  haveI : Finite L := Finite.of_surjective q₁ hq₁
  let ψ : hopfMultiplier L →* q₁.ker :=
    hopfMultiplierToKer q₁ hq₁ hk₁
  have hψ : Function.Surjective ψ := hopfMultiplierToKer_surjective q₁ hq₁ hk₁
  have hMc : Nat.card (hopfMultiplier L) = Nat.card q₁.ker * Nat.card ψ.ker :=
    card_eq_card_mul_card_ker ψ hψ
  set m := Nat.card ψ.ker with hm_def
  have hcardM : Nat.card (hopfMultiplier L) = Nat.card q₁.ker * m := hMc
  have hm3 : Nat.Coprime 3 m := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    rintro ⟨t, ht⟩
    apply hM
    rw [hcardM, hc₁, ht]
    exact ⟨t, by ring⟩
  have hE3 : IsPGroup 3 q₂.ker := IsPGroup.of_card (n := 1) (by rw [hc₂, pow_one])
  obtain ⟨α, hα, hcomp⟩ := exists_lift_of_coprime_index3 h₁ h₂ q₁ hq₁ hk₁ q₂ hq₂ hk₂ hE3 m hm3
    hcardM
  have hcards : Nat.card C₁ = Nat.card C₂ := by
    rw [card_eq_card_mul_card_ker q₁ hq₁, card_eq_card_mul_card_ker q₂ hq₂, hc₁, hc₂]
  exact ⟨MulEquiv.ofBijective α ((Nat.bijective_iff_surjective_and_card α).mpr ⟨hα, hcards⟩)⟩

theorem isPGroup_three_center_of_pPrimeCore_eq_bot {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 3 X = ⊥) : IsPGroup 3 (center X) := by
  intro g
  have hz : (g : X) ∈ center X := g.2
  set z : X := (g : X) with hzdef
  have hzpos : orderOf z ≠ 0 := (orderOf_pos z).ne'
  have hpow : orderOf z = 3 ^ (orderOf z).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hzpos
    intro d hd hdvd
    by_contra hne
    have hdne : d ≠ 3 := hne
    set w : X := z ^ (orderOf z / d) with hwdef
    have hw_ord : orderOf w = d := orderOf_pow_orderOf_div hzpos hdvd
    have hwc : w ∈ center X := (center X).pow_mem hz _
    have hnorm : (Subgroup.zpowers w).Normal := by
      constructor
      intro n hn g'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hc : Commute g' w := Subgroup.mem_center_iff.1 hwc g'
      have : g' * w ^ k * g'⁻¹ = w ^ k := by
        rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      rw [this]
      exact hn
    have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers w)) := by
      rw [Nat.card_zpowers, hw_ord]
      exact (Nat.coprime_primes Nat.prime_three hd).2 (Ne.symm hdne)
    have hle : Subgroup.zpowers w ≤ CFSG.pPrimeCore 3 X :=
      le_sSup ⟨hnorm, hcop⟩
    rw [hO] at hle
    have hw1 : w = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers w))
    rw [hw1, orderOf_one] at hw_ord
    exact hd.one_lt.ne' hw_ord.symm
  refine ⟨(orderOf z).primeFactorsList.length, ?_⟩
  have : z ^ (3 ^ (orderOf z).primeFactorsList.length) = 1 := by
    rw [← hpow]
    exact pow_orderOf_eq_one z
  exact Subtype.ext this

theorem card_center_dvd_hopf {C : Type} [Group C] [Finite C] (hC : Group.IsPerfect C) :
    Nat.card (center C) ∣ Nat.card (hopfMultiplier (C ⧸ center C)) := by
  let q : C →* C ⧸ center C := QuotientGroup.mk' (center C)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = center C := QuotientGroup.ker_mk' _
  have hkc : q.ker ≤ center C := hk.le
  let ψ : hopfMultiplier (C ⧸ center C) →* q.ker := hopfMultiplierToKer q hq hkc
  have hψ : Function.Surjective ψ := hopfMultiplierToKer_surjective q hq hkc
  have h := card_eq_card_mul_card_ker ψ hψ
  have hcenter : Nat.card (center C) = Nat.card q.ker := by rw [hk]
  refine ⟨Nat.card ψ.ker, ?_⟩
  rw [hcenter]
  exact h

end CFSG.RankThree.PerfectCover
