module

public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Subgroup CFSG.RankThree.PerfectCover

theorem exists_lift_of_coprime_index {p : ℕ} [Fact p.Prime]
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀] [Finite E]
    (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (q : E →* J) (hq : Function.Surjective q) (hk : q.ker ≤ center E)
    (hEp : IsPGroup p q.ker) (m : ℕ) (hm : Nat.Coprime m p)
    (hcard : Nat.card (hopfMultiplier J) = Nat.card p₀.ker * m) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ q.comp α = p₀ := by
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have h1 : p = 1 := (Nat.coprime_zero_left p).1 hm
      have h2 := (Fact.out : p.Prime).one_lt
      omega
    · exact h0
  set h₀ := hopfLift p₀ hp₀ hk₀ with hh₀
  set h := hopfLift q hq hk with hh
  have h₀s : Function.Surjective h₀ := hopfLift_surjective p₀ hp₀ hk₀
  have hs : Function.Surjective h := hopfLift_surjective q hq hk
  have hcomp₀ : p₀.comp h₀ = hopfCoverMap J := comp_hopfLift p₀ hp₀ hk₀
  have hcomp : q.comp h = hopfCoverMap J := comp_hopfLift q hq hk
  have hmap₀ : (hopfMultiplier J).map h₀ = p₀.ker := map_hopfMultiplier_hopfLift p₀ hp₀ hk₀
  have hmap : (hopfMultiplier J).map h = q.ker := map_hopfMultiplier_hopfLift q hq hk
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
      exact (Nat.mul_pos Nat.card_pos hmpos).ne')
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
    have hhu : h u ∈ q.ker := by
      rw [← hmap]
      exact ⟨u, hum, rfl⟩
    have hpow : (⟨h u, hhu⟩ : q.ker) ^ m = 1 := Subtype.ext (by
      change (h u) ^ m = 1
      rw [← map_pow, hu3, map_one])
    obtain ⟨k, hk2⟩ := hEp ⟨h u, hhu⟩
    have hcop : Nat.Coprime (p ^ k) m := Nat.Coprime.pow_left _ (Nat.Coprime.symm hm)
    have h1 : (⟨h u, hhu⟩ : q.ker) = 1 := by
      have hp1 : (⟨h u, hhu⟩ : q.ker) ^ (p ^ k) = 1 := hk2
      have := (pow_gcd_eq_one (a := (⟨h u, hhu⟩ : q.ker))).2 ⟨hp1, hpow⟩
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

end CFSG.HardMathSupport.Solomon.Proving

end
