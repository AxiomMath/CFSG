module

public import CFSG.RankThree.PerfectCover.HopfCover
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public noncomputable section

namespace CFSG.Quasithin.B69K.OddCovers

open Subgroup CFSG.RankThree.PerfectCover

theorem exists_lift_of_coprime_index
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀] [Finite E]
    (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (p : E →* J) (hp : Function.Surjective p) (hk : p.ker ≤ center E)
    {r : ℕ} (hr : r.Prime) (hE2 : IsPGroup r p.ker) (m : ℕ) (hm : Nat.Coprime r m)
    (hcard : Nat.card (hopfMultiplier J) = Nat.card p₀.ker * m) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ p.comp α = p₀ := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by
    rintro rfl
    exact hr.one_lt.ne' ((Nat.coprime_zero_right r).1 hm))
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
    obtain ⟨k, hk2⟩ := hE2 ⟨h u, hhu⟩
    have hcop : Nat.Coprime (r ^ k) m := Nat.Coprime.pow_left _ hm
    have h1 : (⟨h u, hhu⟩ : p.ker) = 1 := by
      have hp1 : (⟨h u, hhu⟩ : p.ker) ^ (r ^ k) = 1 := hk2
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

theorem card_center_dvd_hopfMultiplier {L X : Type} [Group L] [Finite L] [Group X]
    (hL : Group.IsPerfect L) (e : L ⧸ center L ≃* X) :
    Nat.card (center L) ∣ Nat.card (hopfMultiplier X) := by
  let q := centralQuotientMap e
  have hq : Function.Surjective q := centralQuotientMap_surjective e
  have hk : q.ker = center L := centralQuotientMap_ker e
  have : Finite X := finite_of_surjective_monoidHom q hq
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := q) hq
  let ψ : hopfMultiplier X →* q.ker := hopfMultiplierToKer q hq hk.le
  have hψ : Function.Surjective ψ := hopfMultiplierToKer_surjective q hq hk.le
  have h1 : Nat.card q.ker ∣ Nat.card (hopfMultiplier X) := Subgroup.card_dvd_of_surjective hψ
  rwa [hk] at h1

theorem mulEquiv_of_lift {S₀ E : Type} [Group S₀] [Group E] [Finite S₀] [Finite E] (α : S₀ →* E)
    (hα : Function.Surjective α) (hcard : Nat.card S₀ = Nat.card E) : Nonempty (S₀ ≃* E) :=
  ⟨MulEquiv.ofBijective α ((Nat.bijective_iff_surjective_and_card α).mpr ⟨hα, hcard⟩)⟩

end CFSG.Quasithin.B69K.OddCovers
