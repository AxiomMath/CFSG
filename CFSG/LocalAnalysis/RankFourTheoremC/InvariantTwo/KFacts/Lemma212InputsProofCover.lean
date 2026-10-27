module

public import CFSG.Open.Defs
public import CFSG.RankThree.PerfectCover.HopfCover
import CFSG.GH74.Generic.GKFCover
import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.RankThree.PerfectCover

theorem exists_lift_of_coprime_index {p : ℕ} (hp : p.Prime)
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀] [Finite E]
    (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (q : E →* J) (hq : Function.Surjective q) (hk : q.ker ≤ center E)
    (hEp : IsPGroup p q.ker) (m : ℕ) (hm : ¬ p ∣ m)
    (hcard : Nat.card (hopfMultiplier J) = Nat.card p₀.ker * m) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ q.comp α = p₀ := by
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
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exact absurd (h0 ▸ dvd_zero p) hm
      · exact h0
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
    have hcop : Nat.Coprime (p ^ k) m :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
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
    rw [MonoidHom.comp_apply, hα, ← MonoidHom.comp_apply, hcomp, ← MonoidHom.comp_apply,
      hcomp₀]

open CFSG.GH74.Generic (centralQuotientMap centralQuotientMap_apply centralQuotientMap_ker
  centralQuotientMap_surjective)

theorem exists_cover_of_card {p : ℕ} (hp : p.Prime) {L S J : Type} [Group L] [Finite L]
    [Group S] [Finite S] [Group J] (hL : CFSG.Open.IsQuasisimple L)
    (hZp : IsPGroup p (center L)) (hS : Group.IsPerfect S) (π : S →* J)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center S) (e : L ⧸ center L ≃* J)
    (hm : ∃ m : ℕ, ¬ p ∣ m ∧ Nat.card (hopfMultiplier J) = Nat.card π.ker * m) :
    ∃ φ : S →* L, Function.Surjective φ ∧ ∀ s, e (QuotientGroup.mk (φ s)) = π s := by
  obtain ⟨m, hpm, hcard⟩ := hm
  haveI : Group.IsPerfect L := ⟨hL.1⟩
  obtain ⟨α, hα, hcomp⟩ := exists_lift_of_coprime_index hp hS this π hπ hker
    (centralQuotientMap e) (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
    (by rw [centralQuotientMap_ker e]; exact hZp) m hpm hcard
  refine ⟨α, hα, fun s => ?_⟩
  have h1 := congrArg (fun f : S →* J => f s) hcomp
  simpa [centralQuotientMap_apply] using h1

theorem cover_ker_center {S L J : Type} [Group S] [Group L] [Group J] (φ : S →* L)
    (hφ : Function.Surjective φ) (π : S →* J) (e : L ⧸ center L ≃* J)
    (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s) :
    φ.ker ≤ π.ker ∧ center L ≤ π.ker.map φ := by
  refine ⟨fun s hs => ?_, fun x hx => ?_⟩
  · rw [MonoidHom.mem_ker] at hs ⊢
    rw [← hφπ, hs, QuotientGroup.mk_one, map_one]
  · obtain ⟨s, rfl⟩ := hφ x
    refine ⟨s, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hφπ, (QuotientGroup.eq_one_iff (φ s)).2 hx,
      map_one]

end CFSG.LocalAnalysis.RankFourTheoremC
