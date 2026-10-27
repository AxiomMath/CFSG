module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.RankThree.PerfectCover

theorem exists_lift_of_coprime_card {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀]
    [Finite E] (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E) (p₀ : S₀ →* J)
    (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ Subgroup.center S₀) (q : E →* J)
    (hq : Function.Surjective q) (hk : q.ker ≤ Subgroup.center E) {m : ℕ}
    (hcop : Nat.Coprime (Nat.card q.ker) m)
    (hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) = Nat.card p₀.ker * m) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ q.comp α = p₀ := by
  have : Finite J := Finite.of_surjective p₀ hp₀
  have : Finite (hopfMultiplier J) := finite_hopfMultiplier (Group.IsPerfect.ofSurjective hp₀)
  set h₀ := hopfLift p₀ hp₀ hk₀
  set h := hopfLift q hq hk
  have h₀s : Function.Surjective h₀ := hopfLift_surjective p₀ hp₀ hk₀
  have hs : Function.Surjective h := hopfLift_surjective q hq hk
  have hcomp₀ : ∀ u, p₀ (h₀ u) = hopfCoverMap J u := DFunLike.congr_fun (comp_hopfLift p₀ hp₀ hk₀)
  have hcomp : ∀ u, q (h u) = hopfCoverMap J u := DFunLike.congr_fun (comp_hopfLift q hq hk)
  have hkerM : h₀.ker ≤ hopfMultiplier J := fun u hu => by
    rw [MonoidHom.mem_ker, ← hcomp₀, MonoidHom.mem_ker.1 hu, map_one]
  have hcardk : Nat.card h₀.ker = m := by
    let ψ : hopfMultiplier J →* p₀.ker :=
      (h₀.comp (hopfMultiplier J).subtype).codRestrict p₀.ker fun x => by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hcomp₀]
        exact x.2
    have hψs : Function.Surjective ψ := by
      rintro ⟨c, hc⟩
      rw [← map_hopfMultiplier_hopfLift p₀ hp₀ hk₀] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨⟨x, hx⟩, rfl⟩
    have hψk : ψ.ker = h₀.ker.subgroupOf (hopfMultiplier J) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩
    have h1 := Subgroup.card_ker_mul_card_of_surjective hψs
    rw [hψk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerM).toEquiv, hcard,
      mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hle : h₀.ker ≤ h.ker := by
    intro u hu
    have h1 : orderOf (h u) ∣ m :=
      hcardk ▸ (orderOf_map_dvd h u).trans (Subgroup.orderOf_dvd_natCard h₀.ker hu)
    have hhu : h u ∈ q.ker := by
      rw [MonoidHom.mem_ker, hcomp, ← hcomp₀, MonoidHom.mem_ker.1 hu, map_one]
    have h2 : orderOf (h u) ∣ Nat.card q.ker := Subgroup.orderOf_dvd_natCard q.ker hhu
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  let α : S₀ →* E := (h₀.liftOfRightInverse (Function.surjInv h₀s)
    (Function.rightInverse_surjInv h₀s)) ⟨h, hle⟩
  have hα : ∀ u, α (h₀ u) = h u := fun u =>
    h₀.liftOfRightInverse_comp_apply (Function.surjInv h₀s) (Function.rightInverse_surjInv h₀s)
      ⟨h, hle⟩ u
  refine ⟨α, fun y => ?_, MonoidHom.ext fun x => ?_⟩
  · obtain ⟨u, rfl⟩ := hs y
    exact ⟨h₀ u, hα u⟩
  · obtain ⟨u, rfl⟩ := h₀s x
    rw [MonoidHom.comp_apply, hα, hcomp, hcomp₀]

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
