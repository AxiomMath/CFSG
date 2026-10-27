module

public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.SectionRank

theorem two_le_pRank_top_of_commute {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y) (hx1 : x ≠ 1)
    (hy1 : ∀ n : ℕ, x ^ n ≠ y) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  set B₀ : Subgroup G := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = p ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := exists_extend hc₀ hp₀ hcard₀ B₀.subtype
    Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, -⟩ := exists_extend hc₁ hp₁ hcard₁ F₁ hF₁ (y := y) hy
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hy1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  exact le_pRank_of_injective hp.out.one_lt hc₂ hp₂ hcard₂ F₂ hF₂ le_top

theorem pRank_le_one_of_isCyclic {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {S : Subgroup X} (hS : IsCyclic S) : CFSG.Open.pRank p S ≤ 1 := by
  refine pRank_le hp.one_lt fun E hES hE => ?_
  have : IsCyclic E :=
    isCyclic_of_injective (Subgroup.inclusion hES) (Subgroup.inclusion_injective hES)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  rw [pow_one, ← hg]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2)))

end CFSG.SectionRank
