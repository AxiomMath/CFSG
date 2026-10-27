module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Gamma

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Card

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem card_Vsub_le (hb : PAB G L t E W z) (a : PA5 L t E z) :
    Nat.card ↥(Vsub t a.ub) ≤ 4 := by
  have hub2 := PA5.ub_sq a
  have htt := hb.t_mul_t
  have hsub : ((Vsub t a.ub : Subgroup G) : Set G) ⊆ ({1, t, a.ub, t * a.ub} : Set G) := by
    intro y hy
    have := (mem_Vsub_iff htt hub2 (PA5.t_ub a hb)).1 hy
    rcases this with h | h | h | h <;> simp [h]
  have h1 : Nat.card ↥(Vsub t a.ub) = ((Vsub t a.ub : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [h1]
  refine (Set.ncard_le_ncard hsub).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  have h2 := Set.ncard_insert_le t ({a.ub, t * a.ub} : Set G)
  have h3 := Set.ncard_insert_le a.ub ({t * a.ub} : Set G)
  have h4 : ({t * a.ub} : Set G).ncard = 1 := Set.ncard_singleton _
  omega

theorem card_Abar (a : PA5 L t E z) : Nat.card ↥a.Abar = 1440 := by
  rw [Nat.card_congr a.eAbar.toEquiv]
  exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6

theorem card_cent_le (hb : PAB G L t E W z) (a : PA5 L t E z) :
    Nat.card ↥(centralizer ({tG hb a} : Set ↥(Cen a.ub))) ≤ 5760 := by
  classical
  have hdec : ∀ g : ↥(centralizer ({tG hb a} : Set ↥(Cen a.ub))),
      ∃ p : ↥(Vsub t a.ub) × ↥a.Abar, (p.1 : G) * (p.2 : G) = ((g : ↥(Cen a.ub)) : G) := by
    intro g
    have h1 : ((g : ↥(Cen a.ub)) : G) * t = t * ((g : ↥(Cen a.ub)) : G) := by
      have := Subgroup.mem_centralizer_singleton_iff.1 g.2
      exact congrArg Subtype.val this
    have h2 : ((g : ↥(Cen a.ub)) : G) * a.ub = a.ub * ((g : ↥(Cen a.ub)) : G) :=
      mem_Cen.1 (g : ↥(Cen a.ub)).2
    obtain ⟨v, hv, x, hx, hvx⟩ := PA5.cent_decomp hb a h1 h2
    exact ⟨(⟨v, hv⟩, ⟨x, hx⟩), hvx.symm⟩
  choose ψ hψ using hdec
  have hinj : Function.Injective ψ := by
    intro g g' h
    have e1 := hψ g
    have e2 := hψ g'
    rw [h] at e1
    exact Subtype.ext (Subtype.ext (e1.symm.trans e2))
  have := Nat.card_le_card_of_injective ψ hinj
  rw [Nat.card_prod] at this
  have h4 := card_Vsub_le hb a
  have h5 := card_Abar a
  calc Nat.card ↥(centralizer ({tG hb a} : Set ↥(Cen a.ub)))
      ≤ Nat.card ↥(Vsub t a.ub) * Nat.card ↥a.Abar := this
    _ ≤ 4 * 1440 := by rw [h5]; exact Nat.mul_le_mul_right _ h4
    _ = 5760 := by norm_num

end Card

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
