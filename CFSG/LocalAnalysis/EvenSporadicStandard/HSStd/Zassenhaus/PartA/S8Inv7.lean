module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Gamma

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Comm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA5.comm_mem_J (hb : PAB G L t E W z) (a : PA5 L t E z) {c c' : G} (h1 : c * t = t * c)
    (h2 : c * a.ub = a.ub * c) (h1' : c' * t = t * c') (h2' : c' * a.ub = a.ub * c') :
    ⁅c, c'⁆ ∈ derivedIn a.Abar := by
  obtain ⟨v, hv, x, hx, rfl⟩ := PA5.cent_decomp hb a h1 h2
  obtain ⟨v', hv', x', hx', rfl⟩ := PA5.cent_decomp hb a h1' h2'
  have hcx : ∀ y ∈ Vsub t a.ub, ∀ x ∈ a.Abar, y * x = x * y := fun y hy x hx =>
    (commute_Vsub (PA5.Abar_comm_t hb a hx) (PA5.Abar_comm_ub hb a hx) y hy).symm
  rw [comm_mul_mul (hcx v hv x hx) (hcx v hv x' hx') (hcx v' hv' x hx) (hcx v' hv' x' hx')]
  have h1 : ⁅v, v'⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Vsub_comm (PA5.t_ub a hb) hv hv'
  rw [h1, one_mul]
  exact derivedIn_mem_of_commutator hx hx'

@[expose] def CT (hb : PAB G L t E W z) (a : PA5 L t E z) : Subgroup ↥(Cen a.ub) :=
  centralizer ({tG hb a} : Set ↥(Cen a.ub))

theorem mem_CT (hb : PAB G L t E W z) (a : PA5 L t E z) {c : ↥(Cen a.ub)} :
    c ∈ CT hb a ↔ c * tG hb a = tG hb a * c := Subgroup.mem_centralizer_singleton_iff

theorem CT_comm_mem_J (hb : PAB G L t E W z) (a : PA5 L t E z) {c c' : ↥(Cen a.ub)}
    (hc : c ∈ CT hb a) (hc' : c' ∈ CT hb a) : ((⁅c, c'⁆ : ↥(Cen a.ub)) : G) ∈ derivedIn a.Abar := by
  have h1 : (c : G) * t = t * c := congrArg Subtype.val ((mem_CT hb a).1 hc)
  have h1' : (c' : G) * t = t * c' := congrArg Subtype.val ((mem_CT hb a).1 hc')
  have h2 : (c : G) * a.ub = a.ub * c := mem_Cen.1 c.2
  have h2' : (c' : G) * a.ub = a.ub * c' := mem_Cen.1 c'.2
  have := PA5.comm_mem_J hb a h1 h2 h1' h2'
  simpa [commutatorElement_def] using this

end Comm

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
