module

import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Comp
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4a
import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Core
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18
public import CFSG.GH74.GLS.Stage2.Local.Basic
import CFSG.Assembly.ComponentTypeDefs
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

structure CtxFacts {G : Type} [Group G] [Finite G] (z : G) (M E : Subgroup G) (p : ℕ) :
    Prop where
  hMz : M = centralizer ({z} : Set G)
  hz2' : orderOf z = 2
  hz2 : z * z = 1
  hp : p.Prime
  hp2 : p ≠ 2
  hMc : IsCoatom M
  hsimple : IsSimpleGroup G
  hzV : z ∈ Vof M E
  hVle : Vof M E ≤ M
  hZP : omega1Z p (Op p M) ≤ Op p M
  hZV : omega1Z p (Op p M) ≤ Vof M E
  hZodd : ∀ x ∈ omega1Z p (Op p M), Odd (orderOf x)
  hMZ : M ≤ normalizer ((omega1Z p (Op p M) : Subgroup G) : Set G)
  hZbot : omega1Z p (Op p M) ≠ ⊥
  hNZ : normalizer ((omega1Z p (Op p M) : Subgroup G) : Set G) = M
  hEO : E ≤ pPrimeCoreOf 2 (Vof M E)
  hZO : omega1Z p (Op p M) ≤ pPrimeCoreOf 2 (Vof M E)

section Nilp

variable {G : Type} [Group G] [Finite G]

theorem isNilpotent_of_le_Fm {M V : Subgroup G} (h : V ≤ Fm M) : Group.IsNilpotent ↥V := by
  have : Group.IsNilpotent ↥(Fm M) := Final.Thm6.L20.Fm_isNilpotent M
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h)

theorem le_Op_of_pow_eq_one {F A : Subgroup G} (hF : Group.IsNilpotent ↥F) {r : ℕ}
    (hr : r.Prime) (hAF : A ≤ F) (hA : ∀ a ∈ A, a ^ r = 1) : A ≤ Op r F := by
  have : Fact r.Prime := ⟨hr⟩
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact (Op r F).one_mem
  · exact Final.Thm6.L20.mem_Op_of_orderOf_prime hF (hAF ha) (orderOf_eq_prime (hA a ha) ha1)

end Nilp

theorem CtxFacts.of_ctx (h171 : Prop17_1) {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) :
    CtxFacts z M E p := by
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have hMz : M = centralizer ({z} : Set G) := (h171 G z k S M hctx.base.ctx hctx.base.fail).1
  have hz2' : orderOf z = 2 := hS2.orderOf_z
  have hz2 : z * z = 1 := by
    have : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hz2')
    simpa [pow_two] using this
  have hp : p.Prime := hctx.prime
  have hMc : IsCoatom M := hctx.base.ctx.mem.1
  have hsimple : IsSimpleGroup G := hctx.base.ctx.ctx.std.kps.1
  have hzV : z ∈ Vof M E := P2S4a.z_mem_Vof hMz hz2' hctx.E_le
  have hVle : Vof M E ≤ M := inf_le_left.trans (Fm_le M)
  have hZP : omega1Z p (Op p M) ≤ Op p M := omega1Z_le p _
  have hZV : omega1Z p (Op p M) ≤ Vof M E := by
    intro x hx
    refine ⟨Op_le_Fm p hp M (hZP hx), Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    exact (hx.2.1 e (hctx.E_le he)).symm
  have hZodd : ∀ x ∈ omega1Z p (Op p M), Odd (orderOf x) := by
    intro x hx
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx.2.2
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hp.odd_of_ne_two hctx.odd
  have hMZ : M ≤ normalizer ((omega1Z p (Op p M) : Subgroup G) : Set G) := fun m hm =>
    mem_normalizer_of_forall_conj fun x hx => omega1Z_conj_mem (le_normalizer_Op p M hm) hx
  have ht1 : t ≠ 1 := by
    intro h
    have := hctx.t_ord
    rw [h, orderOf_one] at this
    exact hp.one_lt.ne this
  have hZbot : omega1Z p (Op p M) ≠ ⊥ :=
    omega1Z_ne_bot hp (isPGroup_Op p hp M) hctx.t_mem ht1
  have hZtop : omega1Z p (Op p M) ≠ ⊤ := by
    intro h
    apply hMc.1
    have : (⊤ : Subgroup G) ≤ M := h ▸ (hZP.trans (Op_le p M))
    exact top_le_iff.mp this
  have hNZ := normalizer_eq_of_coatom hsimple hMc hZbot hZtop hMZ
  have hVnil : Group.IsNilpotent ↥(Vof M E) := isNilpotent_of_le_Fm inf_le_left
  have hEV : E ≤ Vof M E := by
    refine le_inf (hctx.E_le.trans (Op_le_Fm p hp M)) ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val
      ((hctx.E_elem.toIsMulCommutative.is_comm).comm (⟨g, hg⟩ : ↥E) ⟨e, he⟩)
  have hEO : E ≤ pPrimeCoreOf 2 (Vof M E) := by
    refine (le_Op_of_pow_eq_one hVnil hp hEV fun a ha => ?_).trans
      (Final.Thm6.L20.Op_le_pPrimeCoreOf _ p hp hctx.odd)
    have := hctx.E_elem
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) a ha
  have hZO : omega1Z p (Op p M) ≤ pPrimeCoreOf 2 (Vof M E) :=
    (le_Op_of_pow_eq_one hVnil hp hZV fun a ha => ha.2.2).trans
      (Final.Thm6.L20.Op_le_pPrimeCoreOf _ p hp hctx.odd)
  exact ⟨hMz, hz2', hz2, hp, hctx.odd, hMc, hsimple, hzV, hVle, hZP, hZV, hZodd, hMZ, hZbot, hNZ,
    hEO, hZO⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4
