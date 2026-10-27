module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.PCentralLayer
public import CFSG.Open.GLADefs
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC

public section

namespace CFSG.HardMathSupport.Dickson.I271.PCentralLayer

open CFSG.Open Subgroup

theorem pPrimeCore_eq_bot_of_glaPPrimeCoreOf {G : Type*} [Group G] {p : ℕ} {C : Subgroup G}
    (hO : GLAPPrimeCoreOf p C = ⊥) : CFSG.pPrimeCore p ↥C = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hO

theorem exists_component_dvd_card_center_of_glaPComponent {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {C : Subgroup G} {z : G} (hzC : z ∈ C)
    (hcent : ∀ g ∈ C, g * z = z * g) (hzo : orderOf z = p) {P : Subgroup G} (hPC : P ≤ C)
    (hP : Nat.card P = p ^ (Nat.card C).factorization p)
    (hZ : ∀ c ∈ P, (∀ g ∈ P, c * g = g * c) → c ∈ zpowers z)
    (hO : GLAPPrimeCoreOf p C = ⊥) {J : Subgroup G} (hJ : GLAPComponent p C J) :
    ∃ K : Subgroup ↥C, CFSG.IsComponent K ∧ p ∣ Nat.card (center K) := by
  have hJC : J ≤ C := hJ.1
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_glaPComponent_of_comm hp hJ
      (fun g _ o ho => by
        rw [hO, Subgroup.mem_bot] at ho
        rw [ho, one_mul, mul_one])
  have hcomp : CFSG.Assembly.IsComponentOf J C :=
    CFSG.Assembly.isComponentOf_iff_open.2 ⟨hJC, hJ.2.1, hJq⟩
  have hK : CFSG.IsComponent (J.subgroupOf C) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJC).1 hcomp
  have hzo' : orderOf (⟨z, hzC⟩ : C) = p := (Subgroup.orderOf_mk z hzC).trans hzo
  have hzc : (⟨z, hzC⟩ : C) ∈ center C :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcent g g.2)
  have hP' : Nat.card (P.subgroupOf C) = p ^ (Nat.card C).factorization p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv).trans hP
  have hZ' : ∀ c ∈ P.subgroupOf C, (∀ g ∈ P.subgroupOf C, c * g = g * c) →
      c ∈ zpowers (⟨z, hzC⟩ : C) := by
    intro c hc hcomm
    have hcP : (c : G) ∈ P := hc
    have h1 := hZ (c : G) hcP fun g hg =>
      congrArg Subtype.val (hcomm ⟨g, hPC hg⟩ (show (⟨g, hPC hg⟩ : C) ∈ P.subgroupOf C from hg))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
  exact exists_component_dvd_card_center hp hzo' hzc hP' hZ'
    (pPrimeCore_eq_bot_of_glaPPrimeCoreOf hO) hK

end CFSG.HardMathSupport.Dickson.I271.PCentralLayer
