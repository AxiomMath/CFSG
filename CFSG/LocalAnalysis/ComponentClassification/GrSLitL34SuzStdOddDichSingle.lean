module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichSetup
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroSingle
import CFSG.GroupTheory.CommuteOfSqEqOne

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

section Certified


theorem isComponent_of_isComponent_map_of_l34SuzOdd
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hW : ∀ F : Subgroup G, F ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 F →
      8 ≤ Nat.card F → wGroup F = ⊥)
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    (hK : IsComponent ((K.subgroupOf (centralizer ({u} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))))) :
    IsComponent (K.subgroupOf (centralizer ({u} : Set G))) := by
  have hFK : V ⊔ zpowers t ≤ centralizer (K : Set G) :=
    (sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD).trans inf_le_right
  have hFt : V ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    (sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD).trans inf_le_left
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.orderOf_t]
    exact pow_orderOf_eq_one t
  have htV : t ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.mp hS.t_mem v (hD.le_A hv)
  have hVea : Open.IsElemAbelian 2 V := by
    have h := Open.IsElemAbelian.closure_of_commute (p := 2) (s := (V : Set G))
      (fun a ha b hb => CFSG.commute_of_sq_eq_one
        (by rw [pow_two]; exact hD.mul_self a ha)
        (by rw [pow_two]; exact hD.mul_self b hb)
        (by rw [pow_two]; exact hD.mul_self (a * b) (V.mul_mem ha hb)))
      (fun a ha => by rw [pow_two]; exact hD.mul_self a ha)
    simpa [Subgroup.closure_eq] using h
  have hFea : Open.IsElemAbelian 2 (V ⊔ zpowers t) :=
    hVea.sup_of_commute (Open.isElemAbelian_zpowers ht2) fun v hv w hw =>
      Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr htV) hw) v hv
  have hF8 : 8 ≤ Nat.card ↥(V ⊔ zpowers t) := by
    rw [card_sup_zpowers_of_l34SuzOdd hS hD]
  have huF : u ∈ V ⊔ zpowers t := Subgroup.mem_sup_left hu
  have hFu : V ⊔ zpowers t ≤ centralizer ({u} : Set G) := by
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.2 (hFea.comm hf huF)
  have hu2 : orderOf u = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨by rw [pow_two]; exact hD.mul_self u hu, hu1⟩
  exact isComponent_of_isComponent_map_of_l34 hSch hU hheld hS.base hu2
    (le_centralizer_of_l34SuzOddData hD hu) (isQuasisimple_of_l34SuzOdd hD) hK
    hFK hFu hFea hF8 (hW (V ⊔ zpowers t) hFt hFea hF8)

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S
