module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocBase
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporM12J2

public section

namespace CFSG.ComponentClassification.GSThmB.Soc

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal] {α : G} {J : Subgroup G}

namespace Hyp

theorem false_of_not_dvd (h : Hyp N α J)
    (hN : ¬ 20160 ∣ Nat.card N) : False :=
  hN h.dvd_card_N

theorem false_of_J1
    (h : Hyp N α J) (hs : Blueprint.NativeSporadic.IsSporadic N .J1) : False := by
  obtain ⟨e⟩ := hs
  apply h.false_of_not_dvd
  rw [Nat.card_congr e.toEquiv,
    show Nat.card (Blueprint.NativeSporadic.Carrier .J1) = Nat.card Blueprint.NativeSporadic.J1
      from rfl, Sporadic.J1.card_J1]
  decide

theorem false_of_J3
    (h : Hyp N α J) (hs : Blueprint.NativeSporadic.IsSporadic N .J3) : False := by
  obtain ⟨e⟩ := hs
  apply h.false_of_not_dvd
  rw [Nat.card_congr e.toEquiv,
    show Nat.card (Blueprint.NativeSporadic.Carrier .J3) = Nat.card Blueprint.NativeSporadic.J3
      from rfl, Sporadic.J3.card_J3]
  decide

theorem false_of_M12
    (h : Hyp N α J) (hs : Blueprint.NativeSporadic.IsSporadic N .M12) : False := by
  obtain ⟨e⟩ := hs
  apply h.false_of_not_dvd
  rw [Nat.card_congr e.toEquiv,
    show Nat.card (Blueprint.NativeSporadic.Carrier .M12) = Nat.card Blueprint.NativeSporadic.M12
      from rfl, Sporadic.Mathieu.card_M12]
  decide

theorem false_of_J2
    (h : Hyp N α J)
    (hs : Blueprint.NativeSporadic.IsSporadic N .J2) : False := by
  obtain ⟨e⟩ := hs
  let E : N ≃* J2Cover.P := e.trans J2Cover.nativeEquivP
  have hσ : orderOf (MulAut.congr E (beta N α)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h.orderOf_beta
  have hd := h.dvd_card_fixed_congr E
  have hc : Nat.card (fixedSubgroup (MulAut.congr E (beta N α))) =
      Nat.card {x : J2Cover.P // MulAut.congr E (beta N α) x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [hc] at hd
  rcases GH74.GLS.IVK.Proofs2.j2_fixed_card_aut _ hσ with h1 | h1 | h1 <;> rw [h1] at hd <;>
    exact absurd hd (by decide)

theorem fixSub_beta : Sporadic.Schreier.fixSub (beta N α) = fixedSubgroup (beta N α) :=
  Subgroup.ext fun _ => Iff.rfl

theorem isComponent_fixSub [Finite G] (h : Hyp N α J) :
    IsComponent ((J.subgroupOf N).subgroupOf (Sporadic.Schreier.fixSub (beta N α))) := by
  rw [fixSub_beta]
  exact h.isComponent_fixed

theorem card_quot_fixSub (h : Hyp N α J) :
    Nat.card (((J.subgroupOf N).subgroupOf (Sporadic.Schreier.fixSub (beta N α))) ⧸
      center ((J.subgroupOf N).subgroupOf (Sporadic.Schreier.fixSub (beta N α)))) = 20160 := by
  have hle : J.subgroupOf N ≤ Sporadic.Schreier.fixSub (beta N α) := by
    rw [fixSub_beta]
    exact h.le_fixed
  let e1 : ↥((J.subgroupOf N).subgroupOf (Sporadic.Schreier.fixSub (beta N α))) ≃* ↥J :=
    (subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe h.le_N)
  rw [Nat.card_congr (quotCenterCongr e1).toEquiv]
  exact h.card_quot

theorem mem_of_suz [Finite G] (h : Hyp N α J)
    (hSuzO : SolMax.SuzOuterComponentsInput)
    (hs : Blueprint.NativeSporadic.IsSporadic N .Suz) : α ∈ N := by
  by_contra hαN
  have hout : beta N α ∉ inner N := fun hi => hαN (h.mem_of_mem_inner hi)
  have hcard := hSuzO N hs (beta N α) h.beta_sq hout _ h.isComponent_fixSub
  rw [h.card_quot_fixSub] at hcard
  omega

theorem mem_of_ON [Finite G] (h : Hyp N α J)
    (hONO : SolMax.ONOuterComponentsInput)
    (hs : Blueprint.NativeSporadic.IsSporadic N .ONan) : α ∈ N := by
  by_contra hαN
  have hout : beta N α ∉ inner N := fun hi => hαN (h.mem_of_mem_inner hi)
  have hcard := hONO N hs (beta N α) h.beta_sq hout _ h.isComponent_fixSub
  rw [h.card_quot_fixSub] at hcard
  omega

end Hyp

end CFSG.ComponentClassification.GSThmB.Soc
