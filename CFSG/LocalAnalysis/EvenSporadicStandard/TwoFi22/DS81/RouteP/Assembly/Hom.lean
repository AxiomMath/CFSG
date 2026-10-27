module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.F13
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.F14
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

variable {G : Type*} [Group G] {E : Subgroup G} {t : G}

theorem exists_hom_of_pins
    (P : Pins G E t) :
    ∃ Φ : Q3 →* G, (∀ x : ↥Zq, Φ x = ((P.ψN.symm x : ↥(normalizer (E : Set G))) : G)) ∧
      ∀ x : ↥Ze, Φ x = ((P.ψH.symm x : ↥(centralizer ({t} : Set G))) : G) := by
  let φN : ↥Zq →* G := (normalizer (E : Set G)).subtype.comp P.ψN.symm.toMonoidHom
  let φH : ↥Ze →* G := (centralizer ({t} : Set G)).subtype.comp P.ψH.symm.toMonoidHom
  have hNH : ∀ (x : Q3) (hN : x ∈ Zq) (hH : x ∈ Ze), φN ⟨x, hN⟩ = φH ⟨x, hH⟩ := P.agree_NH
  have hNH'' : ∀ (x : Q3) (hN : x ∈ Zq) (h'' : x ∈ Ze''), φN ⟨x, hN⟩ = P.φH'' ⟨x, h''⟩ :=
    P.agree_NH''
  have hHH'' : ∀ (x : Q3) (hH : x ∈ Ze) (h'' : x ∈ Ze''), φH ⟨x, hH⟩ = P.φH'' ⟨x, h''⟩ :=
    P.agree_HH''
  let φp : ↥(L0.subgroupOf Zp) →* G :=
    φH.comp ((inclusion L0_le_Ze).comp (subgroupOfEquivOfLe L0_le_Zp).toMonoidHom)
  let φq : ↥((Zp ⊓ Zq).subgroupOf Zp) →* G :=
    φN.comp ((inclusion (inf_le_right : Zp ⊓ Zq ≤ Zq)).comp
      (subgroupOfEquivOfLe (inf_le_left : Zp ⊓ Zq ≤ Zp)).toMonoidHom)
  let φe : ↥(Y0.subgroupOf Zp) →* G :=
    P.φH''.comp ((inclusion Y0_le_Ze'').comp (subgroupOfEquivOfLe Y0_le_Zp).toMonoidHom)
  obtain ⟨Φ₁, hΦ₁p, hΦ₁q, -⟩ := AmalgamUniversal.exists_hom f13 φp φq φe
    (fun x hp hq => (hNH x (Subgroup.mem_inf.1 hq).2 (L0_le_Ze hp)).symm)
    (fun x hp he => hHH'' x (L0_le_Ze hp) (Y0_le_Ze'' he))
    (hNH'' s2 s2_mem_Zq s2_mem_Ze'')
  obtain ⟨Φ, -, hΦq, hΦe⟩ := AmalgamUniversal.exists_hom f14 Φ₁ φN φH
    (fun x hp hq => (hΦ₁q ⟨⟨x, hp⟩, Subgroup.mem_inf.2 ⟨hp, hq⟩⟩).trans rfl)
    (fun x hp he => by
      have hL : x ∈ L0 := by
        rw [← Ze_inf_stabilizer]
        exact Subgroup.mem_inf.2 ⟨he, Zp_eq_stabilizer ▸ hp⟩
      exact hΦ₁p ⟨⟨x, hp⟩, hL⟩)
    (hNH s01 s01_mem_Zq (mem_Ze_iff.2 (Or.inr ⟨s01_smul_x0, s01_smul_x1⟩)))
  exact ⟨Φ, hΦq, hΦe⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
