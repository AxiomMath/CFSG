module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.PinN
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F10Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F11Rigid
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Extension

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem Std.exists_pinH
    (h : Std G L E t) (hr : L.relIndex (centralizer ({t} : Set G)) = 2) (P : PinN G L E t) :
    ∃ ψH : ↥(centralizer ({t} : Set G)) ≃* ↥Model.Ze,
      ∀ (x : Q3) (hN : x ∈ Model.Zq) (hH : x ∈ Model.Ze),
        ((P.ψN.symm ⟨x, hN⟩ : ↥(normalizer (E : Set G))) : G) =
          ((ψH.symm ⟨x, hH⟩ : ↥(centralizer ({t} : Set G))) : G) := by
  obtain ⟨ψL, -, hψN⟩ := Std.exists_pinL h hr
  have hψNL : ∀ y : ↥(normalizer (E : Set G)),
      (y : G) ∈ L ↔ ((P.ψN y : ↥Model.Zq) : Q3) ∈ Model.L0 := fun y =>
    (P.mem_L y).trans ⟨fun hb => hb.1, fun hl => ⟨hl, (P.ψN y).2⟩⟩
  obtain ⟨c, -, hcZe, hc⟩ := Model.f10_conj (interAut ψL P.ψN hψN hψNL)
  have hc' : ∀ (n : ↥(normalizer (E : Set G))) (hnL : (n : G) ∈ L),
      ((ψL ⟨(n : G), hnL⟩ : ↥Model.L0) : Q3) = c * ((P.ψN n : ↥Model.Zq) : Q3) * c⁻¹ := by
    intro n hnL
    have hb : ((P.ψN n : ↥Model.Zq) : Q3) ∈ Model.L0 ⊓ Model.Zq :=
      ⟨(hψNL n).1 hnL, (P.ψN n).2⟩
    rw [← interAut_apply ψL P.ψN hψN hψNL ⟨_, hb⟩ n hnL rfl]
    exact hc ⟨_, hb⟩
  have hg : ∀ k ∈ Model.L0, c⁻¹ * k * c⁻¹⁻¹ ∈ Model.L0 := fun k hk =>
    Model.conj_mem_L0_of_mem_Ze (Model.Ze.inv_mem hcZe) hk
  have hg' : ∀ k ∈ Model.L0, c⁻¹⁻¹ * k * c⁻¹ ∈ Model.L0 := fun k hk => by
    rw [inv_inv]
    exact Model.conj_mem_L0_of_mem_Ze hcZe hk
  let ψL' : ↥L ≃* ↥Model.L0 := ψL.trans (conjAut Model.L0 c⁻¹ hg hg')
  have key : ∀ (n : ↥(normalizer (E : Set G))) (hnL : (n : G) ∈ L),
      ((ψL' ⟨(n : G), hnL⟩ : ↥Model.L0) : Q3) = ((P.ψN n : ↥Model.Zq) : Q3) := by
    intro n hnL
    show c⁻¹ * ((ψL ⟨(n : G), hnL⟩ : ↥Model.L0) : Q3) * c⁻¹⁻¹ = _
    rw [hc' n hnL]
    simp [mul_assoc]
  let C : Subgroup G := normalizer (E : Set G) ⊓ centralizer ({t} : Set G)
  have hLH : L ≤ centralizer ({t} : Set G) := h.facts.le_centralizer
  have hCH : C ≤ centralizer ({t} : Set G) := inf_le_right
  have hHLC : L ⊔ C = centralizer ({t} : Set G) := by
    refine le_antisymm (sup_le hLH hCH) fun x hx => ?_
    obtain ⟨l, hl, n, hn, rfl⟩ := h.facts.exists_eq_mul hx
    refine mul_mem_sup hl ⟨hn, ?_⟩
    simpa using (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).inv_mem (hLH hl)) hx
  have hLn : (L.subgroupOf (centralizer ({t} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLH]
    intro l k hl hk
    exact (Subgroup.mem_normalizer_iff.1 (h.facts.centralizer_le hk) l).1 hl
  have hL₀n : (Model.L0.subgroupOf Model.Ze).Normal := by
    rw [Subgroup.normal_subgroupOf_iff Model.L0_le_Ze]
    intro k z hk hz
    exact Model.conj_mem_L0_of_mem_Ze hz hk
  let ψC : ↥C →* ↥Model.Ze :=
    ((Model.Zq.subtype.comp (P.ψN : ↥(normalizer (E : Set G)) →* ↥Model.Zq)).comp
      (Subgroup.inclusion (inf_le_left : C ≤ normalizer (E : Set G)))).codRestrict Model.Ze
      (fun x => (P.mem_H ⟨(x : G), x.2.1⟩).1 x.2.2)
  have hagree : ∀ (x : G) (hxL : x ∈ L) (hxC : x ∈ C),
      Subgroup.inclusion Model.L0_le_Ze (ψL' ⟨x, hxL⟩) = ψC ⟨x, hxC⟩ := fun x hxL hxC =>
    Subtype.ext (key ⟨x, hxC.1⟩ hxL)
  have hrigid : ∀ α : ↥Model.L0 ≃* ↥Model.L0,
      (∀ (b : G) (hbL : b ∈ L), b ∈ C → α (ψL' ⟨b, hbL⟩) = ψL' ⟨b, hbL⟩) →
        α = MulEquiv.refl _ := by
    intro α hα
    refine Model.f11 α fun b hb => ?_
    set n : ↥(normalizer (E : Set G)) := P.ψN.symm ⟨(b : Q3), Model.B0_le_Zq hb⟩
    have hnb : ((P.ψN n : ↥Model.Zq) : Q3) = (b : Q3) :=
      congrArg Subtype.val (P.ψN.apply_symm_apply ⟨(b : Q3), Model.B0_le_Zq hb⟩)
    have hnL : (n : G) ∈ L := (P.mem_L n).2 (by rw [hnb]; exact hb)
    have h1 := hα (n : G) hnL ⟨n.2, h.facts.le_centralizer hnL⟩
    have h2 : ψL' ⟨(n : G), hnL⟩ = b := Subtype.ext ((key n hnL).trans hnb)
    rwa [h2] at h1
  have hψCL : ∀ x : ↥C, ((ψC x : ↥Model.Ze) : Q3) ∈ Model.L0 → (x : G) ∈ L := fun x hx =>
    (P.mem_L ⟨(x : G), x.2.1⟩).2 ⟨hx, (P.ψN ⟨(x : G), x.2.1⟩).2⟩
  have hcard : Nat.card ↥(centralizer ({t} : Set G)) = Nat.card ↥Model.Ze := by
    have h1 := Subgroup.relIndex_mul_card (H := L) (K := centralizer ({t} : Set G))
    rw [hr, inf_eq_left.2 hLH] at h1
    rw [← h1, Model.card_Ze, Nat.card_congr ψL'.toEquiv]
  haveI : Finite Q3 := Finite.of_injective Model.rho Model.rho_injective
  obtain ⟨ψH, -, hψH⟩ := exists_mulEquiv_of_sup_eq_of_card_eq hLH hCH hHLC hLn Model.L0_le_Ze hL₀n
    ψL' ψC hagree hrigid hψCL hcard
  refine ⟨ψH, fun x hN hH => ?_⟩
  set n : ↥(normalizer (E : Set G)) := P.ψN.symm ⟨x, hN⟩
  have hnx : ((P.ψN n : ↥Model.Zq) : Q3) = x :=
    congrArg Subtype.val (P.ψN.apply_symm_apply ⟨x, hN⟩)
  have hnH : (n : G) ∈ centralizer ({t} : Set G) := (P.mem_H n).2 (by rw [hnx]; exact hH)
  have hnC : (n : G) ∈ C := ⟨n.2, hnH⟩
  have h2 : ψH.symm ⟨x, hH⟩ = Subgroup.inclusion hCH ⟨(n : G), hnC⟩ := by
    rw [MulEquiv.symm_apply_eq, hψH ⟨(n : G), hnC⟩]
    exact Subtype.ext hnx.symm
  rw [h2]
  rfl

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
