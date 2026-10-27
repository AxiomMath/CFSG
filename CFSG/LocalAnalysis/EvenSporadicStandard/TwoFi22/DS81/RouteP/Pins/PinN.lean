module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.PinL
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.Theta
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.InterEquiv
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F10

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

structure PinN
    (G : Type) [Group G] (L E : Subgroup G) (t : G) where
  ψN : ↥(normalizer (E : Set G)) ≃* ↥Model.Zq
  map_t : ∀ ht : t ∈ normalizer (E : Set G), ((ψN ⟨t, ht⟩ : ↥Model.Zq) : Q3) = Model.t0
  mem_E : ∀ n : ↥(normalizer (E : Set G)), (n : G) ∈ E ↔ ((ψN n : ↥Model.Zq) : Q3) ∈ Model.E0
  mem_L : ∀ n : ↥(normalizer (E : Set G)), (n : G) ∈ L ↔ ((ψN n : ↥Model.Zq) : Q3) ∈ Model.B0
  mem_H : ∀ n : ↥(normalizer (E : Set G)),
    (n : G) ∈ centralizer ({t} : Set G) ↔ ((ψN n : ↥Model.Zq) : Q3) ∈ Model.Ze

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem Std.nonempty_pinN
    (h : Std G L E t) (hr : L.relIndex (centralizer ({t} : Set G)) = 2) :
    Nonempty (PinN G L E t) := by
  obtain ⟨ψL, hψE, hψN⟩ := Std.exists_pinL h hr
  obtain ⟨D⟩ := nonempty_normCocode h.m24 Model.tauM24_zero_ne_one
  have hij : Model.tauM24 0 ≠ Model.tauM24 1 := Model.tauM24_zero_ne_one
  have hA : ∀ n : ↥(normalizer (E : Set G)),
      n ∈ D.ext.Bduad (Model.tauM24 0) (Model.tauM24 1) ↔ (n : G) ∈ L :=
    fun n => (Std.mem_iff_mem_Bduad h hr D hij n).symm
  have hA₀ : ∀ n : ↥Model.Zq,
      n ∈ Model.cocodeExtension_Zq.Bduad (Model.tauM24 0) (Model.tauM24 1) ↔
        (n : Q3) ∈ Model.L0 :=
    fun n => (Model.mem_B0_iff_mem_Bduad n).symm.trans ⟨fun hb => hb.1, fun hl => ⟨hl, n.2⟩⟩
  let θ₁ := restrictSubgroupOf ψL hψN hA hA₀
  have hθ₁ : ∀ b : ↥(D.ext.Bduad (Model.tauM24 0) (Model.tauM24 1)),
      Model.cocodeExtension_Zq.toExtData.π (θ₁ b) = 1 ↔ D.ext.toExtData.π b = 1 := by
    intro b
    show Model.cocodeExtension_Zq.π (θ₁ b) = 1 ↔ D.ext.π b = 1
    rw [Model.cocodeExtension_Zq.π_eq_one_iff, D.ext.π_eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact (hψE ⟨(((b : ↥(normalizer (E : Set G))) : ↥(normalizer (E : Set G))) : G),
      (hA b).1 b.2⟩).symm
  obtain ⟨θ, hθπ, hθe⟩ := ExtData.exists_theta_duad D.ext.toExtData
    Model.cocodeExtension_Zq.toExtData hij (fun n => D.ext.mem_Bduad_iff)
    (fun n => Model.cocodeExtension_Zq.mem_Bduad_iff) θ₁ hθ₁
  obtain ⟨Ψ, hΨe, hΨπ⟩ := exists_mulEquiv_of_extData_duad (X := D.ext.toExtData)
    (X₀ := Model.cocodeExtension_Zq.toExtData) hij (fun n => D.ext.mem_Bduad_iff) θ hθπ hθe
  have hΨE := D.ext.apply_eq_of_eT Model.cocodeExtension_Zq Ψ hΨe hΨπ
  have hπ : ∀ n, Model.cocodeExtension_Zq.π (Ψ n) = D.ext.π n := hΨπ
  refine ⟨⟨Ψ, fun ht => ?_, fun n => ?_, fun n => ?_, fun n => ?_⟩⟩
  · have h1 := hΨE ⟨⟨t, ht⟩, Subgroup.mem_subgroupOf.2 D.t_mem⟩
    have h2 : ((Ψ ⟨t, ht⟩ : ↥Model.Zq) : Q3) =
        (((Model.e0.symm (D.e ⟨t, D.t_mem⟩) : ↥Model.E0q) : ↥Model.Zq) : Q3) :=
      congrArg Subtype.val h1
    rw [D.e_t] at h2
    exact h2
  · rw [← Subgroup.mem_subgroupOf (H := E) (K := normalizer (E : Set G)) (h := n),
      ← D.ext.π_eq_one_iff, ← hπ n, Model.cocodeExtension_Zq.π_eq_one_iff,
      Subgroup.mem_subgroupOf]
  · rw [Std.mem_iff_mem_Bduad h hr D hij n, Model.mem_B0_iff_mem_Bduad (Ψ n),
      D.ext.mem_Bduad_iff, Model.cocodeExtension_Zq.mem_Bduad_iff, hπ n]
  · rw [NormCocode.mem_centralizer_iff_mem_Bhat D hij n, Model.mem_Ze_iff_mem_Bhat (Ψ n),
      D.ext.mem_Bhat_iff, Model.cocodeExtension_Zq.mem_Bhat_iff, hπ n]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
