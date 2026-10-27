module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitLift
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitConeMat
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitLayer

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

theorem eq_of_add_eq_zero2' {v w : V6} (h : v + w = 0) : v = w := by
  calc v = v + w + w := by rw [add_assoc, v6_add_self, add_zero]
    _ = w := by rw [h, zero_add]

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {k : ℕ} {A : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) k A) (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
include hS hC hinv

theorem mem_At_of_affX [Finite G] {y₁ y₂ : G}
    (h₁ : y₁ ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G))
    (h₂ : y₂ ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G))
    (hc : cOf ψ t k y₁ = cOf ψ t k y₂) (hl : ∀ v, lin ψ y₁ v = lin ψ y₂ v) :
    y₂⁻¹ * y₁ ∈ A ⊔ zpowers t := by
  have hR := hS.rad
  have hN₁ := hC.normalizes_QX hS hinv h₁
  have hN₂ := hC.normalizes_QX hS hinv h₂
  have hlin : ∀ v, lin ψ (y₂⁻¹ * y₁) v = v := fun v => by
    rw [hR.lin_mul (inv_mem hN₂) hN₁, hl, hR.lin_inv' hN₂]
  have hcomm : ∀ q ∈ Q, y₂⁻¹ * y₁ * q = q * (y₂⁻¹ * y₁) := by
    intro q hq
    obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
    have h := (hR.lin_eq_iff (mul_mem (inv_mem hN₂) hN₁) v v).1 (hlin v)
    calc y₂⁻¹ * y₁ * ψ v = y₂⁻¹ * y₁ * ψ v * (y₂⁻¹ * y₁)⁻¹ * (y₂⁻¹ * y₁) := by group
      _ = ψ v * (y₂⁻¹ * y₁) := by rw [h]
  have hinvc : cOf ψ t k y₂⁻¹ = lin ψ y₂⁻¹ (cOf ψ t k y₂) := by
    have h := hC.cOf_mulX hS hinv (inv_mem h₂) h₂
    rw [inv_mul_cancel, cOf_oneX hS] at h
    exact (eq_of_add_eq_zero2' h.symm)
  refine hC.mem_At_of_cOfX hS hinv (mem_Rsub.2 ⟨mul_mem (inv_mem h₂) h₁, hcomm⟩) ?_
  rw [hC.cOf_mulX hS hinv (inv_mem h₂) h₁, hinvc, ← hR.lin_add (inv_mem hN₂), hc,
    v6_add_self, (hR.lin_eq_iff (inv_mem hN₂) 0 0).2 (by rw [hR.ψ_zero]; group)]

theorem rep_of_mem_AtX [Finite G] {B : Subgroup G} (hBA : B ≤ A) {Φ : (Fin 6 → ZMod 4) → G}
    (hΦ : Coord4 B ψ Φ) {z : G} (hz : z ∈ A ⊔ zpowers t) :
    ∃ s : Bool, Rep Φ z (if s then -1 else 1) := by
  have hrepA : ∀ b ∈ A, Rep Φ b 1 := fun b hb v => by
    rw [one_mulVec, hC.level.comm b hb _ (hBA (hΦ.mem v)), mul_inv_cancel_right]
  have hrept : Rep Φ t (-1) := fun v => by
    rw [hinv _ (hBA (hΦ.mem v)), neg_mulVec, one_mulVec, hΦ.neg]
  obtain ⟨b, hb, hzb | hzb⟩ := hC.mem_AtX hS hz
  · exact ⟨false, hzb ▸ hrepA b hb⟩
  · refine ⟨true, ?_⟩
    have := Coord4.rep_mul (hrepA b hb) hrept
    rw [one_mul] at this
    rw [hzb]
    exact this

theorem false_of_coneX [Finite G]
    {g : G}
    (hg : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G))
    (hc : cOf ψ t k g = Pi.single 0 1) (hl : ∀ v, lin ψ g v = tauMat ε *ᵥ v) : False := by
  have hR := hS.rad
  have hk := hC.two_le
  set B := pw A (2 ^ (k - 2))
  have hB : Level Q 2 B := by
    have := hC.level_mX hS (m := k - 2) (by omega)
    rwa [show k - (k - 2) = 2 by omega] at this
  have hBA : B ≤ A := pw_le A _
  have hBP : ∀ x ∈ P, ∀ y ∈ B, x * y * x⁻¹ ∈ B := fun x hx y hy =>
    pw_conj_mem_gen hC.level.comm (hC.P_norm x (mem_sup_left hx)) hy
  obtain ⟨Φ, hΦ, hw⟩ := exists_coord_lift_of hR (fun x hx hc => hS.mem_Q_of_mem_P hx hc) hB hBP
  have hgQ := hC.normalizes_QX hS hinv hg
  obtain ⟨T, hT⟩ := hΦ.exists_rep (g := g) fun y hy =>
    pw_conj_mem_gen hC.level.comm (fun a ha => hC.conj_mem_AX hS hinv hg ha) hy
  have hTred : T.map red4 = tauMat ε :=
    hΦ.map_red4_of_rep hT hR.ψ_inj fun v => by rw [← hl, hR.ψ_lin hgQ]
  have hsq : (1 : G)⁻¹ * (g * g) ∈ A ⊔ zpowers t := by
    refine hC.mem_At_of_affX hS hinv (mul_mem hg hg) (one_mem _) ?_ fun v => ?_
    · rw [hC.cOf_mulX hS hinv hg hg, hc, hl, tauMat_e₀, v6_add_self, cOf_oneX hS]
    · rw [hR.lin_mul hgQ hgQ, hl, hl, mulVec_mulVec, tauMat_mul_self, one_mulVec, hR.lin_one]
  obtain ⟨s₀, hs₀⟩ := hC.rep_of_mem_AtX hS hinv hBA hΦ hsq
  rw [inv_one, one_mul] at hs₀
  have h2 : T * T = if s₀ then -1 else 1 := hΦ.rep_unique (Coord4.rep_mul hT hT) hs₀
  have hgen : ∀ j < 2, ∃ s : Bool, T * prodW ε (c0Mat ε) ((coneWords ε).getD j []) =
      if s then -(prodW ε (c0Mat ε) ((coneWords ε).getD j []) * T)
      else prodW ε (c0Mat ε) ((coneWords ε).getD j []) * T := by
    intro j hj
    obtain ⟨hcheck, -⟩ : coneGenCheck ε j = true ∧ True := by
      obtain ⟨-, -, h0, h1, -⟩ := splitConeCheck_parts ε
      interval_cases j
      · exact ⟨h0, trivial⟩
      · exact ⟨h1, trivial⟩
    obtain ⟨he₀, hcomm, -⟩ := coneGenCheck_parts hcheck
    set w := (coneWords ε).getD j []
    have hpP := hR.wordElt_mem w
    have hpN1 := hC.P_le_N1X hS hpP
    have hpQ := hR.P_le_normalizer hpP
    have hpc : cOf ψ t k (wordElt p w) = 0 := cOf_eq_zero_of_commuteX hS (hS.commute_of_mem_P hpP)
    have hz : (wordElt p w * g)⁻¹ * (g * wordElt p w) ∈ A ⊔ zpowers t := by
      refine hC.mem_At_of_affX hS hinv (mul_mem hg hpN1) (mul_mem hpN1 hg) ?_ fun v => ?_
      · rw [hC.cOf_mulX hS hinv hg hpN1, hC.cOf_mulX hS hinv hpN1 hg, hpc, hc,
          lin_wordElt_eq hR, he₀, (hR.lin_eq_iff hgQ 0 0).2 (by rw [hR.ψ_zero]; group),
          add_zero, zero_add]
      · rw [hR.lin_mul hgQ hpQ, hR.lin_mul hpQ hgQ, hl, hl, lin_wordElt_eq hR,
          lin_wordElt_eq hR, mulVec_mulVec, mulVec_mulVec, tauMat_eq, hcomm]
    obtain ⟨s, hs⟩ := hC.rep_of_mem_AtX hS hinv hBA hΦ hz
    refine ⟨s, ?_⟩
    have e : g * wordElt p w = wordElt p w * g * ((wordElt p w * g)⁻¹ * (g * wordElt p w)) := by
      group
    have h1 := Coord4.rep_mul hT (hw w)
    rw [e] at h1
    have h2 := hΦ.rep_unique h1 (Coord4.rep_mul (Coord4.rep_mul (hw w) hT) hs)
    rw [h2]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    · simp only [↓reduceIte, mul_neg, mul_one]
  obtain ⟨s₁, h₁⟩ := hgen 0 (by norm_num)
  obtain ⟨s₂, h₂⟩ := hgen 1 (by norm_num)
  exact no_cone_lift ε T hTred s₀ s₁ s₂ h2 h₁ h₂

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
