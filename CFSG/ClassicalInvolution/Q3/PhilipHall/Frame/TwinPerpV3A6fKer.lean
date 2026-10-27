module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fL2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fOdd
public import CFSG.ClassicalInvolution.Q3.E29Ker.Main
public import CFSG.ClassicalInvolution.Q3.TL3T12_6Dual

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Abstract

open CFSG.ClassicalInvolution.Q3.E29Ker CFSG.ClassicalInvolution.Q3.E29Data in
theorem e29_ker_eq_bot {X : Type} [Group X] [Finite X]
    (φ : X →* AE.AEQ 8) (hφ : φ.range = AE.e29Sub) (hker : φ.ker ≤ Subgroup.center X)
    (Q : Set (Subgroup X)) (hgen : pSpan Q = ⊤)
    (hconj : ∀ L ∈ Q, ∀ x : X, conjSub x L ∈ Q) (hord : ∀ L ∈ Q, Nat.card L = 8)
    (hlab : ∀ L ∈ Q, ∃ α ∈ AE.e29Sets, ∃ (h : α.card = 4) (b : Bool),
      L.map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ AE.e29Sets, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Q,
      L.map φ = AE.memBar α h b)
    (hinj : ∀ L ∈ Q, ∀ L' ∈ Q, L.map φ = L'.map φ → L = L')
    (E : Subgroup X) (hE : ∀ L ∈ Q, ∀ u : X, IsUniqueInvolution L u → u ∈ E)
    (hEZ : ∀ c ∈ E, c ∈ Subgroup.center X → c = 1) : φ.ker = ⊥ := by
  have H : E29Ker.Hyp φ Q := ⟨hφ, hconj, hord, hlab, hsurj, hinj⟩
  obtain ⟨F⟩ := Lab.exists_lab H
  have hz1 : IsUniqueInvolution F.K1 F.z1 := F.isUniqueInvolution_K1 H
  have hnker : ∀ p ∈ e29Partners, F.np p ∈ φ.ker := fun p hp => F.np_mem_ker H hp
  have hnc : ∀ p ∈ e29Partners, F.np p ∈ Subgroup.center X := fun p hp => hker (hnker p hp)
  have hnE : ∀ p ∈ e29Partners, F.np p = 1 := by
    intro p hp
    have h1 : F.z1 ∈ E := hE _ F.mem_Q _ hz1
    have h2 : F.zj p ∈ E := hE _ (F.L_mem_Q H p) _ (F.isUniqueInvolution_L H p)
    exact hEZ _ (E.mul_mem (E.inv_mem h1) h2) (hnc p hp)
  have hN0 : F.N0 = ⊥ := by
    refine eq_bot_iff.mpr ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨p, hp, rfl⟩
    rw [hnE p hp]
    exact Subgroup.one_mem _
  have hN0ker : F.N0 ≤ φ.ker := by
    rw [hN0]
    exact bot_le
  have hbound : Nat.card X ≤ 86016 * Nat.card F.N0 :=
    card_le_of_enum F.gen (F.closure_gen_eq_top H hgen) (hN0ker.trans hker) (F.eval_rels H)
      (fun p hp => F.partner_mem_N0 hnc hp) (U := F.K1) (by rw [F.gen_zero]; exact F.a_mem)
      (by rw [F.gen_one]; exact F.b_mem) (by rw [hord F.K1 F.mem_Q])
  have hrange : 86016 ≤ Nat.card φ.range := by
    rw [hφ]
    exact le_card_e29Sub
  rw [ker_eq_of_le φ hrange hN0ker hbound, hN0]

end Abstract

section Datum

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}
  (Z : LCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h)

include Z in
theorem inv_mem_e3_of_mem_KL {J : Subgroup Y}
    (hJ : J ∈ ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K) {u : Y}
    (hu : IsUniqueInvolution J u) : u ∈ e3 t y h := by
  obtain ⟨g, hg, hgJ⟩ := hJ
  have h1 : IsUniqueInvolution (conjSub g K) (g * t * g⁻¹) := Z.C.H.ex.1.datum.hz.conj g
  rw [hgJ] at h1
  rw [hu.eq h1]
  exact (Subgroup.mem_normalizer_iff.mp (L_le_normalizer Z hg) t).mp (t_mem_e3 t y h)

include Z in
theorem e3_inf_center {c : Y} (hc : c ∈ e3 t y h)
    (hcc : ∀ g ∈ ae6L Ω[R] t (tauE t y) (xE t y h), g * c * g⁻¹ = c) : c = 1 := by
  obtain ⟨htt, hττ, hxx, htτ, htx, hτx, ht1, hτ1, hx1, hτt, hxt, hxτ, hxtτ⟩ := E3_facts Z
  by_contra hc1
  obtain ⟨ℓ, hℓ, hℓc⟩ := exists_conj_t_of_mem_E3 Z hc hc1
  have h1 : ℓ * t * ℓ⁻¹ = ℓ * c * ℓ⁻¹ := hℓc.trans (hcc ℓ hℓ).symm
  have htc : t = c := mul_left_cancel (mul_right_cancel h1)
  obtain ⟨ℓ', hℓ', hℓ't⟩ := exists_conj_t_of_mem_E3 Z (tau_mem_e3 t y h) hτ1
  have h2 := hcc ℓ' hℓ'
  rw [← htc] at h2
  exact hτt (hℓ't.symm.trans h2)

include Z in
theorem odd_pSpan_KL :
    classicalInvolutionOddCore ↥(pSpan (ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K)) = ⊥ := by
  have hOdd0 := oddCoreOf_L_eq_bot Z
  have h1 : classicalInvolutionOddCore ↥(ae6L Ω[R] t (tauE t y) (xE t y h)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (ae6L Ω[R] t (tauE t y) (xE t y h)).subtype_injective).mp
      hOdd0
  rw [pSpan_KL Z]
  exact h1

include Z in
theorem ker_eq_bot_e29
    (I : AEIdentOn (ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K) 8 AE.e29Sets AE.e29Sub) :
    I.φ.ker = ⊥ := by
  revert I
  have hΩ := A6d.hypOf Z.C.H
  have h2 := A6d.h2Of Z.C.H
  have h8 := A6d.h8Of Z.C.H
  have hd := Z.C.H.ex.1.datum
  set L := ae6L Ω[R] t (tauE t y) (xE t y h) with hLdef
  set P := ae6ConjIn L K with hPdef
  intro I
  have hspan : pSpan P = L := pSpan_KL Z
  have hPΩ : P ⊆ Ω[R] := A6d.ae6ConjIn_subset hΩ.conjInvariant hd.mem
  have hinv : ∀ L' ∈ P, ∀ x ∈ pSpan P, conjSub x L' ∈ P := fun L' hL' x hx =>
    A6d.conjSub_mem_of_mem_ae6ConjIn (by rw [hspan] at hx; exact hx) hL'
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker (odd_pSpan_KL Z)
  have hLX : ∀ L' ∈ P, L' ≤ pSpan P := fun L' hL' => le_pSpan hL'
  have hinj : ∀ L₁ ∈ P, ∀ L₂ ∈ P,
      (L₁.subgroupOf (pSpan P)).map I.φ = (L₂.subgroupOf (pSpan P)).map I.φ → L₁ = L₂ := by
    intro L₁ h₁ L₂ h₂ he
    obtain ⟨α, -, hα4, b, hlab⟩ := I.label L₁ h₁
    exact TL4.eq_of_map_le_memBar hΩ h2 (by norm_num) I.φ hk (hPΩ h₁) (hPΩ h₂) (hLX _ h₁)
      (hLX _ h₂) hlab he.le
  refine e29_ker_eq_bot (X := ↥(pSpan P)) I.φ I.range_eq I.ker_le (restrictFamily P (pSpan P))
    (pSpan_restrictFamily_eq_top P) ?_ ?_ ?_ ?_ ?_ ((e3 t y h).subgroupOf (pSpan P)) ?_ ?_
  · rintro _ ⟨L₁, hL₁, hLX', rfl⟩ x
    refine ⟨conjSub (x : Y) L₁, hinv L₁ hL₁ x x.2, hLX _ (hinv L₁ hL₁ x x.2), ?_⟩
    rw [conjSub_subgroupOf]
  · rintro _ ⟨L₁, hL₁, hLX', rfl⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX').toEquiv]
    exact h8 L₁ (hPΩ hL₁)
  · rintro _ ⟨L₁, hL₁, hLX', rfl⟩
    obtain ⟨α, hα, hα4, b, hlab⟩ := I.label L₁ hL₁
    exact ⟨α, hα, hα4, b, hlab⟩
  · intro α hα h4 b
    obtain ⟨L₁, hL₁, hlab⟩ := I.label_surj α hα h4 b
    exact ⟨L₁.subgroupOf (pSpan P), ⟨L₁, hL₁, hLX L₁ hL₁, rfl⟩, hlab⟩
  · rintro _ ⟨L₁, hL₁, hLX', rfl⟩ _ ⟨L₂, hL₂, hLX'', rfl⟩ he
    rw [hinj L₁ hL₁ L₂ hL₂ he]
  · rintro _ ⟨L₁, hL₁, hLX', rfl⟩ u hu
    exact Subgroup.mem_subgroupOf.mpr
      (inv_mem_e3_of_mem_KL Z hL₁ (isUniqueInvolution_of_subgroupOf hu hLX'))
  · intro c hcE hcZ
    have hcE' : (c : Y) ∈ e3 t y h := Subgroup.mem_subgroupOf.mp hcE
    refine Subtype.ext (e3_inf_center Z hcE' fun g hg => ?_)
    have e := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨g, by rw [hspan]; exact hg⟩)
    have e' : g * (c : Y) = (c : Y) * g := e
    rw [e', mul_inv_cancel_right]

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
