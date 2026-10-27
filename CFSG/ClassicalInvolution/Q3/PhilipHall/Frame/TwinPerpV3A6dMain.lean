module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

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
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

@[expose] def V3AE6IOrb (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      ∀ m ∈ MGrp Ω[R] W, ∃ x, (x = 1 ∨ x = t ∨ x = a₁ * a₂ * a₃ * a₄ ∨ x = a₁ * a₂ * a₃ * a₄ * t) ∧
        m * (a₁ * a₂) * m⁻¹ = a₁ * a₂ * x

theorem v3AE6I_of {n : ℕ} (hP : TL4.TightBelowRPlus 3 n)
    (hD : V3AE6D n) (hDN : V3AE6DNorm n) (hOrb : V3AE6IOrb n) : V3AE6I n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  have hStd := H.ex.1
  have hd := hStd.datum
  obtain ⟨hE, hEu, hEt, hEτ, -⟩ := hD Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨hDsq, hYuN⟩ := hDN Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  have horb := hOrb Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  have hGen := rLayer_le_pSpan H
  have hOdd0 := oddCoreOf_ae6I_eq_bot H hDsq hYuN hEu hEt fun c _ hcP =>
    conjSub_ae6I_of_orbit H horb fr hcP
  set Ω : Set (Subgroup Y) := Ω[R] with hΩdef
  set I : Subgroup Y := ae6I Ω W (u₁ * u₂) with hIdef
  set D : Subgroup Y := ae6D Ω W (u₁ * u₂) with hDdef
  set P : Set (Subgroup Y) := ae6ConjIn I K with hPdef
  have hIN : I ≤ Subgroup.normalizer (D : Set Y) := ae6I_le_normalizer_ae6D Ω W (u₁ * u₂) hYuN
  have hD2 : IsPGroup 2 ↥D := isPGroup_two_of_sq_eq_one hDsq
  have htD : t ∈ D := ae6E_le_ae6D Ω W (u₁ * u₂) hEt
  have hDI : ∀ x ∈ I, ∀ d ∈ D, x * d * x⁻¹ ∈ D := fun x hx d hd' =>
    (Subgroup.mem_normalizer_iff.mp (hIN hx) d).mp hd'
  have hItop : I < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hn : D.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hIN))
    haveI := hStd.perp.core.simple
    have hbot := eq_bot_of_normal_isPGroup hStd.perp.core.nonab hn hD2
    exact hd.hz.ne_one (by simpa [hbot] using htD)
  refine ⟨hItop, ?_⟩
  have hKI : K ≤ I := (K_le_M H).trans (M_le_ae6I Ω W (u₁ * u₂))
  have hspan : pSpan P = I :=
    le_antisymm (pSpan_ae6ConjIn_le hKI) (sup_le (M_le_pSpan H) hGen)
  have hodd : classicalInvolutionOddCore ↥(pSpan P) = ⊥ := by
    have h1 : classicalInvolutionOddCore ↥I = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ I.subtype_injective).mp hOdd0
    rw [hspan]
    exact h1
  have hΩ := hypOf H
  have h2 := h2Of H
  have h8 := h8Of H
  have hA := aEmptyOf H
  have hPΩ : P ⊆ Ω := ae6ConjIn_subset hΩ.conjInvariant hd.mem
  have hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P := fun L hL x hx =>
    conjSub_mem_of_mem_ae6ConjIn (by rw [← hspan]; exact hx) hL
  have htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L' := by
    intro L hL L' hL'
    obtain ⟨x, hx, h⟩ := exists_conj_of_mem_ae6ConjIn hL hL'
    exact ⟨x, by rw [hspan]; exact hx, h⟩
  have hDinv : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → u ∈ D := by
    rintro L ⟨g, hg, rfl⟩ u hu
    rw [hu.eq (hd.hz.conj g)]
    exact hDI g hg t htD
  have he2 : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∃ Q : Subgroup Y, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q := by
    intro L hL u hu
    refine ⟨D ⊓ pSpan P, inf_le_right, ?_, hD2.to_le inf_le_left, hDinv L hL u hu, le_pSpan hL hu.mem⟩
    intro x hx q hq
    exact ⟨hDI x (by rw [← hspan]; exact hx) q hq.1,
      (pSpan P).mul_mem ((pSpan P).mul_mem hx hq.2) ((pSpan P).inv_mem hx)⟩
  have hmemP : ∀ {J : Subgroup Y}, J ∈ DSet Ω W → J ∈ P := by
    intro J hJ
    obtain ⟨m, hm, rfl⟩ := exists_M_conj_of_mem_D H hJ
    exact conjSub_mem_ae6ConjIn (M_le_ae6I Ω W (u₁ * u₂) hm)
  have hK₃P : K₃ ∈ P := hmemP H.hK₃
  have hthin : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∀ Q : Subgroup Y, Q ≤ pSpan P →
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q →
        x = 1 ∨ x = u := by
    intro L hL u hu Q hQle hQn hQ2 x hxL hxQ
    by_contra hcon'
    have hcon := not_or.mp hcon'
    have hxx : x * x ≠ 1 := fun h => (hu.unique x hxL h).elim hcon.1 hcon.2
    obtain ⟨g, hg, hgL⟩ := htrans L hL K₃ hK₃P
    have hx' : g * x * g⁻¹ ∈ K₃ := hgL ▸ conj_mem_conjSub hxL
    have hxQ' : g * x * g⁻¹ ∈ Q := hQn g hg x hxQ
    have hYuP : rLayer Ω (u₁ * u₂) ≤ pSpan P := hGen
    have hNn : ∀ y ∈ rLayer Ω (u₁ * u₂), ∀ h ∈ Q ⊓ rLayer Ω (u₁ * u₂),
        y * h * y⁻¹ ∈ Q ⊓ rLayer Ω (u₁ * u₂) := fun y hy h hh =>
      ⟨hQn y (hYuP hy) h hh.1,
        (rLayer Ω (u₁ * u₂)).mul_mem ((rLayer Ω (u₁ * u₂)).mul_mem hy hh.2)
          ((rLayer Ω (u₁ * u₂)).inv_mem hy)⟩
    have hNnorm : ((Q ⊓ rLayer Ω (u₁ * u₂)).subgroupOf (rLayer Ω (u₁ * u₂))).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun y hy => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hNn y hy h hh, fun hh => ?_⟩
      have := hNn y⁻¹ ((rLayer Ω (u₁ * u₂)).inv_mem hy) _ hh
      simpa [mul_assoc] using this
    have hle : Q ⊓ rLayer Ω (u₁ * u₂) ≤ ae6E Ω (u₁ * u₂) :=
      CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ inf_le_right
        hNnorm (hQ2.to_le inf_le_left)
    have hxE : g * x * g⁻¹ ∈ ae6E Ω (u₁ * u₂) := hle ⟨hxQ', K₃_le_rLayer H hx'⟩
    have hsq := hE.2 _ hxE
    apply hxx
    have e : x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
    rw [e, hsq]
    group
  have hlt : Nat.card ↥(pSpan P) < n := by
    rw [hspan, ← hStd.perp.core.card]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq =>
      (ne_of_lt hItop) ((Subgroup.card_eq_iff_eq_top _).mp heq)
  have hDabs : ThmDAbsAt 3 ↥(pSpan P) := hP.thmD.d2 _ hlt
  have hfive : ∃ y : ↥(pSpan P), orderOf y = 5 := by
    obtain ⟨y, hy, hord⟩ := exists_order_five H
    refine ⟨⟨y, by rw [hspan]; exact rLayer_le_ae6I Ω W (u₁ * u₂) hy⟩, ?_⟩
    rw [← hord]
    exact Subgroup.orderOf_mk _ _
  obtain ⟨I₀⟩ := aeIdent8_of_thmD hΩ h2 h8 hA hPΩ htrans hinv hodd he2 hDabs (fourTwins_of H) hthin
    hfive noOrderFive_e64Sub noOrderFive_e29Sub
  have hk : IsPGroup 2 I₀.φ.ker := I₀.isPGroup_ker hodd
  obtain ⟨hH, hker⟩ := ker_eq_bot_of_twins hΩ h2 h8 hPΩ hinv htrans I₀ hk (fourTwins_of H)
  refine ⟨I₀, hspan, hker, ?_⟩
  have hDle : D ≤ I := ae6D_le_ae6I Ω W (u₁ * u₂)
  refine le_antisymm ?_ ?_
  · have := pCoreOf_le_of_involutions I₀ hH hDinv
    rwa [hspan] at this
  · exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 D I hDle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hDle).mpr hIN) hD2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
